#!/usr/bin/env python3
"""Rebuild, audit and replay this pinned Lean proof. This is local checking, not prize review."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_SHA = '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'
MATHLIB_SHA = '5ed2965256430c3649e86755f9576b54eca72435'


def audit(text: str, names: list[str]) -> dict[str, list[str]]:
    result = {}
    for name in names:
        prefix = "'" + re.escape(name) + "' "
        empty = re.findall(prefix + r'does not depend on any axioms', text)
        filled = re.findall(prefix + r'depends on axioms: \[([^\]]*)\]', text)
        if len(empty) + len(filled) != 1:
            raise ValueError('Missing or duplicate axiom audit: ' + name)
        axioms = [] if empty else [a.strip() for a in filled[0].split(',') if a.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError('Unapproved axiom dependency: ' + name)
        result[name] = axioms
    return result


def guard(source: str, imports: list[str], names: list[str]) -> None:
    if re.search(r'\b(sorry|admit|native_decide|unsafe)\b|skipKernelTC|ofReduceBool', source):
        raise ValueError('Unapproved proof shortcut')
    if re.search(r'^\s*(axiom|constant)\s', source, re.M):
        raise ValueError('Custom assumption')
    if re.findall(r'^import\s+(.+)$', source, re.M) != imports:
        raise ValueError('Unexpected imports')
    declared = re.findall(r'^theorem\s+(\w+)', source, re.M)
    printed = re.findall(r'^#print axioms\s+(\w+)', source, re.M)
    if declared != names or printed != names:
        raise ValueError('Theorem inventory does not match the complete audit list')


def execute(args: list[str], cwd: Path = ROOT, timeout: int = 300) -> subprocess.CompletedProcess:
    with subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True) as proc:
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
            raise RuntimeError('Verification timed out: ' + args[0])
        return subprocess.CompletedProcess(args, proc.returncode, stdout, stderr)


def require_ok(proc: subprocess.CompletedProcess, label: str) -> str:
    if proc.returncode:
        raise RuntimeError(f'{label} failed ({proc.returncode})\n{proc.stdout}\n{proc.stderr}')
    return proc.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification-output')
    args = parser.parse_args()
    out = ROOT / args.output
    out.mkdir(parents=True, exist_ok=True)
    cfg = json.loads((ROOT / 'verification-config.json').read_text())
    module = cfg['module']
    started = datetime.now(timezone.utc).isoformat()
    version = require_ok(execute(['lake', 'env', 'lean', '--version']), 'Lean version')
    if 'version 4.34.0,' not in version or LEAN_SHA not in version:
        raise RuntimeError('Unexpected Lean version')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dependency_pins = {}
    for dep in manifest['packages']:
        path = ROOT / '.lake/packages' / dep['name']
        sha = require_ok(execute(['git', 'rev-parse', 'HEAD'], path), 'dependency revision')
        if sha != dep['rev']:
            raise RuntimeError('Dependency pin mismatch: ' + dep['name'])
        if require_ok(execute(['git', 'status', '--porcelain', '--untracked-files=no'], path),
                      'dependency cleanliness'):
            raise RuntimeError('Modified dependency: ' + dep['name'])
        dependency_pins[dep['name']] = sha
    if dependency_pins.get('mathlib') != MATHLIB_SHA:
        raise RuntimeError('Unexpected mathlib revision')
    source = (ROOT / (module + '.lean')).read_text()
    guard(source, cfg['imports'], cfg['theorems'])

    def save_log(name: str, proc: subprocess.CompletedProcess, temporary: str = '') -> str:
        text = (proc.stdout + proc.stderr).replace(str(ROOT), '$PROJECT')
        if temporary:
            text = text.replace(temporary, '$NEGATIVE_FIXTURE')
        (out / name).write_text(text)
        return text

    build = ROOT / '.lake/build'
    if build.is_symlink():
        raise RuntimeError('Refusing a symlinked project build directory')
    if build.exists():
        shutil.rmtree(build)
    proc = execute(['lake', '--wfail', 'build'])
    save_log('build.log', proc)
    require_ok(proc, 'clean project rebuild')
    proc = execute(['lake', 'env', 'lean', module + '.lean'])
    text = save_log('axioms.log', proc)
    require_ok(proc, 'source proof check')
    if re.search(r'\b(error|warning)(?:\([^)]*\))?:', text):
        raise RuntimeError('Unexpected source diagnostic')
    axioms = audit(text, [cfg['namespace'] + '.' + n for n in cfg['theorems']])
    proc = execute(['lake', 'env', 'leanchecker', '--verbose', '--fresh', module], timeout=600)
    text = save_log('kernel-replay.log', proc)
    require_ok(proc, 'fresh-environment kernel replay')
    if 'replaying ' + module + ' with --fresh' not in text:
        raise RuntimeError('Missing replay confirmation')

    cases = {
        'false_arithmetic': ('import Mathlib.Tactic\ntheorem bad : (2 : Nat) = 3 := by decide\n', None),
        'placeholder': ('import Mathlib.Tactic\ntheorem bad : False := by sorry\n#print axioms bad\n', 'bad'),
        'custom_axiom': ('import Mathlib.Tactic\naxiom forged : False\ntheorem bad : False := forged\n#print axioms bad\n', 'bad'),
    }
    for label, mutation in cfg['mutations'].items():
        before, after = mutation
        if before not in source:
            raise RuntimeError('Stale negative-control mutation: ' + label)
        cases[label] = (source.replace(before, after), None)
    negatives = {}
    with tempfile.TemporaryDirectory(prefix=module.lower() + '-negative-') as tmp:
        for label, (content, name) in cases.items():
            path = Path(tmp) / (label + '.lean')
            path.write_text(content)
            proc = execute(['lake', 'env', 'lean', str(path)])
            text = save_log(label + '.log', proc, tmp)
            if name is None:
                if proc.returncode == 0 or 'error' not in text:
                    raise RuntimeError('Invalid mutation not rejected: ' + label)
                status = 'REJECTED_BY_LEAN'
            else:
                require_ok(proc, 'negative-control compilation')
                try:
                    audit(text, [name])
                except ValueError:
                    status = 'REJECTED_BY_AXIOM_AUDIT'
                else:
                    raise RuntimeError('Unsound assumption was not detected')
            negatives[label] = {'exit_code': proc.returncode, 'status': status}

    files = {}
    for name in [module + '.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                 'verification-config.json', 'scripts/verify.py']:
        data = (ROOT / name).read_bytes()
        files[name] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
    report = dict(status='LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED', problem_id=cfg['problem_id'],
                  scope=cfg['scope'], checked_at_utc=started,
                  completed_at_utc=datetime.now(timezone.utc).isoformat(), lean_version=version,
                  dependency_pins=dependency_pins, clean_project_rebuild=True,
                  full_fresh_kernel_replay=True, independent_checker_implementation=False,
                  independent_human_review=False, full_dependency_source_rebuild=False,
                  audited_theorem_count=len(axioms), axioms=axioms, negative_controls=negatives,
                  files=files, novel_mathematical_discovery='NOT_ESTABLISHED',
                  mathematical_contribution='Minimal block crossings give unconditional coefficient 1 with a logarithmic error and a sharper exact inverse-factorial parameter bound. This strengthens the pinned Pratt Proposition 7.1 comparison and the earlier half-root submission. Worldwide priority, attainability and optimality are not established.',
                  formalization_priority='NOT_ESTABLISHED', award_eligibility='UNDETERMINED')
    (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
