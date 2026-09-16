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
from fetch_upstream import fetch

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LEAN_SHA = '50aaf682e9b74ab92880292a25c68baa1cc81c87'
MATHLIB_SHA = '37df177aaa770670452312393d4e84aaad56e7b6'


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
    printed = re.findall(r'^#print axioms\s+([\w.]+)', source, re.M)
    if declared != names or printed != ['Erdos751.Main.erdos_751_strong'] + names:
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


def validate_replay(text: str) -> None:
    markers = (
        'Fresh target-closure replay: 9 targets;',
        'CONTROL: kernel accepted True from True.intro',
        'CONTROL: kernel rejected False from True.intro',
        'PASS: all nine targets and their complete transitive logical dependencies replayed from an empty environment',
    )
    if 'PANIC' in text or 'uncaught exception' in text or not all(m in text for m in markers):
        raise RuntimeError('Missing or invalid replay confirmation')
    if not re.search(r'Checked [1-9][0-9]* logical declarations in target dependency closures', text):
        raise RuntimeError('Missing nonzero replay count')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification-output')
    args = parser.parse_args()
    out = ROOT / args.output
    out.mkdir(parents=True, exist_ok=True)
    fetch()
    cfg = json.loads((ROOT / 'verification-config.json').read_text())
    module = cfg['module']
    started = datetime.now(timezone.utc).isoformat()
    version = require_ok(execute(['lake', 'env', 'lean', '--version']), 'Lean version')
    if 'version 4.23.0,' not in version or LEAN_SHA not in version:
        raise RuntimeError('Unexpected Lean version')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dependency_pins = {}
    for dep in manifest['packages']:
        if dep['type'] == 'path':
            if dep['name'] != 'erdos751' or dep['dir'] != '.upstream':
                raise RuntimeError('Unexpected local dependency')
            dependency_pins['erdos751'] = 'ae3ead960a494cf81b28541c477e50997cb03999'
            continue
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
    upstream_build = ROOT / '.upstream/.lake/build'
    if upstream_build.is_symlink():
        raise RuntimeError('Refusing a symlinked upstream build directory')
    if upstream_build.exists():
        shutil.rmtree(upstream_build)
    proc = execute(['lake', '--wfail', 'build'])
    save_log('build.log', proc)
    require_ok(proc, 'clean project rebuild')
    proc = execute(['lake', 'env', 'lean', module + '.lean'])
    text = save_log('axioms.log', proc)
    require_ok(proc, 'source proof check')
    if re.search(r'\b(error|warning)(?:\([^)]*\))?:', text):
        raise RuntimeError('Unexpected source diagnostic')
    axioms = audit(text, [cfg['namespace'] + '.' + n for n in cfg['theorems']])
    imported_audit = audit(text, ['Erdos751.Main.erdos_751_strong'])
    proc = execute(['lake', 'env', 'lean', '--run', 'scripts/Replay.lean'], timeout=600)
    text = save_log('kernel-replay.log', proc)
    require_ok(proc, 'fresh-environment kernel replay')
    validate_replay(text)

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
                 'verification-config.json', 'scripts/verify.py', 'scripts/fetch_upstream.py',
                 'scripts/Replay.lean', 'upstream-hashes.json']:
        data = (ROOT / name).read_bytes()
        files[name] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
    report = dict(status='LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED', problem_id=cfg['problem_id'],
                  scope=cfg['scope'], checked_at_utc=started,
                  completed_at_utc=datetime.now(timezone.utc).isoformat(), lean_version=version,
                  dependency_pins=dependency_pins, clean_project_rebuild=True,
                  full_fresh_kernel_replay=False, complete_target_dependency_replay=True, independent_checker_implementation=False,
                  independent_human_review=False, full_dependency_source_rebuild=False,
                  audited_theorem_count=len(axioms), axioms=axioms, imported_finite_theorem_audit=imported_audit, negative_controls=negatives,
                  files=files, novel_mathematical_discovery=False,
                  formalization_priority='NOT_ESTABLISHED', award_eligibility='UNDETERMINED')
    (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
