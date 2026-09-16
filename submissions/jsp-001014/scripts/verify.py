#!/usr/bin/env python3
"""Rebuild this contribution, audit every theorem, and replay the complete environment.
The bundled checker shares Lean's kernel; this is not an independent implementation
or an official prize review. Run after `lake update` and `lake exe cache get ...`.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_SHA = '5ed2965256430c3649e86755f9576b54eca72435'
LEAN_SHA = '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAT = ('prime_with_square_obstruction', 'nextPrime_spec', 'sequence_spec',
       'sequence_strictMono', 'squarefree_shift_iff', 'prime_shift_iff',
       'simultaneous_counterexample', 'answer_prime', 'answer_squarefree')
INTEGER = ('obstruction', 'shift_ne_zero', 'shift_even', 'shift_odd', 'shift_covers',
           'next_spec', 'sequence_spec', 'sequence_strictMono', 'squarefree_shift_iff',
           'prime_shift_iff', 'simultaneous_counterexample')
MODULES = {
    'NaturalShifts': tuple('JustinSunPrize.JSP001014.' + n for n in NAT),
    'IntegerShifts': tuple('JustinSunPrize.JSP001014.IntegerShifts.' + n for n in INTEGER),
}
IMPORTS = ['Mathlib.NumberTheory.LSeries.PrimesInAP',
           'Mathlib.Data.Nat.Squarefree', 'Mathlib.Tactic']


def audit(text, names):
    result = {}
    for name in names:
        prefix = "'" + re.escape(name) + "' "
        empty = re.findall(prefix + r'does not depend on any axioms', text)
        filled = re.findall(prefix + r'depends on axioms: \[([^\]]*)\]', text)
        if len(empty) + len(filled) != 1:
            raise ValueError('Missing or repeated axiom report: ' + name)
        axioms = [] if empty else [a.strip() for a in filled[0].split(',') if a.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError('Unapproved axiom dependency: ' + name)
        result[name] = axioms
    return result


def guard(source):
    # Supplementary lexical check; the kernel replay and axiom audit are decisive.
    if re.search(r'\b(sorry|admit|native_decide|unsafe)\b|skipKernelTC|ofReduceBool', source):
        raise ValueError('Unapproved proof shortcut')
    if re.search(r'^\s*(axiom|constant)\s', source, re.M):
        raise ValueError('Custom assumption')
    if re.findall(r'^import\s+(.+)$', source, re.M) != IMPORTS:
        raise ValueError('Unexpected imports')


def execute(args, cwd=ROOT, timeout=300):
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                          timeout=timeout, check=False)


def require_ok(proc, label):
    if proc.returncode != 0:
        raise RuntimeError('%s failed (%s)\n%s\n%s' %
                           (label, proc.returncode, proc.stdout, proc.stderr))
    return proc.stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='verification-output')
    args = parser.parse_args()
    out = ROOT / args.output
    out.mkdir(parents=True, exist_ok=True)
    started = datetime.now(timezone.utc).isoformat()
    mathlib = ROOT / '.lake/packages/mathlib'
    sha = require_ok(execute(['git', 'rev-parse', 'HEAD'], mathlib), 'mathlib revision')
    if sha != MATHLIB_SHA:
        raise RuntimeError('Unexpected mathlib revision: ' + sha)
    if require_ok(execute(['git', 'status', '--porcelain', '--untracked-files=no'], mathlib),
                  'mathlib cleanliness'):
        raise RuntimeError('Modified tracked mathlib files')
    version = require_ok(execute(['lake', 'env', 'lean', '--version']), 'Lean version')
    if 'version 4.34.0,' not in version or LEAN_SHA not in version:
        raise RuntimeError('Unexpected Lean distribution: ' + version)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dep = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if dep['rev'] != MATHLIB_SHA:
        raise RuntimeError('Manifest pin mismatch')

    sources = {}
    for module in MODULES:
        path = ROOT / ('JSP1014/' + module + '.lean')
        source = path.read_text(encoding='utf-8')
        guard(source)
        sources[module] = source

    def save_log(name, proc):
        text = (proc.stdout + proc.stderr).replace(str(ROOT), '$PROJECT')
        (out / name).write_text(text, encoding='utf-8')
        return text

    # Only remove this package's generated outputs, never dependency builds.
    build = ROOT / '.lake/build'
    if build.is_symlink():
        raise RuntimeError('Refusing a symlinked build directory')
    if build.exists():
        shutil.rmtree(build)
    result = execute(['lake', '--wfail', 'build'])
    save_log('build.log', result)
    require_ok(result, 'fresh package rebuild')

    axioms = {}
    for module, names in MODULES.items():
        result = execute(['lake', 'env', 'lean', 'JSP1014/' + module + '.lean'])
        text = save_log(module + '.log', result)
        require_ok(result, module)
        if re.search(r'\b(error|warning)(?:\([^)]*\))?:', text):
            raise RuntimeError('Unexpected Lean diagnostic')
        axioms.update(audit(text, names))

    result = execute(['lake', 'env', 'leanchecker', '--verbose', '--fresh', 'JSP1014'], timeout=600)
    checker_log = save_log('kernel-replay.log', result)
    require_ok(result, 'full fresh-environment kernel replay')
    if 'JSP1014' not in checker_log:
        raise RuntimeError('Missing checker target confirmation')

    cases = {
        'false_arithmetic': ('import Mathlib.Tactic\ntheorem bad : (2 : Nat) = 3 := by decide\n', None),
        'wrong_good_shift': (sources['NaturalShifts'].replace('= {0}', '= {1}'), None),
        'positive_only_enumeration': (sources['IntegerShifts'].replace(
            'else -((k / 2 + 1 : ℕ) : ℤ)', 'else ((k / 2 + 1 : ℕ) : ℤ)'), None),
        'placeholder': ('import Mathlib.Tactic\ntheorem bad : False := by sorry\n#print axioms bad\n', 'bad'),
        'custom_axiom': ('import Mathlib.Tactic\naxiom forged : False\ntheorem bad : False := forged\n#print axioms bad\n', 'bad'),
    }
    negative_results = {}
    with tempfile.TemporaryDirectory(prefix='jsp1014-negative-') as tmp:
        for label, (content, theorem) in cases.items():
            path = Path(tmp) / (label + '.lean')
            path.write_text(content, encoding='utf-8')
            proc = execute(['lake', 'env', 'lean', str(path)])
            text = (proc.stdout + proc.stderr).replace(tmp, '$NEGATIVE_FIXTURE')
            (out / (label + '.log')).write_text(text.replace(str(ROOT), '$PROJECT'), encoding='utf-8')
            if theorem is None:
                if proc.returncode == 0 or 'error' not in text:
                    raise RuntimeError('Invalid mutation was not rejected: ' + label)
                status = 'REJECTED_BY_LEAN'
            else:
                require_ok(proc, 'negative-control compilation ' + label)
                try:
                    audit(text, (theorem,))
                except ValueError:
                    status = 'REJECTED_BY_AXIOM_AUDIT'
                else:
                    raise RuntimeError('Axiom audit accepted ' + label)
            negative_results[label] = {'exit_code': proc.returncode, 'status': status}

    files = {}
    for name in ['JSP1014.lean', 'JSP1014/NaturalShifts.lean', 'JSP1014/IntegerShifts.lean',
                 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        data = (ROOT / name).read_bytes()
        files[name] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
    report = {
        'status': 'LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED',
        'checked_at_utc': started,
        'completed_at_utc': datetime.now(timezone.utc).isoformat(),
        'problem_id': 'JSP-001014',
        'scope': 'Erdos 1209 parts i and ii; all-integer-shift extension; not Fermat-number variants',
        'lean_version': version,
        'mathlib_commit': sha,
        'rebuild': 'PASS: only project build outputs were deleted before rebuilding',
        'kernel_replay': 'PASS: all imported and local constants replayed into a fresh kernel environment',
        'independent_checker_implementation': False,
        'independent_human_review': False,
        'complete_source_rebuild_of_dependencies': False,
        'dependencies': 'Pinned upstream precompiled mathlib cache, checked by fresh kernel replay',
        'audited_theorem_count': len(axioms),
        'axioms': axioms,
        'negative_controls': negative_results,
        'files': files,
        'novel_mathematical_discovery': False,
        'formalization_priority': 'Not established; subject to public prior-art review',
        'award_eligibility': 'Undetermined; requires operator review',
    }
    (out / 'verification.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
