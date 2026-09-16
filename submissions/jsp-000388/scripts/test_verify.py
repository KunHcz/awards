"""Regression tests for the audit and independent finite arithmetic cross-checks."""
import json
from fractions import Fraction
from pathlib import Path
import unittest
from verify import audit, guard


class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(audit("'x' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['x'])['x'],
                         ['propext', 'Classical.choice', 'Quot.sound'])

    def test_axiom_free(self):
        self.assertEqual(audit("'x' does not depend on any axioms", ['x']), {'x': []})

    def test_missing_audit(self):
        with self.assertRaises(ValueError):
            audit("'other' does not depend on any axioms", ['x'])

    def test_duplicate_audit(self):
        with self.assertRaises(ValueError):
            audit("'x' does not depend on any axioms\n" * 2, ['x'])

    def test_unapproved_axioms(self):
        for name in ['sorryAx', 'forged', 'Lean.ofReduceBool']:
            with self.subTest(axiom=name), self.assertRaises(ValueError):
                audit("'x' depends on axioms: [" + name + "]", ['x'])

    def test_source_guard(self):
        source = 'import Mathlib.Tactic\ntheorem foo : True := by trivial\n#print axioms foo\n'
        guard(source, ['Mathlib.Tactic'], ['foo'])
        for word in ['sorry', 'admit', 'native_decide', 'unsafe', 'skipKernelTC', 'ofReduceBool']:
            with self.subTest(word=word), self.assertRaises(ValueError):
                guard(source + word, ['Mathlib.Tactic'], ['foo'])

    def test_reject_unexpected_inventory(self):
        source = 'import Mathlib.Tactic\ntheorem foo : True := by trivial\n#print axioms foo\n'
        with self.assertRaises(ValueError):
            guard(source, ['Other'], ['foo'])
        with self.assertRaises(ValueError):
            guard(source, ['Mathlib.Tactic'], ['bar'])

    def test_actual_package_inventory(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / 'verification-config.json').read_text())
        guard((root / (cfg['module'] + '.lean')).read_text(), cfg['imports'], cfg['theorems'])


class ArithmeticCrossChecks(unittest.TestCase):
    def test_signed_quadratic_identities_and_bounds(self):
        for a in [-3, -2, -1, 1, 2, 3]:
            for b in range(-4, 5):
                for c in range(-2, 3):
                    f = lambda x: a * x * x + b * x + c
                    for k in range(-5, 6):
                        if b:
                            self.assertEqual(f(k) - f(-k), 2 * b * k)
                        else:
                            self.assertEqual(f(k + 1) - f(k - 1), 4 * a * k)
                        if a > 0:
                            self.assertGreaterEqual(f(k), c - b * b)
                        else:
                            self.assertLessEqual(f(k), c + b * b)


if __name__ == '__main__':
    unittest.main()
