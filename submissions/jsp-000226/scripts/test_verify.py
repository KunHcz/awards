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
    def test_dyadic_family_exact_rationals(self):
        values = []
        for m in range(2, 13):
            n = 2 ** (m + 1) - m - 2
            terms = list(range(n + 1, n + m + 1))
            self.assertGreaterEqual(n, m)
            self.assertEqual(len(set(terms)), m)
            self.assertEqual(Fraction(n, 2 ** n), sum((Fraction(a, 2 ** a) for a in terms), Fraction()))
            values.append(n)
        self.assertEqual(values, sorted(set(values)))
        self.assertEqual(values[:4], [4, 11, 26, 57])



if __name__ == '__main__':
    unittest.main()
