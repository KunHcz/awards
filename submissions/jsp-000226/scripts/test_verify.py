"""Regression tests for the audit and independent finite arithmetic cross-checks."""
import json
from itertools import combinations
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
    def test_weight_boundary_and_monotonicity(self):
        self.assertEqual(Fraction(1, 2), Fraction(2, 4))
        for a in range(2, 128):
            self.assertGreater(Fraction(a, 2 ** a), Fraction(a + 1, 2 ** (a + 1)))

    def test_one_term_is_excluded(self):
        self.assertEqual(Fraction(2, 2 ** 2), Fraction(1, 2 ** 1))
        self.assertGreater(2, 2 ** (1 + 1) - 1 - 2)
        source = (Path(__file__).resolve().parents[1] / 'JSP226.lean').read_text()
        self.assertIn('theorem maximal_start (k : ℕ) (hk : 2 ≤ k)', source)

    def test_small_extrema_exact_enumeration(self):
        # A bounded independent regression test, not the universal proof.
        checked = 0
        for k in (2, 3, 4):
            maximum = 2 ** (k + 1) - k - 2
            by_value = {}
            for n in range(1, maximum + 4):
                by_value.setdefault(Fraction(n, 2 ** n), []).append(n)
            maxima = []
            for terms in combinations(range(1, maximum + k + 3), k):
                checked += 1
                value = sum((Fraction(a, 2 ** a) for a in terms), Fraction())
                for n in by_value.get(value, []):
                    self.assertLessEqual(n, maximum)
                    if n == maximum:
                        maxima.append(terms)
            self.assertEqual(maxima, [tuple(range(maximum + 1, maximum + k + 1))])
        self.assertGreater(checked, 30000)

    def test_all_mutation_targets_are_live(self):
        root = Path(__file__).resolve().parents[1]
        cfg = json.loads((root / 'verification-config.json').read_text())
        source = (root / 'JSP226.lean').read_text()
        self.assertEqual(len(cfg['theorems']), 16)
        for before, after in cfg['mutations'].values():
            self.assertIn(before, source)
            self.assertNotEqual(before, after)

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
