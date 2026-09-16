"""Axiom-audit regression and independent finite mathematical cross-checks."""
import json
from pathlib import Path
from fractions import Fraction
from itertools import combinations, product
from math import factorial
import unittest
from verify import audit, guard

ROOT = Path(__file__).resolve().parents[1]

class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(len(audit("'T' depends on axioms: [propext, Classical.choice, Quot.sound]", ['T'])['T']), 3)

    def test_axiom_free(self):
        self.assertEqual(audit("'T' does not depend on any axioms", ['T']), {'T': []})

    def test_missing_report(self):
        with self.assertRaises(ValueError):
            audit('', ['T'])

    def test_duplicate_report(self):
        with self.assertRaises(ValueError):
            audit("'T' does not depend on any axioms\n" * 2, ['T'])

    def test_unapproved_assumption(self):
        for name in ['sorryAx', 'forged', 'Lean.ofReduceBool']:
            with self.subTest(name=name), self.assertRaises(ValueError):
                audit("'T' depends on axioms: [" + name + "]", ['T'])

    def test_inventory_and_semantic_mutations(self):
        cfg = json.loads((ROOT / 'verification-config.json').read_text())
        source = (ROOT / (cfg['module'] + '.lean')).read_text()
        guard(source, cfg['imports'], cfg['theorems'])
        for before, after in cfg['mutations'].values():
            self.assertIn(before, source)
            self.assertNotEqual(before, after)
        with self.assertRaises(ValueError):
            guard(source, cfg['imports'], cfg['theorems'][:-1])

    def test_shortcuts_rejected(self):
        for bad in ['sorry', 'admit', 'native_decide', 'unsafe', 'axiom forged : False']:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                guard(bad, [], [])

class SplittingChecks(unittest.TestCase):
    def test_overlapping_infinite_set_models(self):
        # Finite initial schedule only; the Lean theorem establishes infinitude.
        # Set i consists of all integers divisible by i+2. The sets overlap heavily.
        selected = {}; witnesses = {}; used = set()
        for i, c, r in product(range(4), range(3), range(7)):
            x = i + 2
            while x in used:
                x += i + 2
            used.add(x); selected[x] = c; witnesses[i,c,r] = x
        self.assertEqual(len(used), 4*3*7)
        for i, c in product(range(4), range(3)):
            xs = [witnesses[i,c,r] for r in range(7)]
            self.assertEqual(len(set(xs)), 7)
            self.assertTrue(all(x % (i+2) == 0 and selected[x] == c for x in xs))

    def test_finite_set_cannot_supply_fresh_points_forever(self):
        pool = {4}; used = set()
        self.assertTrue(pool-used)
        used.add(next(iter(pool-used)))
        self.assertFalse(pool-used)

    def test_final_quantifiers_have_no_intersection_hypotheses(self):
        source = (ROOT / 'JSP489.lean').read_text()
        signature = source.split('theorem infinitely_many_each_color')[1].split(':= by')[0]
        self.assertIn('A : ℕ → Set α', signature)
        self.assertIn('(A i).Infinite', signature)
        self.assertNotIn('Countable', signature)
        self.assertNotIn('Disjoint', signature)
        self.assertNotIn('Fintype', signature)

if __name__ == '__main__':
    unittest.main()
