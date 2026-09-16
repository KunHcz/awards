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

def by_divisors(t,n):
    # Enumerate actual divisors, not the bounded finite predicate used in Lean.
    ds = [d for d in range(1,n+1) if n % d == 0]
    sums = {0}
    for d in ds:
        sums |= {x+d for x in tuple(sums) if x+d <= t}
    return t in sums

def by_bounded_subsets(t,n):
    values = [a for a in range(1,t+1) if n % a == 0]
    return any(sum(s) == t for size in range(len(values)+1) for s in combinations(values,size))

class DensityChecks(unittest.TestCase):
    def test_literal_and_finite_definitions_agree(self):
        for t,n in product(range(9),range(1,161)):
            self.assertEqual(by_divisors(t,n), by_bounded_subsets(t,n), (t,n))

    def test_exact_small_densities(self):
        expected = [Fraction(1),Fraction(1),Fraction(1,2),Fraction(2,3),Fraction(1,2),Fraction(7,15),Fraction(7,15)]
        for t,d in enumerate(expected):
            L=factorial(t)
            C=sum(by_bounded_subsets(t,n) for n in range(1,L+1))
            self.assertEqual(Fraction(C,L),d)

    def test_periodicity_and_uniform_error(self):
        for t in range(7):
            L=factorial(t)
            p=[by_bounded_subsets(t,n) for n in range(1,3*L+8)]
            C=sum(p[:L]); count=0
            for N,val in enumerate(p,1):
                count += val
                self.assertEqual(count,(N//L)*C+sum(p[:N%L]))
                self.assertLessEqual(abs(Fraction(count)-N*Fraction(C,L)),L)
                if N+L <= len(p): self.assertEqual(val,p[N+L-1])

    def test_distinctness_matters(self):
        # Three is not a subset sum of the distinct divisors {1,5}; repeating 1 would be wrong.
        self.assertFalse(by_divisors(3,5))
        self.assertEqual(1+1+1,3)

    def test_zero_target_and_endpoint(self):
        self.assertTrue(all(by_divisors(0,n) for n in range(1,30)))
        self.assertFalse(by_divisors(2,1))
        self.assertTrue(by_divisors(2,2))

if __name__ == '__main__':
    unittest.main()
