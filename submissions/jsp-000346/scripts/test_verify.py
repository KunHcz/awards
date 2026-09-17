"""Proof-audit regression tests and independent, bounded integer cross-checks.

The finite computations are diagnostics, not substitutes for the universal Lean proof.
"""
from functools import lru_cache
from math import factorial, isqrt
from pathlib import Path
import json
import random
import unittest

from verify import audit, guard

ROOT = Path(__file__).resolve().parents[1]


def triples(n: int) -> list[tuple[int, int, int]]:
    r = isqrt(n)
    return [(2*k, 2*k+1, 2*k*(2*k+1))
            for k in range(isqrt(r)//2+1, (r-1)//2+1)]


def bound(n: int) -> int:
    r = isqrt(n)
    return max(0, max(0, r-1)//2-isqrt(r)//2)


def local_obstructions(n: int) -> list[tuple[int, int, int]]:
    return [(a, a+1, a*(a+1)) for a in range(2, isqrt(n)+1) if a*(a+1) <= n]


def avoids_adjacent_product(b: set[int]) -> bool:
    return all(not (a+1 in b and a*(a+1) in b) for a in b if a >= 2)


def minimum_local_omissions(n: int) -> int:
    """Exact minimum hitting-set size, enumerating only relevant obstruction edges."""
    edges = local_obstructions(n)
    coverage: dict[int, int] = {}
    for i, edge in enumerate(edges):
        for v in edge:
            coverage[v] = coverage.get(v, 0) | (1 << i)

    @lru_cache(None)
    def solve(mask: int) -> int:
        if not mask:
            return 0
        i = (mask & -mask).bit_length()-1
        return min(1 + solve(mask & ~coverage[v]) for v in edges[i])

    return solve((1 << len(edges))-1)


def distinct_blocks(values: list[int]) -> bool:
    seen: set[int] = set()
    for i in range(len(values)):
        p = 1
        for v in values[i:]:
            p *= v
            if p in seen:
                return False
            seen.add(p)
    return True


class AuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(audit("'x' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ['x']),
                         {'x': ['propext', 'Classical.choice', 'Quot.sound']})
        self.assertEqual(audit("'x' does not depend on any axioms", ['x']), {'x': []})

    def test_missing_duplicate_and_extra_assumptions(self):
        for text in ['', "'x' does not depend on any axioms\n" * 2,
                     "'x' depends on axioms: [sorryAx]", "'x' depends on axioms: [forged]",
                     "'x' depends on axioms: [Lean.ofReduceBool]"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                audit(text, ['x'])

    def test_source_shortcuts(self):
        s = 'import Mathlib.Tactic\ntheorem foo : True := by trivial\n#print axioms foo\n'
        guard(s, ['Mathlib.Tactic'], ['foo'])
        for token in ['sorry', 'admit', 'native_decide', 'unsafe', 'skipKernelTC', 'ofReduceBool',
                      '\naxiom forged : False']:
            with self.subTest(token=token), self.assertRaises(ValueError):
                guard(s+token, ['Mathlib.Tactic'], ['foo'])

    def test_actual_inventory_and_mutations(self):
        cfg = json.loads((ROOT/'verification-config.json').read_text())
        source = (ROOT/'JSP346.lean').read_text()
        guard(source, cfg['imports'], cfg['theorems'])
        self.assertEqual(len(cfg['theorems']), 54)
        for before, after in cfg['mutations'].values():
            self.assertEqual(source.count(before), 1)
            self.assertNotEqual(before, after)

    def test_literal_scope(self):
        s = (ROOT/'JSP346.lean').read_text()
        self.assertIn('∏ i ∈ Finset.Icc p.1 p.2, d i', s)
        self.assertIn('(Finset.Icc 1 N).filter (fun n => n ∉ B)', s)
        self.assertNotIn('HasDensity', s)
        final = s.split('theorem product_distinct_half_root', 1)[1].split('#print', 1)[0]
        self.assertIn('∀ᶠ N : ℕ in atTop', final)
        self.assertIn('(hprod : DistinctBlockProducts d)', final)
        self.assertIn('((1 : ℝ)/2 - ε)', final)
        stronger = s.split('theorem product_distinct_full_root_eventually', 1)[1].split('#print', 1)[0]
        self.assertIn('(hprod : DistinctBlockProducts d)', stronger)
        self.assertIn('(1-ε) * Real.sqrt', stronger)
        self.assertNotIn('AvoidsAdjacentProduct', stronger)


class IntegerCrossChecks(unittest.TestCase):
    def test_all_selected_triples_and_small_cutoffs(self):
        for n in list(range(4097)) + [10**6, 10**8]:
            r = isqrt(n)
            ts = triples(n)
            self.assertEqual(len(ts), bound(n))
            used: set[int] = set()
            for a, b, c in ts:
                self.assertEqual(b, a+1)
                self.assertEqual(c, a*b)
                self.assertTrue(1 <= a < b <= r < c <= n)
                self.assertFalse(used.intersection([a,b,c]))
                used.update([a,b,c])

    def test_exact_small_relaxed_minima(self):
        for n in list(range(81)) + [100, 144, 200, 256, 400]:
            e = minimum_local_omissions(n)
            self.assertGreaterEqual(e, bound(n))
            r = isqrt(n)
            self.assertLessEqual(r, 2*e+isqrt(r)+2)
        self.assertEqual(minimum_local_omissions(6), 1)
        self.assertGreater(bound(400), 0)

    def test_actual_hole_choices(self):
        rng = random.Random(346421)
        for n in [36, 100, 400, 4096]:
            for _ in range(8):
                b = set(range(1,n+1))
                for edge in local_obstructions(n):
                    if all(v in b for v in edge):
                        b.remove(rng.choice(edge))
                self.assertTrue(avoids_adjacent_product(b))
                holes = [next(v for v in edge if v not in b) for edge in triples(n)]
                self.assertEqual(len(holes), len(set(holes)))
                self.assertGreaterEqual(n-len(b), len(holes))

    def test_cutoff_is_needed(self):
        # Without the lower cutoff, a large product can equal another pair endpoint.
        self.assertFalse(set((2,3,6)).isdisjoint((6,7,42)))

    def test_coefficient_one_is_not_a_local_consequence(self):
        n = 400
        r = isqrt(n)
        b = {a for a in range(1,r+1) if a % 2 == 1} | set(range(r+2,n+1))
        self.assertTrue(avoids_adjacent_product(b))
        e = n-len(b)
        self.assertGreater(r, e+isqrt(r)+2)
        self.assertLessEqual(r, 2*e+isqrt(r)+2)

    def test_local_condition_is_weaker_than_full_blocks(self):
        b = {2,4,8}
        self.assertTrue(avoids_adjacent_product(b))
        self.assertFalse(distinct_blocks(sorted(b)))
        self.assertTrue(distinct_blocks([2,3,5,7,11,13,17,19,23,29]))
        self.assertTrue(distinct_blocks([2**(2**i) for i in range(8)]))
        self.assertFalse(distinct_blocks(list(range(2,11))))

    def test_exact_displayed_example(self):
        self.assertEqual(bound(10**8), 4949)
        self.assertEqual(bound(10**12), 499499)
        self.assertEqual(bound(0), 0)
        self.assertEqual(bound(1), 0)


def retained_holes(values: list[int], n: int) -> tuple[list[int], list[int]]:
    """Finite reference of the retained-successor injection, not a proof oracle."""
    if values != sorted(set(values)):
        raise ValueError('Expected strictly increasing values')
    m = isqrt(n)
    retained = [x for x in values if x <= m]
    last = retained[-1] if retained else None
    domain = [x for x in range(isqrt(m)+1, m+1) if x != last]
    index = {x: i for i, x in enumerate(values)}
    holes = [x * values[index[x]+1] if x in index else x for x in domain]
    return domain, holes


class FullHypothesisCrossChecks(unittest.TestCase):
    def test_exhaustive_finite_prefixes(self):
        # Every possible subset is examined. Only the literal full interval property qualifies.
        for mask in range(1 << 10):
            values = [i+2 for i in range(10) if mask & (1 << i)]
            if not distinct_blocks(values):
                continue
            for n in range(12):
                domain, holes = retained_holes(values, n)
                self.assertEqual(len(set(holes)), len(domain))
                self.assertTrue(all(1 <= h <= n and h not in values for h in holes))
                omissions = n - sum(1 for x in values if 1 <= x <= n)
                self.assertLessEqual(isqrt(n), omissions+isqrt(isqrt(n))+1)

    def test_large_greedy_prefix_and_all_cutoffs(self):
        values = []
        for x in range(2, 257):
            if distinct_blocks(values+[x]):
                values.append(x)
        self.assertTrue(distinct_blocks(values))
        for n in range(1025):
            domain, holes = retained_holes(values, n)
            self.assertEqual(len(holes), len(set(holes)))
            self.assertTrue(all(1 <= h <= n and h not in values for h in holes))
            missing = n - sum(x <= n for x in values)
            self.assertGreaterEqual(missing, max(0,isqrt(n)-isqrt(isqrt(n))-1))

    def test_last_retained_exception_is_necessary(self):
        values = [2,3,5,7,11]
        self.assertTrue(distinct_blocks(values))
        domain, holes = retained_holes(values, 49)
        self.assertNotIn(7, domain)
        self.assertTrue(all(h <= 49 for h in holes))
        self.assertGreater(7*11, 49)

    def test_small_and_large_holes_need_separation(self):
        values = [2,3,5,7,11]
        # Removing the lower cutoff would charge both 2 and missing 6 to 6.
        self.assertNotIn(6, values)
        self.assertEqual(2*3, 6)
        domain, holes = retained_holes(values, 49)
        self.assertNotIn(2, domain)
        self.assertEqual(len(set(holes)), len(holes))

    def test_retained_not_ambient_successor(self):
        self.assertTrue(distinct_blocks([2,3,5,10,11]))
        # A skipped retained successor is not a consecutive block, and can be a retained value.
        self.assertEqual(2*5, 10)
        self.assertNotEqual(3+1, 5)

    def test_full_root_displayed_values(self):
        exact = lambda n: max(0,isqrt(n)-isqrt(isqrt(n))-1)
        self.assertEqual(exact(10**8), 9899)
        self.assertEqual(exact(10**12), 998999)
        for n in range(4):
            self.assertEqual(exact(n), 0)


def factorial_length(m: int) -> int:
    if m < 0:
        raise ValueError('Negative cutoff')
    length = 0
    while factorial(length+1) <= m:
        length += 1
    return length


def crossing_holes(values: list[int], n: int, length: int) -> tuple[list[int], list[int]]:
    """An independent finite implementation of minimal block crossings.

    The caller checks the full block-product hypothesis. This is a diagnostic,
    not an oracle used by any Lean proof.
    """
    if n < 0 or length < 0 or values != sorted(set(values)) or any(x < 2 for x in values):
        raise ValueError('Invalid sequence, length or cutoff')
    m = isqrt(n)
    if factorial(length+1) <= m:
        raise ValueError('Insufficient crossing-length bound')
    retained = [x for x in values if x <= m]
    tail_count = max(0, length-1)
    tail = set(retained[max(0, len(retained)-tail_count):])
    domain = [x for x in range(1, m+1) if x not in tail]
    indices = {x: i for i,x in enumerate(retained)}
    holes = []
    for x in domain:
        if x not in indices:
            holes.append(x)
            continue
        product = 1
        for y in retained[indices[x]:]:
            product *= y
            if product > m:
                holes.append(product)
                break
        else:
            raise AssertionError('A qualifying retained start did not cross the cutoff')
    return domain, holes


class BlockCrossingCrossChecks(unittest.TestCase):
    def assert_crossing(self, values, n):
        m = isqrt(n)
        length = factorial_length(m)
        domain, holes = crossing_holes(values, n, length)
        self.assertEqual(len(domain), len(set(holes)))
        self.assertTrue(all(1 <= h <= n and h not in values for h in holes))
        self.assertLessEqual(m, len(domain)+max(0,length-1))
        missing = n-sum(1 <= x <= n for x in values)
        self.assertLessEqual(m, missing+max(0,length-1))
        self.assertLessEqual(m, missing+max(0,m.bit_length()-1))

    def test_exhaustive_product_distinct_sets(self):
        for mask in range(1 << 11):
            values = [i+2 for i in range(11) if mask & (1 << i)]
            if distinct_blocks(values):
                for n in range(33):
                    self.assert_crossing(values,n)

    def test_greedy_prefix_many_cutoffs(self):
        values = []
        for x in range(2,129):
            if distinct_blocks(values+[x]):
                values.append(x)
        for n in list(range(513))+[10**4,10**6,10**8]:
            self.assert_crossing(values,n)

    def test_minimality_is_needed_for_upper_range(self):
        # At M=5 the first crossing from 2 is 2*3=6, within N=25.
        # Extending by one more factor gives 30, outside that same cutoff.
        self.assertLessEqual(2*3,25)
        self.assertGreater(2*3*5,25)

    def test_tail_exception_is_needed(self):
        values = [2,3,5,7,11,13]
        self.assertTrue(distinct_blocks(values))
        domain,holes = crossing_holes(values,121,3)
        self.assertNotIn(11,domain)
        self.assertNotIn(7,domain)
        self.assertIn(5,domain)
        self.assertGreater(11*13,121)
        self.assertTrue(all(h <= 121 for h in holes))

    def test_original_hypothesis_and_parameter_are_required(self):
        self.assertFalse(distinct_blocks([2,3,6]))
        self.assertEqual(2*3,6)
        with self.assertRaises(ValueError):
            crossing_holes([2,3,5,7],100,1)
        with self.assertRaises(ValueError):
            crossing_holes([1,2,3],25,3)

    def test_exact_bounds_and_zero_cases(self):
        def explicit(n):
            m=isqrt(n)
            return max(0,m-max(0,factorial_length(m)-1))
        self.assertEqual(explicit(10**8),9994)
        self.assertEqual(explicit(10**12),999992)
        self.assertEqual(factorial_length(10000),7)
        self.assertEqual(factorial_length(1000000),9)
        for n in range(4):
            self.assert_crossing([],n)
        self.assertEqual(explicit(0),0)
        self.assertEqual(explicit(1),1)

    def test_new_theorems_keep_literal_full_hypothesis(self):
        text=(ROOT/'JSP346.lean').read_text()
        for name in ['product_distinct_factorial_error','product_distinct_logarithmic_error']:
            theorem=text.split('theorem '+name,1)[1].split('\ntheorem ',1)[0]
            self.assertIn('(hprod : DistinctBlockProducts d)',theorem)
            self.assertNotIn('HasDensity',theorem)
        self.assertIn('Nat.sqrt N < (L+1).factorial',text)
        self.assertIn('omittedCount (Set.range d) N + (L-1)',text)


if __name__ == '__main__':
    unittest.main()
