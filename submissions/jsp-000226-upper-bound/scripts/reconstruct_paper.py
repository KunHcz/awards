#!/usr/bin/env python3
"""Reconstruct the longer counterexample from the blocks in TUZ Corollary 3.6.
This secondary witness is credited to the paper's existing data and checked
with exact arithmetic; the separate 185-term witness is certified in Lean.
"""
import json
from check_witness import ROOT, check

def greedy(n: int, limit: int = 10000) -> list[int]:
    if n < 2 or limit <= n:
        raise ValueError('Invalid bounded reconstruction parameters')
    numerator = n
    exponents = []
    for a in range(n+1, limit+1):
        numerator *= 2
        if numerator >= a:
            numerator -= a
            exponents.append(a)
        if numerator == 0:
            return exponents
    raise RuntimeError('Reconstruction budget ended without termination')

if __name__ == '__main__':
    blocks = [greedy(n) for n in (8,32,46)]
    if [(len(a), a[-1]) for a in blocks] != [(13,32),(9,46),(169,392)]:
        raise ValueError('Reconstruction differs from the paper table')
    exponents = [3,6] + blocks[0][:-1] + blocks[1][:-1] + blocks[2]
    recorded = json.loads((ROOT / 'paper-derived-witness.json').read_text())
    if exponents != recorded['terms']:
        raise ValueError('Reconstructed witness differs from recorded data')
    print(json.dumps(check(2, exponents), indent=2))
