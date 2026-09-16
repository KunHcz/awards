#!/usr/bin/env python3
"""Fetch the unchanged, pinned finite-graph proof for local checking only.
Third-party proof sources are not redistributed or relicensed by this package.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
BASE = ('https://raw.githubusercontent.com/SpringSense-Innovation-Institute/'
        'ai-for-math-lean/ae3ead960a494cf81b28541c477e50997cb03999/'
        'erdos-problems/erdos751/')

def fetch() -> None:
    expected = json.loads((ROOT / 'upstream-hashes.json').read_text())
    for name, record in expected.items():
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts:
            raise ValueError('Invalid upstream relative path')
        target = ROOT / '.upstream' / relative
        if target.exists():
            data = target.read_bytes()
        else:
            with urlopen(BASE + name, timeout=60) as response:
                data = response.read()
        if len(data) != record['bytes'] or hashlib.sha256(data).hexdigest() != record['sha256']:
            raise ValueError('Unexpected upstream contents: ' + name)
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    print('Verified %d pinned upstream source/configuration files.' % len(expected))

if __name__ == '__main__':
    fetch()
