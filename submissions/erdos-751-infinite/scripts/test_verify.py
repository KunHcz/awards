#!/usr/bin/env python3
"""Test the source inventory, pinned inputs and fail-closed axiom checks."""
import hashlib
import json
from pathlib import Path
import re
import unittest
import verify

ROOT = Path(__file__).resolve().parents[1]

class AuditTests(unittest.TestCase):
    def test_actual_source_inventory(self):
        cfg = json.loads((ROOT / 'verification-config.json').read_text())
        self.assertEqual(len(cfg['theorems']), 8)
        verify.guard((ROOT / 'Erdos751Extension.lean').read_text(), cfg['imports'], cfg['theorems'])

    def test_imported_theorem_attribution(self):
        source = (ROOT / 'Erdos751Extension.lean').read_text()
        self.assertIn('#print axioms Erdos751.Main.erdos_751_strong', source)
        self.assertNotIn('theorem erdos_751_strong', source)

    def test_standard_axioms(self):
        result = verify.audit("'T' depends on axioms: [propext, Classical.choice, Quot.sound]", ['T'])
        self.assertEqual(len(result['T']), 3)

    def test_axiom_free(self):
        self.assertEqual(verify.audit("'T' does not depend on any axioms", ['T']), {'T': []})

    def test_missing_audit(self):
        with self.assertRaises(ValueError):
            verify.audit('', ['T'])

    def test_duplicate_audit(self):
        with self.assertRaises(ValueError):
            verify.audit("'T' does not depend on any axioms\n" * 2, ['T'])

    def test_unapproved_axioms(self):
        for axiom in ['sorryAx', 'forged', 'Lean.ofReduceBool']:
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                verify.audit("'T' depends on axioms: [" + axiom + "]", ['T'])

    def test_proof_shortcuts(self):
        for source in ['theorem T : False := by sorry', 'axiom forged : False', 'unsafe def x := 1']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                verify.guard(source, [], ['T'])

    def test_no_finite_type_restriction_on_final_result(self):
        source = (ROOT / 'Erdos751Extension.lean').read_text()
        final = source.split('theorem close_cycle_lengths')[1].split(':= by')[0]
        self.assertNotIn('Fintype', final)
        self.assertNotIn('[Finite', final)
        self.assertIn('(4 : ℕ∞) ≤ G.chromaticNumber', final)

    def test_all_upstream_hashes(self):
        hashes = json.loads((ROOT / 'upstream-hashes.json').read_text())
        self.assertEqual(len(hashes), 9)
        for name, meta in hashes.items():
            data = (ROOT / '.upstream' / name).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), meta['sha256'])
            self.assertEqual(len(data), meta['bytes'])

    def test_checker_not_imported_by_proof(self):
        source = (ROOT / 'Erdos751Extension.lean').read_text()
        self.assertNotIn('import Lean.Replay', source)
        self.assertNotIn('import scripts.Replay', source)

    def test_mutations_match_actual_source(self):
        cfg = json.loads((ROOT / 'verification-config.json').read_text())
        source = (ROOT / 'Erdos751Extension.lean').read_text()
        for before, after in cfg['mutations'].values():
            self.assertIn(before, source)
            self.assertNotEqual(before, after)

    def test_replay_rejects_missing_confirmation(self):
        for text in ['', 'PASS', 'PANIC: missing declaration']:
            with self.subTest(text=text), self.assertRaises(RuntimeError):
                verify.validate_replay(text)

    def test_replay_requires_both_controls(self):
        text = ('Fresh target-closure replay: 9 targets;\n'
                'CONTROL: kernel accepted True from True.intro\n'
                'CONTROL: kernel rejected False from True.intro\n'
                'Checked 10931 logical declarations in target dependency closures\n'
                'PASS: all nine targets and their complete transitive logical dependencies replayed from an empty environment')
        verify.validate_replay(text)
        for marker in ['CONTROL: kernel rejected False from True.intro',
                       'CONTROL: kernel accepted True from True.intro', 'Checked 10931']:
            with self.subTest(marker=marker), self.assertRaises(RuntimeError):
                verify.validate_replay(text.replace(marker, ''))

if __name__ == '__main__':
    unittest.main()
