"""Regression tests for completion and dependency checks."""
import unittest
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
from types import SimpleNamespace
from check_dependencies import check
from audit import validate_dependency_pins, validate_terminal_scope


class DependencyPinTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        source = Path(__file__).resolve().parent.parent
        for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
            (self.root / name).write_bytes((source / name).read_bytes())

    def test_reviewed_pins_accepted(self):
        validate_dependency_pins(self.root)

    def test_toolchain_change_rejected(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:nightly\n')
        with self.assertRaisesRegex(RuntimeError, 'toolchain'):
            validate_dependency_pins(self.root)

    def test_requirement_change_rejected(self):
        path = self.root / 'lakefile.toml'
        path.write_text(path.read_text().replace('v4.33.1', 'master'))
        with self.assertRaisesRegex(RuntimeError, 'Mathlib requirement'):
            validate_dependency_pins(self.root)

    def test_mathlib_revision_change_rejected(self):
        path = self.root / 'lake-manifest.json'
        data = json.loads(path.read_text())
        next(p for p in data['packages'] if p['name'] == 'mathlib')['rev'] = '0' * 40
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(RuntimeError, 'lockfile revision'):
            validate_dependency_pins(self.root)

    def test_unlocked_transitive_dependency_rejected(self):
        path = self.root / 'lake-manifest.json'
        data = json.loads(path.read_text())
        next(p for p in data['packages'] if p['name'] != 'mathlib')['rev'] = 'main'
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(RuntimeError, 'immutable Git revision'):
            validate_dependency_pins(self.root)


class TerminalScopeTests(unittest.TestCase):
    def setUp(self):
        self.coverage = dict(inventory_complete=True, verification_scope='unconditional',
                             paper_roots=['DynamicalCStarAlgebras.result'])
        self.items = [dict(id='result', status='verified',
                           declaration='DynamicalCStarAlgebras.result')]

    def test_completed_inventory_accepted(self):
        validate_terminal_scope(self.coverage, self.items)

    def test_empty_inventory_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(self.coverage, [])

    def test_incomplete_inventory_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(self.coverage, inventory_complete=False), self.items)

    def test_unfinished_or_external_entries_rejected(self):
        for status in ['not_started', 'in_progress', 'external_assumption']:
            with self.subTest(status=status), self.assertRaises(RuntimeError):
                validate_terminal_scope(self.coverage, [dict(self.items[0], status=status)])

    def test_external_scope_rejected(self):
        with self.assertRaises(RuntimeError):
            validate_terminal_scope(dict(self.coverage, verification_scope='conditional'), self.items)

    def test_missing_or_unregistered_roots_rejected(self):
        for roots in [[], ['DynamicalCStarAlgebras.missing']]:
            with self.subTest(roots=roots), self.assertRaises(RuntimeError):
                validate_terminal_scope(dict(self.coverage, paper_roots=roots), self.items)


class DependencyScopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'lean/DynamicalCStarAlgebras').mkdir(parents=True)
        (self.root / 'lean/DynamicalCStarAlgebras/Final.lean').write_text('-- fixture\n')
        self.index = self.root / '.lake/build/lib/lean/DynamicalCStarAlgebras/Final.ilean'
        self.index.parent.mkdir(parents=True)
        self.data = dict(decls={name: [i, 0, i, 10] for i, name in enumerate(
            ['DynamicalCStarAlgebras.result', 'DynamicalCStarAlgebras.helper', 'DynamicalCStarAlgebras.tacticHelper'])}, references={
                json.dumps(dict(c=dict(m='DynamicalCStarAlgebras.Final', n='DynamicalCStarAlgebras.tacticHelper'))):
                    dict(usages=[[0, 0, 0, 1, 'DynamicalCStarAlgebras.result']])})
        self.kernel = dict(roots=['DynamicalCStarAlgebras.result'], declarations=[
            dict(name='DynamicalCStarAlgebras.result', deps=['DynamicalCStarAlgebras.helper']),
            dict(name='DynamicalCStarAlgebras.helper', deps=[])])
        self.inventory = dict(paper_roots=self.kernel['roots'],
                              items=[dict(declaration=n) for n in self.data['decls']])

    def run_check(self):
        self.index.write_text(json.dumps(self.data))
        (self.root / 'lean/coverage.json').write_text(json.dumps(self.inventory))
        with patch('check_dependencies.subprocess.run', return_value=SimpleNamespace(
                stdout=json.dumps(self.kernel))), patch('builtins.print'):
            check(self.root)

    def test_kernel_and_tactic_dependencies_retained(self):
        self.run_check()

    def test_unused_declaration_rejected(self):
        self.data['decls']['DynamicalCStarAlgebras.obsolete'] = [9, 0, 9, 10]
        self.inventory['items'].append(dict(declaration='DynamicalCStarAlgebras.obsolete'))
        with self.assertRaisesRegex(RuntimeError, 'outside the final proof'):
            self.run_check()

    def test_missing_inventory_entry_rejected(self):
        self.inventory['items'].pop()
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_stale_inventory_entry_rejected(self):
        self.inventory['items'].append(dict(declaration='DynamicalCStarAlgebras.removed'))
        with self.assertRaisesRegex(RuntimeError, 'Inventory/source mismatch'):
            self.run_check()

    def test_missing_kernel_source_rejected(self):
        self.kernel['declarations'].append(dict(name='DynamicalCStarAlgebras.missing', deps=[]))
        with self.assertRaisesRegex(RuntimeError, 'no source declaration'):
            self.run_check()

    def test_wrong_roots_rejected(self):
        self.inventory['paper_roots'] = ['DynamicalCStarAlgebras.wrong']
        with self.assertRaisesRegex(RuntimeError, 'Paper roots differ'):
            self.run_check()


if __name__ == '__main__':
    unittest.main()
