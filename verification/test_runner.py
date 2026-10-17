#!/usr/bin/env python3
"""Runner regression tests. Every subprocess and process-group operation is mocked.

Run with: python3 -m unittest discover -s verification -p test_runner.py
No Lean, Lake, memory utility, compiler, or other child process is launched.
"""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


build = load('publication_serial_build_test', 'serial_build.py')
guard = load('publication_serial_guard_test', 'serial_guard.py')
check = load('publication_check_test', 'check.py')


class TemporaryProject(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name)
        self.state = self.project / 'state'
        for name, text in {
            'lean-toolchain': 'leanprover/lean4:test\n',
            'lakefile.toml': 'name = "test"\nweakLeanArgs = ["-M14000"]\n',
            'lake-manifest.json': '{}\n',
        }.items():
            (self.project / name).write_text(text)

    def module(self, name, text=''):
        path = self.project.joinpath(*name.split('.')).with_suffix('.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def isolated(self):
        stack = contextlib.ExitStack()
        # Never touch the live compiler's global lock or send real signals.
        original_open = Path.open
        def safe_open(path, *args, **kwargs):
            if path.name == 'cassels-lean-single-compiler.lock':
                return io.StringIO()
            return original_open(path, *args, **kwargs)
        stack.enter_context(mock.patch.object(Path, 'open', safe_open))
        stack.enter_context(mock.patch.object(build.fcntl, 'flock'))
        stack.enter_context(mock.patch.object(signal, 'signal'))
        stack.enter_context(mock.patch.dict(sys.modules, {'serial_guard': guard}))
        stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
        return stack

    def run_build(self, targets, codes=None, memory=90, run=True):
        argv = ['serial_build.py', '--project', str(self.project), '--state-dir', str(self.state)]
        if run:
            argv.append('--run')
        for name in targets:
            argv += ['--target', name]
        processes = []
        codes = iter(codes or [])
        def popen(*args, **kwargs):
            proc = mock.Mock()
            proc.wait.return_value = next(codes, 0)
            processes.append((args[0], kwargs))
            return proc
        with self.isolated(), mock.patch.object(sys, 'argv', argv), \
                mock.patch.object(guard, 'memory_sample', return_value=(memory, 0)), \
                mock.patch.object(build.subprocess, 'Popen', side_effect=popen):
            build.main()
        return processes


class DependencyTests(TemporaryProject):
    def test_nested_comments_preserve_lines_and_literal_strings(self):
        source = 'import A /- outer\n /- import Hidden -/\n end -/ B\n"--not comment /-"\n'
        cleaned = build.without_comments(source)
        self.assertEqual(cleaned.count('\n'), source.count('\n'))
        self.assertNotIn('Hidden', cleaned)
        self.assertIn('"--not comment /-"', cleaned)
        with self.assertRaisesRegex(ValueError, 'Unclosed'):
            build.without_comments('/- unclosed')

    def test_multi_import_targets_are_topological_and_deduplicated(self):
        self.module('PfaffianDescent.Base')
        self.module('PfaffianDescent.Left', 'public import PfaffianDescent.Base Mathlib\n')
        self.module('PfaffianDescent.Right', 'private import PfaffianDescent.Base\n')
        self.module('PfaffianDescent.Top', '-- import Ignored\nimport PfaffianDescent.Left /- nested /- x -/ -/ PfaffianDescent.Right\n')
        self.assertEqual(build.build_order(self.project, ['PfaffianDescent.Top', 'PfaffianDescent.Right']),
                         ['PfaffianDescent.Base', 'PfaffianDescent.Left', 'PfaffianDescent.Right', 'PfaffianDescent.Top'])

    def test_import_text_inside_multiline_or_raw_string_is_ignored(self):
        self.module('PfaffianDescent.Base')
        self.module('PfaffianDescent.Top', 'import PfaffianDescent.Base\ndef a := "hello\nimport PfaffianDescent.Fake\n"\ndef b := r##"quote " /- literal\nimport PfaffianDescent.FakeRaw\n"##\n')
        self.assertEqual(build.build_order(self.project, 'PfaffianDescent.Top'),
                         ['PfaffianDescent.Base', 'PfaffianDescent.Top'])

    def test_missing_local_and_cycles_fail(self):
        self.module('PfaffianDescent.A', 'import PfaffianDescent.Missing\n')
        with self.assertRaises(FileNotFoundError):
            build.build_order(self.project, 'PfaffianDescent.A')
        self.module('PfaffianDescent.A', 'import PfaffianDescent.B\n')
        self.module('PfaffianDescent.B', 'import PfaffianDescent.A\n')
        with self.assertRaisesRegex(ValueError, 'Import cycle'):
            build.build_order(self.project, 'PfaffianDescent.A')


class BuildTests(TemporaryProject):
    def setUp(self):
        super().setUp()
        self.module('PfaffianDescent.Base')
        self.top = self.module('PfaffianDescent.Top', 'import PfaffianDescent.Base\n')

    def test_plan_does_not_launch_or_create_state(self):
        self.assertEqual(self.run_build(['PfaffianDescent.Top'], run=False), [])
        self.assertFalse(self.state.exists())

    def test_dependency_check_precedes_every_leaf_and_final_validation(self):
        calls = self.run_build(['PfaffianDescent.Top'])
        self.assertEqual([args[-4:] for args, _ in calls], [
            ['lake', 'build', '--no-build', '+PfaffianDescent.Base:deps'],
            [str(self.project.resolve()), 'lake', 'build', '+PfaffianDescent.Base:olean'],
            ['lake', 'build', '--no-build', '+PfaffianDescent.Top:deps'],
            [str(self.project.resolve()), 'lake', 'build', '+PfaffianDescent.Top:olean'],
            ['lake', 'build', '--no-build', '+PfaffianDescent.Top:olean'],
        ])
        for _, kwargs in calls:
            self.assertEqual(kwargs['env']['LEAN_NUM_THREADS'], '1')
            self.assertEqual(kwargs['env']['CASSELS_LEAN_PARALLEL'], '1')
            self.assertNotIn('CASSELS_LEAN_SLOT', kwargs['env'])
            self.assertTrue(kwargs['start_new_session'])

    def test_failure_keeps_only_completed_modules_and_resumes(self):
        with self.assertRaisesRegex(SystemExit, 'exit 7'):
            self.run_build(['PfaffianDescent.Top'], codes=[0, 0, 7])
        saved = json.loads((self.state / 'state.json').read_text())
        self.assertEqual(saved['next_index'], 1)
        calls = self.run_build(['PfaffianDescent.Top'])
        self.assertEqual(len(calls), 3)
        self.assertTrue(all('Base' not in args[-1] for args, _ in calls))
        # Completed runs still verify the requested targets are current.
        self.assertEqual(len(self.run_build(['PfaffianDescent.Top'])), 1)

    def test_changed_source_resets_resume_fingerprint(self):
        self.run_build(['PfaffianDescent.Top'])
        self.top.write_text(self.top.read_text() + '-- changed\n')
        self.assertEqual(len(self.run_build(['PfaffianDescent.Top'])), 5)

    def test_invalid_matching_resume_index_is_rejected(self):
        self.run_build(['PfaffianDescent.Top'])
        path = self.state / 'state.json'
        state = json.loads(path.read_text())
        for bad in (-1, 3, True, '1'):
            state['next_index'] = bad
            path.write_text(json.dumps(state))
            with self.assertRaisesRegex(ValueError, 'Invalid resume index'):
                self.run_build(['PfaffianDescent.Top'])

    def test_memory_stop_before_launch_does_not_advance_state(self):
        with self.assertRaisesRegex(SystemExit, 'before launch'):
            self.run_build(['PfaffianDescent.Top'], memory=44)
        self.assertFalse((self.state / 'state.json').exists())

    def test_missing_or_excessive_lean_memory_limit_rejected(self):
        for contents in ('name = "x"\n', 'weakLeanArgs = ["-M14001"]\n', 'weakLeanArgs = ["-M0"]\n'):
            (self.project / 'lakefile.toml').write_text(contents)
            with self.assertRaisesRegex(SystemExit, 'memory limit'):
                self.run_build(['PfaffianDescent.Top'])


class GuardTests(TemporaryProject):
    def run_guard(self, samples, waits, poll=None, times=None):
        log = self.project / 'guard.log'
        proc = mock.Mock(pid=12345)
        proc.poll.return_value = poll
        waits = iter(waits)
        def wait(*args, **kwargs):
            result = next(waits, 0)
            if isinstance(result, BaseException):
                raise result
            return result
        proc.wait.side_effect = wait
        group_calls = []
        def killpg(pid, sig):
            group_calls.append((pid, sig))
            # First actual stop request succeeds, then the group is absent.
            if sig == 0 or len(group_calls) > 1:
                raise ProcessLookupError()
        with self.isolated(), mock.patch.object(sys, 'argv', ['serial_guard.py', str(log), 'fake-command']), \
                mock.patch.object(guard, 'memory_sample', side_effect=samples), \
                mock.patch.object(guard.subprocess, 'Popen', return_value=proc) as popen, \
                mock.patch.object(guard.os, 'killpg', side_effect=killpg), \
                mock.patch.object(guard.time, 'monotonic', side_effect=times or (lambda: 0)):
            with self.assertRaises(SystemExit) as caught:
                guard.main()
        return caught.exception.code, popen, group_calls

    def test_low_initial_memory_never_starts_child(self):
        code, popen, groups = self.run_guard([(44, 0)], [])
        self.assertIn('Not started', code)
        popen.assert_not_called()
        self.assertEqual(groups, [])

    def test_child_error_exit_is_propagated(self):
        code, _, groups = self.run_guard([(90, 0)], [7], poll=7)
        self.assertEqual(code, 7)
        self.assertEqual(groups, [(12345, 0)])

    def test_runtime_memory_drop_stops_owned_group(self):
        timeout = subprocess.TimeoutExpired('mock', 5)
        code, _, groups = self.run_guard([(90, 0), (44, 0)], [timeout, 0])
        self.assertEqual(code, 130)
        self.assertIn((12345, signal.SIGINT), groups)

    def test_sustained_swap_growth_stops_owned_group(self):
        timeout = subprocess.TimeoutExpired('mock', 5)
        code, _, groups = self.run_guard([(90, 0), (90, 0), (90, 65536)],
                                         [timeout, timeout, 0], times=[0, 5, 60])
        self.assertEqual(code, 130)
        self.assertIn((12345, signal.SIGINT), groups)

    def test_linux_memory_sample_uses_available_and_swap_counter(self):
        def read(path, *args, **kwargs):
            return 'MemTotal: 1000 kB\nMemAvailable: 460 kB\n' if str(path) == '/proc/meminfo' else 'pswpout 27\n'
        with mock.patch.object(sys, 'platform', 'linux'), mock.patch.object(Path, 'read_text', read), \
                mock.patch.object(guard.subprocess, 'check_output') as child:
            self.assertEqual(guard.memory_sample(), (46, 27))
            child.assert_not_called()

    def test_macos_unreadable_memory_telemetry_fails_closed(self):
        with mock.patch.object(sys, 'platform', 'darwin'), \
                mock.patch.object(guard.subprocess, 'check_output', return_value='unparseable'):
            with self.assertRaisesRegex(RuntimeError, 'memory pressure'):
                guard.memory_sample()


class SourceIntegrityTests(TemporaryProject):
    def setUp(self):
        super().setUp()
        self.here = self.project / 'verification'
        self.here.mkdir()
        source = self.project / 'endpoint.lean'
        source.write_text('-- pinned\n')
        labels = ['claim:'+str(i) for i in range(25)]
        tex = self.project / '2-proofs.tex'
        tex.write_text('\n'.join('\\label{'+label+'}' for label in labels))
        self.manifest = dict(manuscript='2-proofs.tex', manuscript_sha256=check.digest(tex),
                             included_conclusions=[dict(label=l, endpoints=[dict(source='endpoint.lean')]) for l in labels])
        self.pins = {'endpoint.lean': check.digest(source)}
        self.save()

    def save(self):
        (self.here / 'coverage.json').write_text(json.dumps(self.manifest))
        (self.here / 'source-pins.json').write_text(json.dumps(self.pins))

    def verify(self):
        with mock.patch.object(check, 'ROOT', self.project), mock.patch.object(check, 'HERE', self.here), \
                contextlib.redirect_stdout(io.StringIO()), mock.patch.object(check.subprocess, 'Popen') as child:
            result = check.verify()
            child.assert_not_called()
            return result

    def test_valid_source_integrity_is_read_only(self):
        self.assertEqual(self.verify(), self.manifest)

    def test_changed_source_and_unsafe_pin_paths_rejected(self):
        (self.project / 'endpoint.lean').write_text('-- changed\n')
        with self.assertRaisesRegex(ValueError, 'changed pinned source'):
            self.verify()
        self.pins = {'../outside': '0'*64}
        self.save()
        with self.assertRaisesRegex(ValueError, 'Unsafe pin path'):
            self.verify()

    def test_duplicate_labels_and_unpinned_endpoint_rejected(self):
        self.manifest['included_conclusions'][1]['label'] = self.manifest['included_conclusions'][0]['label']
        self.save()
        with self.assertRaisesRegex(ValueError, '25 distinct labels'):
            self.verify()
        self.manifest['included_conclusions'][1]['label'] = 'claim:1'
        self.manifest['included_conclusions'][0]['endpoints'][0]['source'] = 'unlisted.lean'
        self.save()
        with self.assertRaisesRegex(ValueError, 'Unpinned endpoint'):
            self.verify()


if __name__ == '__main__':
    unittest.main()
