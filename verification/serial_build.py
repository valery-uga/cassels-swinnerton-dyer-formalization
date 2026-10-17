#!/usr/bin/env python3
"""Plan or resume a guarded, one-module-at-a-time publication build on macOS/Linux.

Uses the accompanying portable memory guard. Does not copy caches,
modify Lean sources, install dependencies, or start a build without --run.
"""
import argparse
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys


def without_comments(text, *, mask_strings=False):
    # Preserve newlines; imports inside strings must not become dependencies.
    out, i, depth, quoted, raw_end = [], 0, 0, False, None
    def string_text(value):
        out.append(''.join('\n' if c == '\n' else ' ' for c in value)
                   if mask_strings else value)
    while i < len(text):
        pair, ch = text[i:i + 2], text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if ch == '\n' else ' ')
        elif raw_end is not None:
            if text.startswith(raw_end, i):
                string_text(raw_end); i += len(raw_end); raw_end = None; continue
            string_text(ch)
        elif quoted:
            string_text(ch)
            if ch == '\\' and i + 1 < len(text):
                i += 1; string_text(text[i])
            elif ch == '"': quoted = False
        elif pair == '/-':
            depth = 1; out.append(' '); i += 2; continue
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        else:
            raw = re.match(r'r(#+)?"', text[i:]) if ch == 'r' else None
            if raw and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
                raw_end = '"' + (raw[1] or '')
                string_text(raw[0]); i += len(raw[0]); continue
            if ch == '"':
                quoted = True; string_text(ch); i += 1; continue
            out.append(ch)
        i += 1
    if depth: raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def build_order(project, target):
    order, visiting, visited = [], set(), set()
    def visit(module):
        if module in visited: return
        if module in visiting: raise ValueError(f'Import cycle: {module}')
        path = project.joinpath(*module.split('.')).with_suffix('.lean')
        if not path.is_file():
            if module.startswith(('AllCharacteristics.', 'PfaffianDescent.')):
                raise FileNotFoundError(path)
            return  # External dependencies must already be built/cached.
        visiting.add(module)
        source = without_comments(path.read_text(), mask_strings=True)
        for match in re.finditer(r'^\s*(?:(?:public|private)\s+)?import[ \t]+([^\n]+)', source, re.M):
            for dependency in match[1].split(): visit(dependency)
        visiting.remove(module)
        visited.add(module)
        order.append(module)
    for item in ([target] if isinstance(target, str) else target): visit(item)
    return order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--target', action='append', help='Repeat to build several targets in one dependency traversal')
    parser.add_argument('--state-dir', type=Path, default=Path('verification-results/serial-state'))
    parser.add_argument('--run', action='store_true', help='Actually build; default only prints the plan')
    args = parser.parse_args()
    project = args.project.expanduser().resolve()
    args.target = args.target or ['AllCharacteristics.ComparatorChallenge.Solution']
    order = build_order(project, args.target)
    top_level = (project / 'lakefile.toml').read_text().split('[[', 1)[0]
    match = re.search(r'(?m)^\s*weakLeanArgs\s*=\s*(\[[^\]]*\])', top_level)
    lean_args = json.loads(match[1]) if match else []
    limits = [int(a[2:]) for a in lean_args if re.fullmatch(r'-M\d+', a)]
    if not limits or not 0 < limits[-1] <= 14000:
        raise SystemExit('Require a positive memory limit <= -M14000 in top-level weakLeanArgs')
    signature = hashlib.sha256(str(project).encode())
    for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
        signature.update((project / name).read_bytes())
    for module in order:
        signature.update(module.encode())
        signature.update(project.joinpath(*module.split('.')).with_suffix('.lean').read_bytes())
    fingerprint = signature.hexdigest()
    state_dir = args.state_dir.expanduser().resolve()
    state_path = state_dir / 'state.json'
    start = 0
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state.get('fingerprint') == fingerprint:
            start = state['next_index']
            if type(start) is not int or not 0 <= start <= len(order):
                raise ValueError('Invalid resume index in state.json')
    print(f'Project: {project}\nTarget: {args.target}\nLocal modules: {len(order)}\nResume index: {start}', flush=True)
    print('Each build is preceded by a no-build dependency check. Missing dependencies stop the run.', flush=True)
    if not args.run:
        print('PLAN ONLY: no Lean or Lake process launched. Add --run to execute.')
        return
    if sys.platform not in ('darwin','linux'): raise SystemExit('Supported platforms: macOS/Linux')
    guard = Path(__file__).resolve().with_name('serial_guard.py')
    if not guard.is_file(): raise SystemExit(f'Missing guard: {guard}')
    state_dir.mkdir(parents=True, exist_ok=True)
    with (state_dir / 'runner.lock').open('a+') as run_lock:
        fcntl.flock(run_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        logs = state_dir / datetime.datetime.now().strftime('%Y%m%d-%H%M%S-%f')
        logs.mkdir()
        print(f'Logs: {logs}', flush=True)
        env = dict(os.environ, CASSELS_LEAN_PARALLEL='1', LEAN_NUM_THREADS='1')
        env.pop('CASSELS_LEAN_SLOT', None)
        child = None
        def interrupt(signum, _frame):
            if child is not None and child.poll() is None:
                child.send_signal(signal.SIGINT)
                child.wait()
            raise SystemExit(130)
        signal.signal(signal.SIGINT, interrupt)
        signal.signal(signal.SIGTERM, interrupt)

        def checked(command, log):
            nonlocal child
            from serial_guard import memory_sample
            available, _ = memory_sample()
            if available < 45:
                raise SystemExit('Stopped before launch: available memory below 45%')
            # Select the requested project while retaining the guarded process group.
            adapter = 'import os,sys; os.chdir(sys.argv[1]); os.execvp(sys.argv[2], sys.argv[2:])'
            invocation = [sys.executable, str(guard), str(log), sys.executable, '-c', adapter, str(project), *command]
            child = subprocess.Popen(invocation, env=env, start_new_session=True)
            code = child.wait()
            child = None
            # The guard verifies that its owned process group is gone.
            lockpath = Path('/private/tmp' if sys.platform == 'darwin' else '/tmp') / 'cassels-lean-single-compiler.lock'
            with lockpath.open('a+') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if code:
                if log.exists(): print('\n'.join(log.read_text(errors='replace').splitlines()[-35:]), flush=True)
                raise SystemExit(f'Stopped (exit {code}). Inspect {log}. Completed modules are retained; rerun to resume.')

        for index in range(start, len(order)):
            module = order[index]
            print(f'[{index + 1}/{len(order)}] {module}', flush=True)
            checked(['lake', 'build', '--no-build', f'+{module}:deps'], logs / f'{index:05d}-deps.log')
            checked(['lake', 'build', f'+{module}:olean'], logs / f'{index:05d}-build.log')
            temp = state_dir / 'state.tmp'
            temp.write_text(json.dumps({'fingerprint': fingerprint, 'next_index': index + 1, 'last_module': module}, indent=2) + '\n')
            temp.replace(state_path)
        # Revalidate after resume, including when a prior invocation completed.
        for index, target in enumerate(args.target):
            checked(['lake', 'build', '--no-build', f'+{target}:olean'], logs / f'final-{index}-current.log')
        print('Selected targets are up-to-date. This was a Lean build, not a Comparator run.', flush=True)


if __name__ == '__main__':
    main()
