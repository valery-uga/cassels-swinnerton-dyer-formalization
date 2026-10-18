#!/usr/bin/env python3
"""One-process-group memory guard for macOS/Linux; no account-specific telemetry."""
import datetime,fcntl,json,os,re,signal,subprocess,sys,time
from pathlib import Path

# Lowered from 45 at the user's request for the Comparator export/replay run.
MIN_AVAILABLE_PERCENT = 20

def process_metrics(pgid):
    """Optional read-only telemetry; failures never count as process absence."""
    try:
        result = subprocess.run(['ps', '-axo', 'pgid=,pcpu=,rss='],
                                capture_output=True, text=True, timeout=5)
        if result.returncode != 0:
            return 'process metrics unavailable'
        rows = [line.split() for line in result.stdout.splitlines() if line.strip()]
        if not rows or any(len(row) != 3 for row in rows):
            return 'process metrics unavailable'
        owned = [(float(cpu), int(rss)) for group, cpu, rss in rows if int(group) == pgid]
        if not owned:
            return 'process group not present in telemetry snapshot'
        return (f'group CPU {sum(cpu for cpu, _ in owned):.1f}%; '
                f'group RSS {sum(rss for _, rss in owned)/1048576:.2f} GiB; '
                f'{len(owned)} processes')
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return 'process metrics unavailable'

def memory_sample():
    if sys.platform == 'darwin':
        text=subprocess.check_output(['memory_pressure','-Q'],text=True)
        match=re.search(r'memory free percentage: (\d+)%',text)
        if not match: raise RuntimeError('Cannot read memory pressure')
        vm=subprocess.check_output(['vm_stat'],text=True)
        swaps=re.search(r'^Swapouts:\s+(\d+)',vm,re.M)
        if not swaps: raise RuntimeError('Cannot read swap counter')
        return int(match[1]),int(swaps[1])
    if sys.platform.startswith('linux'):
        values={line.split(':')[0]:int(line.split()[1]) for line in Path('/proc/meminfo').read_text().splitlines()}
        swaps=dict(line.split() for line in Path('/proc/vmstat').read_text().splitlines())
        return 100*values['MemAvailable']/values['MemTotal'],int(swaps['pswpout'])
    raise RuntimeError('Supported platforms: macOS and Linux')

def group_exists(pgid):
    """EPERM is unknown, never proof that a process group is gone."""
    try:
        os.killpg(pgid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # Some macOS execution contexts deny the signal probe. A successful,
        # complete process inventory can still establish absence. Never signal
        # individual PIDs obtained from this fallback.
        result = subprocess.run(['ps', '-axo', 'pid=,pgid=,stat='],
                                capture_output=True, text=True, timeout=5)
        if result.returncode != 0:
            raise RuntimeError('Process-group probe denied and process inventory unavailable')
        groups = []
        for line in result.stdout.splitlines():
            if not line.strip():
                continue
            fields = line.split()
            if len(fields) != 3 or not fields[0].isdigit() or not fields[1].isdigit():
                raise RuntimeError('Process inventory could not be parsed safely')
            groups.append(int(fields[1]))
        if not groups:
            raise RuntimeError('Empty process inventory cannot establish group absence')
        return pgid in groups

def main():
    if len(sys.argv)<3:raise SystemExit('usage: serial_guard.py LOG COMMAND [ARGS...]')
    root=Path(__file__).resolve().parent.parent
    log=Path(sys.argv[1]).resolve();log.parent.mkdir(parents=True,exist_ok=True)
    if log.exists():raise SystemExit('Refusing to overwrite existing log: '+str(log))
    lockpath=Path('/private/tmp' if sys.platform=='darwin' else '/tmp')/'cassels-lean-single-compiler.lock'
    with lockpath.open('a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        blocked=lockpath.with_suffix('.unconfirmed.json')
        if blocked.exists():
            raise SystemExit(f'A previous shutdown was not confirmed. Inspect {blocked} and stop the recorded process group before removing this marker. No command launched.')
        free,baseline=memory_sample()
        if free<MIN_AVAILABLE_PERCENT:raise SystemExit(f'Not started: available memory {free:.0f}% is below {MIN_AVAILABLE_PERCENT}%')
        began=time.monotonic();child=None
        def owned_group_exists():
            return group_exists(child.pid)
        def stop():
            if child is None:
                return
            # Reap the direct child before probing an already-finished group.
            reaped = child.poll() is not None
            if reaped and not owned_group_exists():
                return
            for sig in [signal.SIGINT, signal.SIGTERM, signal.SIGKILL]:
                try:
                    os.killpg(child.pid, sig)
                except ProcessLookupError:
                    pass
                except PermissionError:
                    # The group may have disappeared between inspection and signal.
                    if owned_group_exists():
                        raise RuntimeError(f'Permission denied stopping process group {child.pid}')
                try:
                    child.wait(timeout=5)
                    reaped = True
                except subprocess.TimeoutExpired:
                    reaped = False
                if reaped and not owned_group_exists():
                    return
            raise RuntimeError(f'Process group {child.pid} has not been confirmed stopped')
        def interrupted(_sig,_frame):
            raise SystemExit(130)
        signal.signal(signal.SIGINT,interrupted);signal.signal(signal.SIGTERM,interrupted)
        env=dict(os.environ,LEAN_NUM_THREADS='1')
        with log.open('x') as output:
            try:
                child=subprocess.Popen(sys.argv[2:],cwd=root,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
                print(f'Running pid {child.pid}; cutoff {MIN_AVAILABLE_PERCENT}% available; swap policy warn; log {log}',flush=True)
                samples=[];last_notice=began;last_swap_notice=began-60
                while child.poll() is None:
                    try:child.wait(timeout=5);break
                    except subprocess.TimeoutExpired:pass
                    free,swaps=memory_sample();now=time.monotonic()
                    samples.append((now,swaps));samples=[p for p in samples if now-p[0]<=65]
                    swapping=len(samples)>1 and now-samples[0][0]>=50 and swaps-samples[0][1]>=65536
                    if free<MIN_AVAILABLE_PERCENT:
                        print(f'STOP: memory {free:.0f}% available; swap increase {swaps-baseline} pages',flush=True)
                        raise SystemExit(130)
                    if swapping and now-last_swap_notice>=60:
                        print(f'WARNING: sustained system-wide swapping; continuing; swap increase {swaps-baseline} pages',flush=True)
                        last_swap_notice=now
                    if now-last_notice>=15:
                        metrics = ('; '+process_metrics(child.pid)) if os.environ.get('CSD_GUARD_PROCESS_METRICS') == '1' else ''
                        print(f'Still running: {int(now-began)} seconds; memory {free:.0f}% available; swap increase {swaps-baseline} pages{metrics}; {log.name}',flush=True)
                        last_notice=now
                code=child.wait(timeout=5)
                if owned_group_exists():
                    raise RuntimeError('Unexpected child processes remained after command exit')
            except BaseException as original:
                # One cleanup attempt, even when cleanup itself cannot confirm exit.
                signal.signal(signal.SIGINT, signal.SIG_IGN)
                signal.signal(signal.SIGTERM, signal.SIG_IGN)
                try:
                    stop()
                except Exception as cleanup_error:
                    record={'pid':child.pid, 'pgid':child.pid, 'log':str(log),
                            'recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            'reason':str(cleanup_error)}
                    blocked.write_text(json.dumps(record,indent=2)+'\n')
                    print(f'STOP UNCONFIRMED: {cleanup_error}. Original stop: {original}.',flush=True)
                    print(f'Do not start another run. Check the recorded process group; marker: {blocked}',flush=True)
                    raise SystemExit(2) from None
                print('Owned command and process group confirmed stopped.',flush=True)
                if isinstance(original, SystemExit):
                    raise
                if isinstance(original, KeyboardInterrupt):
                    raise SystemExit(130) from None
                raise SystemExit(f'Guard stopped: {original}') from None
        print(f'Exit {code}; elapsed {time.monotonic()-began:.1f} seconds; log {log}',flush=True)
        raise SystemExit(code)

if __name__=='__main__':main()
