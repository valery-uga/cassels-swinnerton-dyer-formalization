#!/usr/bin/env python3
"""One-process-group memory guard for macOS/Linux; no account-specific telemetry."""
import datetime,fcntl,os,re,signal,subprocess,sys,time
from pathlib import Path

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

def main():
    if len(sys.argv)<3:raise SystemExit('usage: serial_guard.py LOG COMMAND [ARGS...]')
    root=Path(__file__).resolve().parent.parent
    log=Path(sys.argv[1]).resolve();log.parent.mkdir(parents=True,exist_ok=True)
    if log.exists():raise SystemExit('Refusing to overwrite existing log: '+str(log))
    lockpath=Path('/private/tmp' if sys.platform=='darwin' else '/tmp')/'cassels-lean-single-compiler.lock'
    lock=lockpath.open('a+');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    free,baseline=memory_sample()
    if free<45:raise SystemExit(f'Not started: available memory {free:.0f}% is below 45%')
    began=time.monotonic();child=None
    def group_exists():
        try:os.killpg(child.pid,0);return True
        except ProcessLookupError:return False
    def stop():
        if child is None:return
        for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGKILL]:
            try:os.killpg(child.pid,sig)
            except ProcessLookupError:break
            try:child.wait(timeout=5)
            except subprocess.TimeoutExpired:pass
            if not group_exists():break
        child.wait()
        if group_exists():raise RuntimeError('Owned process group has not stopped; do not launch another check')
    def interrupted(_sig,_frame):
        stop();raise SystemExit(130)
    signal.signal(signal.SIGINT,interrupted);signal.signal(signal.SIGTERM,interrupted)
    env=dict(os.environ,LEAN_NUM_THREADS='1')
    with log.open('x') as output:
        child=subprocess.Popen(sys.argv[2:],cwd=root,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
        print(f'Running pid {child.pid}; log {log}',flush=True)
        samples=[];last_notice=began
        try:
            while child.poll() is None:
                try:child.wait(timeout=5);break
                except subprocess.TimeoutExpired:pass
                free,swaps=memory_sample();now=time.monotonic()
                samples.append((now,swaps));samples=[p for p in samples if now-p[0]<=65]
                swapping=len(samples)>1 and now-samples[0][0]>=50 and swaps-samples[0][1]>=65536
                if free<45 or swapping:
                    print(f'STOP: memory {free:.0f}% available; swap increase {swaps-baseline} pages',flush=True)
                    stop();raise SystemExit(130)
                if now-last_notice>=15:
                    print(f'Still running: {int(now-began)} seconds; memory {free:.0f}% available; {log.name}',flush=True)
                    last_notice=now
        except BaseException:
            stop();raise
        code=child.wait()
        if group_exists():
            stop();raise SystemExit('Unexpected child processes remained after command exit')
    print(f'Exit {code}; elapsed {time.monotonic()-began:.1f} seconds; log {log}',flush=True)
    raise SystemExit(code)

if __name__=='__main__':main()
