#!/usr/bin/env python3
"""Verify pinned sources; --run also builds serially and runs fresh declaration audits."""
import argparse, datetime, hashlib, json, os, signal, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
HERE = ROOT / 'verification'

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def verify():
    manifest=json.loads((HERE/'coverage.json').read_text())
    pins=json.loads((HERE/'source-pins.json').read_text())
    pins[manifest['manuscript']]=manifest['manuscript_sha256']
    for rel,expected in pins.items():
        path=ROOT/rel
        if Path(rel).is_absolute() or '..' in Path(rel).parts: raise ValueError('Unsafe pin path')
        if not path.is_file() or digest(path)!=expected: raise ValueError('Missing or changed pinned source: '+rel)
    rows=manifest['included_conclusions']
    if len(rows)!=25 or len({r['label'] for r in rows})!=25: raise ValueError('Coverage must contain 25 distinct labels')
    tex=(ROOT/manifest['manuscript']).read_text()
    for row in rows:
        if '\\label{'+row['label']+'}' not in tex: raise ValueError('Missing manuscript label: '+row['label'])
        for end in row['endpoints']:
            if end['source'] not in pins: raise ValueError('Unpinned endpoint source')
    print(f'PASS source integrity: {len(pins)-1} pinned files and manuscript; 25 mapped conclusions.',flush=True)
    return manifest

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run',action='store_true',help='Build and audit; without this flag only verify source integrity')
    parser.add_argument('--group',action='append',help='Audit group short name, e.g. SectionFour; repeat as needed')
    args=parser.parse_args();manifest=verify()
    groups=manifest['audit_groups']
    if args.group:
        unknown=set(args.group)-{g['module'].split('.')[-1] for g in groups}
        if unknown: raise ValueError('Unknown groups: '+str(sorted(unknown)))
        groups=[g for g in groups if g['module'].split('.')[-1] in args.group]
    print('Groups: '+', '.join(g['module'].split('.')[-1] for g in groups),flush=True)
    if not args.run:
        print('No Lean process launched. Add --run to build serially and audit. Comparator is separate.')
        return
    logdir=ROOT/'verification-results'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    logdir.mkdir(parents=True)
    targets=[g['module'] for g in groups]
    if not args.group:
        for name in ['OutsideSolution','OutsideChallenge','SectionFourSolution','SectionFourChallenge']:
            targets.append('AllCharacteristics.ManuscriptVerification.'+name)
        targets += ['AllCharacteristics.ComparatorChallenge.Solution','AllCharacteristics.ComparatorChallenge.Challenge']
    child=None
    def stop(_sig,_frame):
        if child is not None and child.poll() is None:
            child.send_signal(signal.SIGINT);child.wait()
        raise SystemExit(130)
    signal.signal(signal.SIGINT,stop);signal.signal(signal.SIGTERM,stop)
    def run(command):
        nonlocal child
        child=subprocess.Popen(command,cwd=ROOT);code=child.wait();child=None
        if code: raise SystemExit(code)
    selection=hashlib.sha256('\n'.join(targets).encode()).hexdigest()[:16]
    command=[sys.executable,str(HERE/'serial_build.py'),'--project',str(ROOT),'--state-dir',str(ROOT/'verification-results'/'build-state'/selection),'--run']
    for target in targets: command+=['--target',target]
    run(command)
    results=[]
    for index,group in enumerate(groups,1):
        short=group['module'].split('.')[-1];log=logdir/(short+'.log')
        print(f'AUDIT [{index}/{len(groups)}] {short}',flush=True)
        source=ROOT.joinpath(*group['module'].split('.')).with_suffix('.lean')
        run([sys.executable,str(HERE/'serial_guard.py'),str(log),'lake','env','lean','-M14000',str(source)])
        output=log.read_text()
        if 'AUDIT COMPLETE:' not in output: raise RuntimeError('Audit footer missing: '+str(log))
        for root in group['roots']:
            marker=('ROOT ' if short=='GlobalHilbertRoute' else 'PASS ')+root+':'
            if marker not in output: raise RuntimeError('Missing root result: '+root)
        results.append({'group':short,'roots':group['roots'],'exit':0,'log':log.name,'sha256':digest(log)})
    (logdir/'results.json').write_text(json.dumps({'groups':results,'comparator':'not_run','scope':'Imported-environment dependency audit, not independent kernel replay'},indent=2)+'\n')
    print(f'PASS: {len(groups)} audit groups. Logs: {logdir}. Comparator was not run.',flush=True)

if __name__=='__main__':
    try: main()
    except (ValueError,RuntimeError,FileNotFoundError) as exc: raise SystemExit(str(exc))
