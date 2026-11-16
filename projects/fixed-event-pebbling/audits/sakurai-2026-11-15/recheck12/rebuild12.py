#!/usr/bin/env python3
"""Clean rebuild of the 11-12..14 Lean units behind v15's Lean section.

Pool: Lean sources extracted (read-only copies) from showa's sakurai bundles.
Same-name modules across bundles were checked to be byte-identical beforehand.
Builds the import closure of TARGETS from source into one work dir, one
systemd-run per module (MemoryMax=2G, RuntimeMaxSec=120, idle CPU weight),
lean 4.31.0 -j1. Then compiles axiom-check files printing the claimed theorems.
"""
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import time

LEAN = '<home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'
ROOTS = ['el/erasure_lean_v11_followup_bundle_20261112', 'u12/z1', 'u12/z2', 'u12/z3',
         'u12/z4', 'u12/z5', 'u12/pebbling-physical-20261114T0300',
         'u12/pebbling-recurrence-20261114T0400', 'u12/pebbling-remaining-perm-20261114T0500',
         'u12/pebbling-board-perm-20261114T0700']
TARGETS = ['PricedRecurrence', 'PhysicalExactOptimum', 'FamilyAllOptimal', 'ActualCheckpoint',
           'FullSlotAssembly', 'WholeBijection', 'PhysicalCount', 'LabelledCount', 'PhysicalCover',
           'RawComponentCount', 'PhysicalComponentCount', 'RawSwapLift', 'ComponentWordCount',
           'SignaturePhysicalExact', 'SignatureExact', 'ComponentMixedRadix', 'FinitePartialDFA',
           'PhysicalAutomataExact', 'FiniteAlphabetDFA', 'FinitePartialEdges', 'PhysicalTransitionCount',
           'Multiplicity', 'PrecedenceCover', 'PrecedenceGuard', 'RationalObstruction', 'ComponentExact',
           'LocalCounts', 'Physical', 'Recurrence', 'RemainingPerm', 'BoardPerm']


def imports(p):
    out = []
    for line in p.read_text(errors='replace').splitlines():
        m = re.match(r'\s*import\s+(.*)', line)
        if m:
            out += m.group(1).split()
    return out


def main(base, work):
    base, work = pathlib.Path(base), pathlib.Path(work)
    pool = {}
    for r in ROOTS:
        for f in sorted((base / r).rglob('*.lean')):
            if f.stem.startswith('attempt') or f.stem.startswith('candidate'):
                continue
            pool.setdefault(f.stem, f)
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for i in imports(pool[m]):
            if i in pool:
                visit(i)
            elif not (i.startswith('Std') or i.startswith('Init') or i.startswith('Lean')):
                raise SystemExit(f'missing import {i} of {m}')
        order.append(m)
    for t in TARGETS:
        visit(t)
    work.mkdir(parents=True, exist_ok=True)
    srcsha = {}
    for m in order:
        shutil.copy2(pool[m], work / (m + '.lean'))
        srcsha[m] = hashlib.sha256((work / (m + '.lean')).read_bytes()).hexdigest()
    (work / 'ORDER.json').write_text(json.dumps(order))
    print('closure', len(order), flush=True)
    steps = []
    failed = set()
    for idx, m in enumerate(order):
        if (work / (m + '.olean')).exists():
            continue
        bad = [i for i in imports(work / (m + '.lean')) if i in failed]
        if bad:
            failed.add(m)
            steps.append(dict(module=m, rc=None, skipped_due_to=bad))
            continue
        cmd = ['systemd-run', '--user', '--wait', '--pipe', '--quiet',
               f'--unit=rb12-{idx}-{int(time.time())}', '-p', 'MemoryMax=2G', '-p', 'MemorySwapMax=0',
               '-p', 'RuntimeMaxSec=120', '-p', 'CPUWeight=idle', '-p', 'Nice=19',
               '-p', f'WorkingDirectory={work}', '--setenv', 'LEAN_PATH=.',
               LEAN, '-j1', '-M1800', '-o', m + '.olean', m + '.lean']
        t0 = time.time()
        p = subprocess.run(cmd, capture_output=True, text=True)
        log = p.stdout + p.stderr
        (work / (m + '.rebuild.log')).write_text(log)
        st = dict(module=m, rc=p.returncode, sec=round(time.time() - t0, 2),
                  olean=(work / (m + '.olean')).exists(), sorryAx='sorryAx' in log,
                  errors=sum(1 for x in log.splitlines() if ': error' in x))
        steps.append(st)
        if p.returncode != 0 or not st['olean']:
            failed.add(m)
            print('FAIL', st, flush=True)
        if idx % 25 == 0:
            print(idx, m, st['sec'], flush=True)
    prev = json.loads((work / 'STEPS.json').read_text())['steps'] if (work / 'STEPS.json').exists() else []
    (work / 'STEPS.json').write_text(json.dumps(dict(steps=prev + steps, srcsha=srcsha), indent=1))
    print('done', len(steps), 'fail' if any(s['rc'] != 0 for s in steps) else 'ok', flush=True)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
