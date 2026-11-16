#!/usr/bin/env python3
"""Mutation checks: copy a GREEN rebuilt unit dir (sources + rebuilt deps),
apply one textual mutation to the target statement, recompile only the target
under the same limits, and expect failure (rc != 0)."""
import json
import pathlib
import shutil
import subprocess
import sys
import time

LEAN = '<home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'
ML = '<local>/dev/github.com/yokoyama-lab/reversible-pebbling-lean-lowend/.lake/packages'
ML_PKGS = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph',
           'mathlib', 'plausible', 'proofwidgets']

MUTS = [
 ('M1', 'PEBBLING-SIGNATURE-COVER-CARD-20261115-A1', 'SignatureCoverCard',
  'signature_number_le_cover_card', '    signatureNumber D ≤ Fintype.card I := by\n  obtain',
  '    signatureNumber D + 1 ≤ Fintype.card I := by\n  obtain', True),
 ('M2', 'PEBBLING-SIGNATURE-COVER-UNIQUE-20261115-A1', 'SignatureCoverUnique',
  'minimum_cover_language_bijection',
  '    (hcard : Fintype.card I = signatureNumber D) :\n    ∃ f : SignatureClass D → I',
  '    (hcard : Fintype.card I = signatureNumber D + 1) :\n    ∃ f : SignatureClass D → I', True),
 ('M3', 'PEBBLING-PHYSICAL-CAPACITY-20261115-A1', 'PhysicalStepCapacity',
  'step_true_iff_false_and_capacity', 'some after ∧ after.length ≤ 5 := by',
  'some after ∧ after.length ≤ 4 := by', False),
 ('M4', 'PEBBLING-CAPACITY-EDGE-I-20261115-A1', 'CapacityCommonEdgeI',
  'capacity_common_edge', '    w.idxOf 1 < w.idxOf 8 := by',
  '    w.idxOf 8 < w.idxOf 1 := by', False),
 ('M5', 'PEBBLING-PHYSICAL-REPLAY-COST-20261115-A2', 'PhysicalReplayCost',
  'successful_replayWithCost_cost',
  'total = PebblingSignature.cost (eventIdIncrement events) (board.length : Int) ids := by',
  'total = PebblingSignature.cost (eventIdIncrement events) ((board.length : Int) + 1) ids := by', False),
]


def main(rebuild_dir, mut_dir):
    rebuild_dir, mut_dir = pathlib.Path(rebuild_dir), pathlib.Path(mut_dir)
    res = []
    for mid, unit, mod, thm, old, new, ml in MUTS:
        src = rebuild_dir / unit
        r0 = json.loads((src / 'RESULT.json').read_text())
        if not r0['green']:
            res.append(dict(id=mid, unit=unit, skipped='unit not green'))
            continue
        w = mut_dir / f'{mid}-{unit}'
        if w.exists():
            shutil.rmtree(w)
        shutil.copytree(src, w)
        f = w / (mod + '.lean')
        txt = f.read_text()
        n = txt.count(old)
        if n != 1:
            res.append(dict(id=mid, unit=unit, error=f'pattern count {n}'))
            continue
        f.write_text(txt.replace(old, new))
        (w / (mod + '.olean')).unlink(missing_ok=True)
        lp = '.'
        if ml:
            lp = ':'.join(['.'] + [f'{ML}/{p}/.lake/build/lib/lean' for p in ML_PKGS])
        cmd = ['systemd-run', '--user', '--wait', '--pipe', '--quiet',
               f'--unit=mutate-{mid.lower()}-{int(time.time())}',
               '-p', 'MemoryMax=2G', '-p', 'MemorySwapMax=0', '-p', 'RuntimeMaxSec=120',
               '-p', f'WorkingDirectory={w}', '--setenv', f'LEAN_PATH={lp}',
               LEAN, '-j1', '-M1800', '-o', mod + '.olean', mod + '.lean']
        p = subprocess.run(cmd, capture_output=True, text=True)
        log = p.stdout + p.stderr
        (w / 'mutation.log').write_text(log)
        errs = [x for x in log.splitlines() if 'error' in x][:3]
        res.append(dict(id=mid, unit=unit, theorem=thm, old=old, new=new, rc=p.returncode,
                        killed=(p.returncode != 0 and bool(errs)), errors=errs))
        print(mid, unit, thm, 'rc', p.returncode, 'KILLED' if res[-1]['killed'] else 'SURVIVED', errs[:1], flush=True)
    (mut_dir / 'mutations.json').write_text(json.dumps(res, indent=1, ensure_ascii=False))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
