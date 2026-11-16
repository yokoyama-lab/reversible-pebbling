#!/usr/bin/env python3
"""Write and compile axiom-check files for the v15-claimed theorems over the
rebuilt closure in <work>. Fully qualified names are derived from the
namespace/section stack at the theorem's line."""
import json
import pathlib
import re
import subprocess
import sys
import time

LEAN = '<home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean'
# group -> list of (module, theorem short name)
GROUPS = {
 'AxMain': [
  ('PricedRecurrence', 'C_affine'), ('PhysicalExactOptimum', 'exact_optimum'),
  ('FamilyAllOptimal', 'every_family_word'), ('ActualCheckpoint', 'actual_checkpoint_board'),
  ('FullSlotAssembly', 'labelled_legal_iff_blocked'), ('WholeBijection', 'local_roundtrip'),
  ('WholeBijection', 'physical_roundtrip'), ('PhysicalCount', 'exact_physical_word_count'),
  ('LabelledCount', 'exact_labelled_word_count'), ('PhysicalCover', 'exact_physical_cover'),
  ('RawComponentCount', 'exact_components'), ('PhysicalComponentCount', 'exact_components'),
  ('RawSwapLift', 'reach_iff_decode'), ('ComponentWordCount', 'exact_component_word_count'),
  ('SignaturePhysicalExact', 'exact_component_cover'), ('SignatureExact', 'count_formula'),
  ('FinitePartialDFA', 'partial_upper_with_initial'), ('FinitePartialDFA', 'partial_lower'),
  ('FiniteAlphabetDFA', 'complete_lower'), ('PhysicalAutomataExact', 'complete_lower'),
  ('FinitePartialEdges', 'finite_edge_count'), ('ComponentExact', 'component_556_cover_exact'),
  ('ComponentExact', 'component_28_cover_exact'), ('Multiplicity', 'raw_exact_multiplicity'),
  ('PrecedenceCover', 'physical_precedence_upper'), ('PrecedenceGuard', 'physical_run_filter'),
  ('RationalObstruction', 'I_normalized_rational_obstruction'),
  ('RationalObstruction', 'M_normalized_rational_obstruction')],
 'AxResidual': [('Physical', 'initial_exact'), ('Physical', 'middle_exact'),
                ('Physical', 'initial_nodup'), ('Physical', 'middle_nodup')],
 'AxRecurrence': [('Recurrence', 'count_exact'), ('Recurrence', 'zero_iff_no_completion'),
                  ('Recurrence', 'count_distinct')],
 'AxRemaining': [('RemainingPerm', 'count_remaining_perm'), ('RemainingPerm', 'completions_remaining_perm')],
 'AxBoard': [('BoardPerm', 'count_remaining_perm'), ('BoardPerm', 'completions_remaining_perm')],
}


def fqn(path, thm):
    stack = []
    for line in path.read_text(errors='replace').splitlines():
        m = re.match(r'\s*(namespace|section)\s*(\S*)', line)
        if m:
            stack.append((m.group(1), m.group(2)))
            continue
        m = re.match(r'\s*end\b\s*(\S*)', line)
        if m and stack:
            stack.pop()
            continue
        if re.match(r'\s*(private\s+)?theorem\s+' + re.escape(thm) + r'\b', line):
            ns = [n for k, n in stack if k == 'namespace' and n]
            return '.'.join(ns + [thm])
    return None


def main(work):
    work = pathlib.Path(work)
    out = {}
    for g, items in GROUPS.items():
        skipped = [(m, t) for m, t in items if not (work / (m + '.olean')).exists()]
        items = [(m, t) for m, t in items if (work / (m + '.olean')).exists()]
        if not items:
            out[g] = dict(skipped=skipped)
            print(g, 'all skipped', flush=True)
            continue
        mods = sorted({m for m, _ in items})
        names = []
        for m, t in items:
            n = fqn(work / (m + '.lean'), t)
            names.append(n or f'?{m}.{t}')
        src = ''.join(f'import {m}\n' for m in mods) + ''.join(f'#print axioms {n}\n' for n in names)
        (work / (g + '.lean')).write_text(src)
        cmd = ['systemd-run', '--user', '--wait', '--pipe', '--quiet', f'--unit=ax12-{g.lower()}-{int(time.time())}',
               '-p', 'MemoryMax=2G', '-p', 'MemorySwapMax=0', '-p', 'RuntimeMaxSec=120',
               '-p', f'WorkingDirectory={work}', '--setenv', 'LEAN_PATH=.', LEAN, '-j1', '-M1800', g + '.lean']
        p = subprocess.run(cmd, capture_output=True, text=True)
        log = p.stdout + p.stderr
        (work / (g + '.log')).write_text(log)
        ax = {}
        for mm in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log, re.S):
            ax[mm.group(1)] = [a.strip() for a in (mm.group(3) or '').replace('\n', ' ').split(',') if a.strip()]
        out[g] = dict(rc=p.returncode, names=names, axioms=ax, skipped=skipped,
                      errors=[x for x in log.splitlines() if 'error' in x][:5])
        print(g, p.returncode, len(ax), '/', len(names), out[g]['errors'][:2], flush=True)
    (work / 'AXCHECK.json').write_text(json.dumps(out, indent=1))


if __name__ == '__main__':
    main(sys.argv[1])
