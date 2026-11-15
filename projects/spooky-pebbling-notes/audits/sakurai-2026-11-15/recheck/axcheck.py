import os, re, subprocess, sys, json
B, LEAN, res_json, out = sys.argv[1:5]
R = json.load(open(res_json))['res']
mods = [m for m in R if R[m].get('rc') == 0]
deps = {m: [i for i in re.findall(r'^import\s+(\S+)', open(f'{B}/{m}.lean').read(), re.M) if i in R] for m in R}
imported = {d for m in mods for d in deps[m]}
leaves = [m for m in mods if m not in imported]
def closure(m, acc):
    if m in acc: return acc
    acc.add(m)
    for d in deps[m]: closure(d, acc)
    return acc
results = {}
for leaf in sorted(leaves):
    cl = sorted(closure(leaf, set()))
    src = 'import Lean\nimport ' + leaf + '\nopen Lean Elab Command\n'
    src += '#eval show CommandElabM Unit from do\n  let env ← getEnv\n'
    src += '  let mods : Array Name := #[' + ','.join('`'+m for m in cl) + ']\n'
    src += '''  let idxs := mods.filterMap (fun m => env.getModuleIdx? m)
  let mut cnt := 0
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | some i =>
      if idxs.contains i then
        if let .thmInfo _ := ci then
          cnt := cnt + 1
          let axs ← collectAxioms n
          let ns := axs.filter (fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound))
          if ns.size > 0 then bad := bad.push s!"{n} :: {ns}"
    | none => pure ()
  IO.println s!"AXCHECK theorems={cnt} modules={idxs.size} nonstandard={bad.size}"
  for b in bad do IO.println s!"NONSTD {b}"
'''
    f = f'{B}/AxCheck_{leaf}.lean'
    open(f, 'w').write(src)
    p = subprocess.run(['systemd-run','--user','--wait','--pipe','--quiet','-p','MemoryMax=2G','-p','RuntimeMaxSec=120','-p','Nice=19',
        '--working-directory',B,'--setenv',f'LEAN_PATH={B}',LEAN,'-j1',f], capture_output=True, text=True)
    o = p.stdout + p.stderr
    results[leaf] = {'rc': p.returncode, 'closure': cl, 'out': o[-6000:]}
    print(leaf, p.returncode, [l for l in o.splitlines() if l.startswith('AXCHECK')], sum(1 for l in o.splitlines() if l.startswith('NONSTD')), flush=True)
json.dump(results, open(out,'w'), indent=1)
