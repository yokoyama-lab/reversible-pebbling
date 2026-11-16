import os, re, subprocess, sys, json, time, hashlib
B = sys.argv[1]; LEAN = sys.argv[2]; out = sys.argv[3]
mods = {f[:-5] for f in os.listdir(B) if f.endswith('.lean')}
deps = {}
for m in mods:
    imps = re.findall(r'^import\s+(\S+)', open(f'{B}/{m}.lean').read(), re.M)
    deps[m] = [i for i in imps if i in mods]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps[m]: visit(d)
    order.append(m)
for m in sorted(mods): visit(m)
res = {}
import ast
SKIP=set(os.environ.get('SKIP','').split(','))
prev={}
if os.environ.get('PREV'):
    for l in open(os.environ['PREV']):
        k,_,v=l.partition(' ')
        try: prev[k]=ast.literal_eval(v.strip())
        except Exception: pass
for m in order:
    if any(res.get(d, {}).get('rc') != 0 for d in deps[m]):
        res[m] = {'rc': None, 'skip': 'dep failed'}; continue
    if m in SKIP:
        res[m]={'rc':None,'skip':'skipped (known source-side timeout)'}; print(m,res[m],flush=True); continue
    if prev.get(m,{}).get('rc')==0 and os.path.exists(f'{B}/{m}.olean'):
        res[m]=dict(prev[m],reused=True); print(m,res[m],flush=True); continue
    t = time.time()
    cmd = ['systemd-run', '--user', '--wait', '--pipe', '--quiet', '-p', 'MemoryMax=2G', '-p', 'RuntimeMaxSec=120',
           '-p', 'Nice=19', '--working-directory', B, '--setenv', f'LEAN_PATH={B}', LEAN, '-j1', '-o', f'{m}.olean', f'{m}.lean']
    p = subprocess.run(cmd, capture_output=True, text=True)
    log = p.stdout + p.stderr
    open(f'{B}/{m}.buildlog', 'w').write(log)
    ok = p.returncode == 0 and os.path.exists(f'{B}/{m}.olean')
    res[m] = {'rc': p.returncode, 'olean': os.path.exists(f'{B}/{m}.olean'), 'sec': round(time.time()-t, 1),
              'errors': log.count('error'), 'sorry': ('declaration uses \'sorry\'' in log)}
    print(m, res[m], flush=True)
json.dump({'order': order, 'res': res}, open(out, 'w'), indent=1)
