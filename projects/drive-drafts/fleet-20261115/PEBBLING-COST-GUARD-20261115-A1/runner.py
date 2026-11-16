import pathlib,datetime,json,subprocess,time,os
p=pathlib.Path('<local>/paper-audits/PEBBLING-COST-GUARD-20261115-A1')
def save(n,d):
 t=p/(n+'.tmp');t.write_text(json.dumps(d,indent=2));t.rename(p/n)
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
assert not (p/'START.json').exists()
cmd=['systemd-run','--user','--wait','--pipe','--unit=pebbling-cost-guard-20261115-a1','-p','MemoryMax=2147483648','-p','MemorySwapMax=0','-p','RuntimeMaxSec=60','-p','LimitCPU=30','-p','WorkingDirectory='+str(p),'/bin/bash','-c','date -u +%FT%T.%NZ; cat /proc/self/cgroup; for f in memory.max memory.swap.max; do cat /sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/$f; done; exec <home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean -j1 -M1800 -o CostGuard.olean CostGuard-20261115.lean']
save('START.json',{'observed_launch':now(),'command':cmd,'note':'manager launch is not yet proof of Lean START; see log'})
s=time.monotonic()
with (p/'lean.log').open('w') as f:
 r=subprocess.run(cmd,env={**os.environ,'XDG_RUNTIME_DIR':'/run/user/1000'},stdout=f,stderr=subprocess.STDOUT)
save('STOP.json',{'observed_stop':now(),'rc':r.returncode,'elapsed':time.monotonic()-s,'olean_exists':(p/'CostGuard.olean').exists()})
print((p/'STOP.json').read_text());print((p/'lean.log').read_text())
