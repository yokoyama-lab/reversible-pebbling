import pathlib,datetime,json,subprocess,time,os
p=pathlib.Path('<local>/paper-audits/PEBBLING-CAPACITY-EDGE-I-20261115-A1')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,d):
 t=p/(n+'.tmp');t.write_text(json.dumps(d,indent=2));t.rename(p/n)
fd=os.open(p/'once.lock',os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600);os.close(fd)
payload='''set -eu
cg=$(cut -d: -f3 /proc/self/cgroup)
cat /proc/self/cgroup
m=$(cat /sys/fs/cgroup$cg/memory.max); s=$(cat /sys/fs/cgroup$cg/memory.swap.max)
echo memory.max=$m memory.swap.max=$s
[ "$m" = 2147483648 ] && [ "$s" = 0 ]
echo SETUP_PASS
printf 'COMPUTE_ENTRY '; date -u +%FT%T.%NZ
export LEAN_PATH=.
exec <home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean -j1 -M1800 -o CapacityCommonEdgeI.olean CapacityCommonEdgeI.lean'''
cmd=['systemd-run','--user','--wait','--pipe','--unit=pebbling-capacity-edge-i-20261115-a1','-p','MemoryMax=2147483648','-p','MemorySwapMax=0','-p','RuntimeMaxSec=60','-p','LimitCPU=30','-p','WorkingDirectory='+str(p),'/bin/bash','-c',payload]
save('START.json',{'manager_launch':now(),'command':cmd,'evaluation':'C; limited arithmetic preparation'})
s=time.monotonic();rc=None;error=None
try:
 with (p/'lean.log').open('w') as f:rc=subprocess.run(cmd,env={**os.environ,'XDG_RUNTIME_DIR':'/run/user/1000'},stdout=f,stderr=subprocess.STDOUT).returncode
except BaseException as e:error=repr(e);raise
finally:
 log=(p/'lean.log').read_text() if (p/'lean.log').exists() else ''
 save('STOP.json',{'observed_stop':now(),'rc':rc,'error':error,'elapsed':time.monotonic()-s,'setup_pass':'SETUP_PASS' in log,'compute_entry':'COMPUTE_ENTRY' in log,'olean_exists':(p/'CapacityCommonEdgeI.olean').exists(),'collection':'pending; OOM cause not inferred from rc alone'})
print((p/'STOP.json').read_text());print((p/'lean.log').read_text())
