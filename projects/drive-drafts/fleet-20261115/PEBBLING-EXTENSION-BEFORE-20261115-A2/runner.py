import pathlib,datetime,json,subprocess,time,os
p=pathlib.Path('<local>/paper-audits/PEBBLING-EXTENSION-BEFORE-20261115-A2')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,d):
 t=p/(n+'.tmp');t.write_text(json.dumps(d,indent=2));t.rename(p/n)
fd=os.open(p/'once.lock',os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600);os.close(fd)
payload='exec python3 payload.py'
cmd=['systemd-run','--user','--wait','--pipe','--unit=pebbling-extension-before-20261115-a2','-p','MemoryMax=2147483648','-p','MemorySwapMax=0','-p','RuntimeMaxSec=60','-p','LimitCPU=30','-p','WorkingDirectory='+str(p),'/bin/bash','-c',payload]
save('START.json',{'manager_launch':now(),'command':cmd,'evaluation':'C; limited arithmetic preparation'})
s=time.monotonic();rc=None;error=None
try:
 with (p/'lean.log').open('w') as f:rc=subprocess.run(cmd,env={**os.environ,'XDG_RUNTIME_DIR':'/run/user/1000'},stdout=f,stderr=subprocess.STDOUT).returncode
except BaseException as e:error=repr(e);raise
finally:
 log=(p/'lean.log').read_text() if (p/'lean.log').exists() else ''
 save('STOP.json',{'observed_stop':now(),'rc':rc,'error':error,'elapsed':time.monotonic()-s,'setup_pass':'SETUP_PASS' in log,'compute_entry':'COMPUTE_ENTRY' in log,'olean_exists':(p/'CompletionFromExtension.olean').exists(),'collection':'pending; OOM cause not inferred from rc alone'})
print((p/'STOP.json').read_text());print((p/'lean.log').read_text())
