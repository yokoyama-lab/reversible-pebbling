import pathlib,datetime,subprocess,resource,math,json,os,sys
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
cg=pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1]
root=pathlib.Path('/sys/fs/cgroup'+cg)
assert (root/'memory.max').read_text().strip()=='2147483648'
assert (root/'memory.swap.max').read_text().strip()=='0'
print('CGROUP',cg,'memory.max=2147483648 memory.swap.max=0',flush=True)
print('SETUP_PASS',flush=True)
os.environ['LEAN_PATH']='.'
steps=[]
for name in ['ExtensionBefore','CompletionFromExtension']:
 used=resource.getrusage(resource.RUSAGE_CHILDREN)
 rem=29-math.ceil(used.ru_utime+used.ru_stime)
 if rem<1:sys.exit(124)
 def limit():resource.setrlimit(resource.RLIMIT_CPU,(rem,rem))
 start=now()
 print('COMPUTE_ENTRY',name,start,'CPU_LIMIT',rem,flush=True)
 r=subprocess.run(['<home>/.elan/toolchains/leanprover--lean4---v4.31.0/bin/lean','-j1','-M1800','-o',name+'.olean',name+'.lean'],preexec_fn=limit)
 steps.append(dict(module=name,start=start,stop=now(),rc=r.returncode))
 tmp=pathlib.Path('STEPS.json.tmp');tmp.write_text(json.dumps(steps,indent=2));tmp.rename('STEPS.json')
 print('STEP_STOP',steps[-1],flush=True)
 if r.returncode:sys.exit(r.returncode)
