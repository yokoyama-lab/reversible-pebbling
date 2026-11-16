import sys
sys.path.insert(0,'<local>/dev/notes/spooky-pebbling/lb/critic3')
from common import load, replay_ql
def epis(mv, n):
    anc=[]
    for v in range(n):
        a,x=[],v
        while True:
            a.append(x)
            if x==0: break
            x=(x-1)//2
        anc.append(a)
    st=[0]*n; cnt=[0]*n; emptied=[True]*n; E=[0]*n; P=[0]*n; eps=[[] for _ in range(n)]
    for t,(op,v) in enumerate(mv, start=1):
        new=1 if op in('pebble','unghost') else (2 if op=='ghost' else 0); old=st[v]
        if new==1:
            P[v]+=1
            if emptied[v]: E[v]+=1; eps[v].append(t)
            emptied[v]=False
        st[v]=new
        d=(new==1)-(old==1)
        for a in anc[v]:
            cnt[a]+=d
            if cnt[a]==0: emptied[a]=True
    return E,P,eps
if __name__=='__main__':
  for path,h,cap in [(sys.argv[i],int(sys.argv[i+1]),int(sys.argv[i+2])) for i in range(1,len(sys.argv),3)]:
      mv=load(path); replay_ql(mv,h,cap); n=2**h-1
      E,P,eps=epis(mv,n)
      print(path.split('/')[-1], 'len',len(mv))
      for d in range(h):
          vs=range(2**d-1,2**(d+1)-1)
          print(f" depth {d} (height {h-d}): E=",[E[v] for v in vs]," X'=",[E[v]-E[(v-1)//2] if v else '-' for v in vs], " places-E=",[P[v]-E[v] for v in vs])
      w=[sum((E[a]-E[(a-1)//2])*(2**(h-((a+1).bit_length()-1))-1) for a in range(1,n) if h-((a+1).bit_length()-1)==k) for k in range(1,h)]
      print(" w_k (height 1..h-1):",w)
