import sys
def comps(n):
    if n==0: yield []; return
    for k in range(1,n+1):
        for r in comps(n-k): yield [k]+r
lo,hi=int(sys.argv[1]),int(sys.argv[2])
for L in range(lo,hi+1):
    for c in comps(L): print(' '.join(map(str,c)))
