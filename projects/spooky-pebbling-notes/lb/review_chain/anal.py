# analytic lower bound: fixed-level cut at depth L=ceil(log2(b*h)), phi(k)=q(1-2^-(k-L)+phi(k-L)), q=1-b/2^L
import math
for h in [8,16,32,64,128,512,4096,2**16]:
    b=h-2; L=max(2,math.ceil(math.log2(b*h))); q=1-b/2**L
    phi={}
    def f(k):
        if k<=L: return 0.0
        return q*(1-2.0**(-(k-L))+f(k-L))
    val=f(h)
    print(h,L,round(val,3),"ratio to h/log2h:",round(val/(h/math.log2(h)),3))
