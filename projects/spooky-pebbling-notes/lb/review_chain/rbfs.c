// reverse BFS: dist-to-goal for spooky pebble game on T_h (h=4), p pebbles. state base-3 digits: 0 empty,1 peb,2 ghost
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  int h=atoi(argv[1]), p=atoi(argv[2]); int n=(1<<h)-1;
  long N=1; for(int i=0;i<n;i++) N*=3;
  long pw[32]; pw[0]=1; for(int i=1;i<=n;i++) pw[i]=pw[i-1]*3;
  int16_t *d=malloc(N*sizeof(int16_t)); for(long i=0;i<N;i++) d[i]=-1;
  int32_t *q=malloc(N*sizeof(int32_t)); long qh=0,qt=0;
  long goal=pw[0]; d[goal]=0; q[qt++]=goal;
  int dig[32];
  while(qh<qt){ long s=q[qh++]; long x=s; int cnt=0;
    for(int i=0;i<n;i++){dig[i]=x%3;x/=3; if(dig[i]==1)cnt++;}
    for(int v=0;v<n;v++){
      int cs=1; for(int c=2*v+1;c<=2*v+2;c++) if(c<n && dig[c]!=1) cs=0;
      long sp=-1;
      // candidate predecessors s' -> s via move on v
      if(dig[v]==1){ // pebble from empty (cs), unghost from ghost (cs); s count<=p already
        if(cs){ long a=s-pw[v]; if(d[a]<0){d[a]=d[s]+1;q[qt++]=a;}
                long b=s+pw[v]; if(d[b]<0){d[b]=d[s]+1;q[qt++]=b;} }
      } else if(dig[v]==0){ // unpebble from peb: need cs, s' count = cnt+1 <=p
        if(cs && cnt+1<=p){ long a=s+pw[v]; if(d[a]<0){d[a]=d[s]+1;q[qt++]=a;} }
      } else { // ghost from peb, s' count cnt+1<=p
        if(cnt+1<=p){ long a=s-pw[v]; if(d[a]<0){d[a]=d[s]+1;q[qt++]=a;} }
      }
      (void)sp;
    }
  }
  fprintf(stderr,"reached %ld, d(start)=%d\n",qt,d[0]);
  FILE*f=fopen(argv[3],"wb"); fwrite(d,sizeof(int16_t),N,f); fclose(f);
}
