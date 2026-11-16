/* Method B: enumerate all walks with T phases (beta_0..beta_{T-1}), every start beta_0 in 0..L.
   For each walk, build the layered graph (phase i, board X) explicitly and run a 0-1 BFS (deque)
   from (0, empty). Edges: (i,X)->(i,Y) cost 1 for a legal toggle with |Y|<=beta_i;
   (i,X)->(i+1,X) cost 0 if |X|<=beta_{i+1}. R at prefix i = dist(i,X).
   Separate implementation of the rules: legality via explicit chain/position tables.
   usage: walkB T l1 ... lm ; prints violation counts per map over all walk prefixes,
   and dumps fingerprints of distinct (beta, D1, D2) per layer if DUMP set. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint16_t u16;
#define INF 0xFFFF
int L,N,m,len[16],chainof[32],posof[32],start[16];
int T;
int legal(int forest,int x,int v){ /* may toggle v in board x? */
  if(!forest){ if(v==L-1) return 1; return (x>>(v+1))&1; }
  int c=chainof[v],p=posof[v]; if(p==len[c]-1) return 1; return (x>>(start[c]+p+1))&1;
}
int pcnt(int x){int c=0;while(x){c+=x&1;x>>=1;}return c;}
u16 *dist; int *dq; 
void solve(int forest,int *beta,u16 *out /* T*N */){
  int tot=T*N; for(int i=0;i<tot;i++) dist[i]=INF;
  /* deque of node ids, size 2*tot*(L+1) circular */
  int cap=4*tot*(L+2); int h=cap/2,t=cap/2;
  dist[0]=0; dq[t++]=0;
  while(h<t){ int u=dq[h++]; int i=u/N,x=u%N; int du=dist[u];
    /* stale check impossible to know w/o value; store pairs instead: recompute */
    for(int v=0;v<L;v++){ if(!legal(forest,x,v)) continue; int y=x^(1<<v); if(pcnt(y)>beta[i]) continue;
      int w=i*N+y; if(dist[w]>du+1){dist[w]=du+1; dq[t++]=w;} }
    if(i+1<T && pcnt(x)<=beta[i+1]){ int w=(i+1)*N+x; if(dist[w]>du){dist[w]=du; dq[--h]=w;} }
  }
  memcpy(out,dist,sizeof(u16)*tot);
}
/* maps */
int nchk,chkx[1<<14],chky[3][1<<14],vio[3][1<<14];
int cmpi(const void*a,const void*b){return *(int*)a-*(int*)b;}
void maps(void){
  for(int x=0;x<N;x++){ int ok=1; for(int c=0;c<m;c++) if(!((x>>start[c])&1)) ok=0; if(!ok)continue;
    int iv[32],ni=0;
    for(int c=0;c<m;c++){ int p=0; while(p<len[c]){ int q=p+1; while(q<len[c] && !((x>>(start[c]+q))&1)) q++; iv[ni++]=q-p; p=q; } }
    qsort(iv,ni,sizeof(int),cmpi);
    int ya=0,yd=0,s=0; for(int i=0;i<ni;i++){ya|=1<<s;s+=iv[i];} s=0; for(int i=ni-1;i>=0;i--){yd|=1<<s;s+=iv[i];}
    chkx[nchk]=x; chky[0][nchk]=ya; chky[1][nchk]=yd; chky[2][nchk]=x; nchk++; }
}
uint64_t fp(const u16 *s,size_t n){ uint64_t h=1469598103934665603ULL; const unsigned char*p=(const unsigned char*)s; for(size_t i=0;i<n*2;i++){h^=p[i];h*=1099511628211ULL;} return h;}
int main(int argc,char**argv){
  T=atoi(argv[1]); m=argc-2; L=0;
  for(int c=0;c<m;c++){len[c]=atoi(argv[c+2]); start[c]=L; for(int p=0;p<len[c];p++){chainof[L+p]=c;posof[L+p]=p;} L+=len[c];}
  N=1<<L; maps();
  dist=malloc(sizeof(u16)*T*N); dq=malloc(sizeof(int)*4*T*N*(L+2));
  u16 *o1=malloc(sizeof(u16)*T*N),*o2=malloc(sizeof(u16)*T*N), *buf=malloc(sizeof(u16)*(1+2*N));
  FILE*f=getenv("DUMP")?fopen(getenv("DUMP"),"w"):NULL;
  int beta[64]; long nwalk=0;
  for(int b0=0;b0<=L;b0++){
    for(long code=0;code<(1L<<(T-1));code++){
      beta[0]=b0; int ok=1; for(int i=1;i<T;i++){beta[i]=beta[i-1]+(((code>>(i-1))&1)?1:-1); if(beta[i]<0||beta[i]>L){ok=0;break;}}
      if(!ok) continue; nwalk++;
      solve(0,beta,o1); solve(1,beta,o2);
      for(int i=0;i<T;i++){ u16*D1=o1+i*N,*D2=o2+i*N;
        for(int mp=0;mp<3;mp++) for(int k=0;k<nchk;k++) if(D1[chky[mp][k]]>D2[chkx[k]]) vio[mp][k]=1;
        if(f){ buf[0]=beta[i]; memcpy(buf+1,D1,N*2); memcpy(buf+1+N,D2,N*2); fprintf(f,"%016llx\n",(unsigned long long)fp(buf,1+2*N)); }
      }
    }
  }
  if(f)fclose(f);
  int nv[3]={0}; for(int mp=0;mp<3;mp++)for(int k=0;k<nchk;k++)nv[mp]+=vio[mp][k];
  printf("B T=%d lens",T); for(int c=0;c<m;c++)printf(" %d",len[c]);
  printf(" L=%d walks=%ld nX=%d viol_asc=%d viol_desc=%d viol_id=%d\n",L,nwalk,nchk,nv[0],nv[1],nv[2]);
  return 0;
}
