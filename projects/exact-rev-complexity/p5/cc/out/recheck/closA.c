/* Method A: closure over joint states (beta, D1[chain L], D2[forest]).
   usage: closA mode l1 l2 ... lm
   mode 0: checks; prints state count and violation counts per map.
   Forest S2: chains l1..lm laid out consecutively: chain c occupies bits off_c..off_c+l_c-1,
   bit off_c+i = position i in chain c (position 0 = top). S1: single chain of length L.
   Maps (X in S2 with all tops pebbled): 0=sort ascending (phi_sort), 1=sort descending, 2=identity(concatenate).
   Also dumps fingerprints of states with depth<=DMAX to file if env DUMP set. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint16_t u16;
#define INF 0xFFFF
static int L, N, m, len[32], off[32];
static int req1[32], req2[32];
static int pc(int x){return __builtin_popcount(x);}
static int *qx, *qv, *sx; static unsigned char *fin;
static int cmpv_D; static u16 *cmpD;
static int cmps(const void*a,const void*b){int x=*(int*)a,y=*(int*)b;return (int)cmpD[x]-(int)cmpD[y];}
static void closure(u16 *D, int beta, int *req){
  int ns=0;
  for(int x=0;x<N;x++){ if(pc(x)>beta) D[x]=INF; else if(D[x]!=INF) sx[ns++]=x; fin[x]=0; }
  cmpD=D; qsort(sx,ns,sizeof(int),cmps);
  int si=0,qh=0,qt=0;
  while(si<ns||qh<qt){
    int x,v;
    if(qh<qt && (si>=ns || qv[qh] < D[sx[si]] )){x=qx[qh];v=qv[qh];qh++;}
    else {x=sx[si];v=D[x];si++;}
    if(fin[x]) continue;
    if(D[x]<v) continue;
    fin[x]=1;
    for(int b=0;b<L;b++){
      if(req[b]>=0 && !((x>>req[b])&1)) continue;
      int y=x^(1<<b); if(pc(y)>beta) continue;
      if(D[y]==INF || D[y]>v+1){ D[y]=v+1; qx[qt]=y; qv[qt]=v+1; qt++; }
    }
  }
}
/* state storage */
static size_t SS; /* u16 per state: 1 + 2N */
static u16 *st=NULL; static size_t nst=0, cap=0; static int *depth=NULL, *par=NULL;
static size_t hcap; static int64_t *ht;
static uint64_t fp(const u16 *s){ uint64_t h=1469598103934665603ULL; const unsigned char*p=(const unsigned char*)s; for(size_t i=0;i<SS*2;i++){h^=p[i];h*=1099511628211ULL;} return h;}
static int64_t lookup_insert(const u16 *s, int d, int parent, int *isnew){
  uint64_t h=fp(s); size_t i=h&(hcap-1);
  while(ht[i]>=0){ if(memcmp(st+ (size_t)ht[i]*SS, s, SS*2)==0){*isnew=0;return ht[i];} i=(i+1)&(hcap-1);}
  if(nst==cap){cap=cap?cap*2:1024; st=realloc(st,cap*SS*2); depth=realloc(depth,cap*sizeof(int)); par=realloc(par,cap*sizeof(int)); if(!st){fprintf(stderr,"OOM\n");exit(3);} }
  memcpy(st+nst*SS,s,SS*2); depth[nst]=d; par[nst]=parent; ht[i]=nst; *isnew=1; nst++;
  if(nst*2>hcap){ /* rehash */ size_t nc=hcap*2; int64_t*nh=malloc(nc*8); for(size_t k=0;k<nc;k++)nh[k]=-1;
    for(size_t k=0;k<nst;k++){uint64_t hh=fp(st+k*SS); size_t j=hh&(nc-1); while(nh[j]>=0)j=(j+1)&(nc-1); nh[j]=k;}
    free(ht); ht=nh; hcap=nc; }
  return nst-1;
}
/* checks */
#define NMAP 3
static int nchk; static int *chkx; static int chky[NMAP][1<<16];
static int vio[NMAP][1<<16]; static int vwit[NMAP][1<<16];
static void build_maps(void){
  nchk=0; chkx=malloc(sizeof(int)*N);
  for(int x=0;x<N;x++){
    int ok=1; for(int c=0;c<m;c++) if(!((x>>off[c])&1)) ok=0;
    if(!ok) continue;
    int iv[32], ni=0;
    for(int c=0;c<m;c++){ int last=-1;
      for(int i=0;i<len[c];i++) if((x>>(off[c]+i))&1){ if(last>=0) iv[ni++]=i-last; last=i; }
      iv[ni++]=len[c]-last; }
    int asc[32],dsc[32]; memcpy(asc,iv,sizeof(int)*ni);
    for(int i=0;i<ni;i++)for(int j=i+1;j<ni;j++) if(asc[j]<asc[i]){int t=asc[i];asc[i]=asc[j];asc[j]=t;}
    for(int i=0;i<ni;i++) dsc[i]=asc[ni-1-i];
    int ya=0,yd=0,p=0; for(int i=0;i<ni;i++){ya|=1<<p;p+=asc[i];} if(p!=L){fprintf(stderr,"sum err\n");exit(4);}
    p=0; for(int i=0;i<ni;i++){yd|=1<<p;p+=dsc[i];}
    chkx[nchk]=x; chky[0][nchk]=ya; chky[1][nchk]=yd; chky[2][nchk]=x; nchk++;
  }
}
int main(int argc,char**argv){
  m=argc-1; L=0; for(int c=0;c<m;c++){len[c]=atoi(argv[c+1]); off[c]=L; L+=len[c];}
  N=1<<L; SS=1+2*(size_t)N;
  for(int i=0;i<L;i++) req1[i]= (i<L-1)? i+1 : -1;
  for(int c=0;c<m;c++) for(int i=0;i<len[c];i++) req2[off[c]+i]= (i<len[c]-1)? off[c]+i+1 : -1;
  qx=malloc(sizeof(int)*N*(L+2)); qv=malloc(sizeof(int)*N*(L+2)); sx=malloc(sizeof(int)*N); fin=malloc(N);
  hcap=1<<16; ht=malloc(hcap*8); for(size_t k=0;k<hcap;k++)ht[k]=-1;
  build_maps();
  u16 *s=malloc(SS*2);
  for(int b0=0;b0<=L;b0++){
    s[0]=b0; for(int x=0;x<N;x++){s[1+x]=INF; s[1+N+x]=INF;} s[1]=0; s[1+N]=0;
    closure(s+1,b0,req1); closure(s+1+N,b0,req2);
    int nw; lookup_insert(s,0,-1,&nw);
  }
  int maxval=0;
  for(size_t k=0;k<nst;k++){
    /* checks on state k */
    u16 *cur=st+k*SS; u16 *D1=cur+1,*D2=cur+1+N;
    for(int x=0;x<N;x++){ if(D1[x]!=INF&&D1[x]>maxval)maxval=D1[x]; if(D2[x]!=INF&&D2[x]>maxval)maxval=D2[x]; }
    for(int mp=0;mp<NMAP;mp++) for(int i=0;i<nchk;i++){
      if(D1[chky[mp][i]] > D2[chkx[i]] && !vio[mp][i]){vio[mp][i]=1; vwit[mp][i]=k;}
    }
    int beta=cur[0];
    for(int d=-1;d<=1;d+=2){ int nb=beta+d; if(nb<0||nb>L) continue;
      cur=st+k*SS; memcpy(s,cur,SS*2); s[0]=nb;
      closure(s+1,nb,req1); closure(s+1+N,nb,req2);
      int nw; lookup_insert(s,depth[k]+1,k,&nw);
    }
  }
  int nv[NMAP]={0}; for(int mp=0;mp<NMAP;mp++) for(int i=0;i<nchk;i++) nv[mp]+=vio[mp][i];
  int maxd=0; for(size_t k=0;k<nst;k++) if(depth[k]>maxd)maxd=depth[k];
  printf("lens");for(int c=0;c<m;c++)printf(" %d",len[c]);
  printf(" L=%d states=%zu maxdepth=%d maxval=%d nX=%d viol_asc=%d viol_desc=%d viol_id=%d\n",L,nst,maxd,maxval,nchk,nv[0],nv[1],nv[2]);
  /* witness walks */
  char *W=getenv("WIT");
  if(W){ FILE*f=fopen(W,"a");
    for(int mp=0;mp<NMAP;mp++){ int cnt=0; for(int i=0;i<nchk&&cnt<3;i++) if(vio[mp][i]){ cnt++;
      int k=vwit[mp][i]; int bs[4096],nb=0; while(k>=0){bs[nb++]=st[(size_t)k*SS]; k=par[k];}
      fprintf(f,"map=%d lens",mp); for(int c=0;c<m;c++)fprintf(f," %d",len[c]);
      fprintf(f," X=%d Y=%d walk",chkx[i],chky[mp][i]); for(int j=nb-1;j>=0;j--)fprintf(f," %d",bs[j]); fprintf(f,"\n"); }}
    fclose(f);}
  char *P=getenv("DUMP"); int dmax=getenv("DMAX")?atoi(getenv("DMAX")):13;
  if(P){ FILE*f=fopen(P,"w"); for(size_t k=0;k<nst;k++) if(depth[k]<=dmax) fprintf(f,"%016llx\n",(unsigned long long)fp(st+k*SS)); fclose(f);}
  return 0;
}
