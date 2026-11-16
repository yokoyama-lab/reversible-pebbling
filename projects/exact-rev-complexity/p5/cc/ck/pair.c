/* 2CM_2 規則版の各列で: 間の予算が最小の相 r（すべて）で森の最適解を切った盤 Z（A^森+B^森 = OPT^森 となる Z すべて）について，
   1 本の盤 Y で A^1本(Y) ≤ A^森(Z) かつ B^1本(Y) ≤ B^森(Z) となるものがあるか．
   出力: 列の数，「ある最適な (r,Z) で Y あり」の列，「どの最適な (r,Z) にも Y なし」の列（例）．使い方: pair LEGS JMAX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define INF 1000000
static int L,N,nc,len[8],st[8],needF[16],needM[16],topsF,pc[1<<16],JMAX;
static void closure(int *d,const int *need,int b){ int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF) continue;
  for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>b) continue; if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } } }
static void A(int *d,const int *need,int req,const int *w,int J,int p){
  for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){ if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if(k==p && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF; closure(d,need,w[k]); } }
static int w[32]; static long rows=0,okall=0,oksome=0,failall=0,failsome=0;
static int *aF,*aM,*bF,*bM;
static void eval(int J,int p,int q){
  int m=INF; for(int k=p;k<q;k++) if(w[k]<m) m=w[k];
  int any_ok=0, any_fail=0, feasible=0;
  for(int r=p;r<q;r++){ if(w[r]!=m) continue;
    int R[32]; for(int i=0;i<J-r;i++) R[i]=w[J-1-i];
    A(aF,needF,topsF,w,r+1,p); A(aM,needM,1,w,r+1,p);
    A(bF,needF,topsF,R,J-r,J-q); A(bM,needM,1,R,J-r,J-q);
    int opt=INF; for(int Z=0;Z<N;Z++) if(aF[Z]<INF&&bF[Z]<INF&&aF[Z]+bF[Z]<opt) opt=aF[Z]+bF[Z];
    if(opt>=INF) continue; feasible=1;
    for(int Z=0;Z<N;Z++){ if(aF[Z]>=INF||bF[Z]>=INF||aF[Z]+bF[Z]!=opt) continue;
      int ok=0; for(int Y=0;Y<N;Y++) if(aM[Y]<=aF[Z]&&bM[Y]<=bF[Z]){ok=1;break;}
      if(ok) any_ok=1; else { any_fail=1; if(failsome<3){ printf("  fail-some r=%d Z=%d opt=%d w=",r,Z,opt); for(int k=0;k<J;k++) printf("%s%d",(k==p||k==q)?"|":" ",w[k]); printf("\n"); } } }
  }
  if(!feasible) return; rows++;
  if(any_ok) oksome++; else { failall++; if(failall<=5){ printf("  FAIL-ALL w="); for(int k=0;k<J;k++) printf("%s%d",(k==p||k==q)?"|":" ",w[k]); printf("\n"); } }
  if(any_fail) failsome++;
}
static void rec(int J,int p,int q,int k){
  if(k==J){ eval(J,p,q); return; }
  if(k==0){ for(int b=0;b<=L+1;b++){ w[0]=b; rec(J,p,q,1);} return; }
  for(int d=-1;d<=1;d+=2){ if(k==p&&d==1) continue; if(k==q&&d==-1) continue; int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; rec(J,p,q,k+1); } }
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  JMAX=atoi(argv[2]);
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L; for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsF=0; for(int i=0;i<nc;i++){ topsF|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needF[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needM[v]= v+1<L?1<<(v+1):0;
  aF=malloc(4*N);aM=malloc(4*N);bF=malloc(4*N);bM=malloc(4*N);
  for(int J=3;J<=JMAX;J++) for(int p=1;p<J;p++) for(int q=p+1;q<J;q++) rec(J,p,q,0);
  printf("legs=%s J<=%d rows=%ld some-optimal-cut-ok=%ld fail-all=%ld rows-with-some-failing-cut=%ld\n",argv[1],JMAX,rows,oksome,failall,failsome);
}
