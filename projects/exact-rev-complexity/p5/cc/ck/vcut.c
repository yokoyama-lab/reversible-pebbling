/* 谷で切った片側（CK.md §6）．∅ → 境目（予算 −1，森は全頂上・1 本は v0）→ 相 r（最後の相）で盤 Z の最短 A_w(Z)．
   森の盤 Z ごとに，全ての歩みで A^1本_w(Z') ≤ A^森_w(Z) となる Z' の集合 cand[Z] を求める．
   使い方: vcut LEGS JMAX [valley] [dump]   valley=1: β_r ≤ β_k (p≤k≤r) の歩みのみ．dump=1 は Z ごとに大きさ |Z| の候補を最大 64 個表示 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define INF 1000000
static int L,N,nc,len[8],st[8],needF[16],needM[16],topsF,pc[1<<12],JMAX,VAL;
static uint64_t cand[1<<12][ (1<<12)/64 ]; static char seen[1<<12], init_[1<<12];
static long nw=0;
static void closure(int *d,const int *need,int b){
  int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF) continue;
    for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>b) continue;
      if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } }
}
static void A(int *d,const int *need,int req,const int *w,int J,int p){
  for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){
    if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if(k==p && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF;
    closure(d,need,w[k]);
  }
}
static int w[32]; static int *aF,*aM;
static void eval(int J,int p){
  int r=J-1;
  if(VAL) for(int k=p;k<=r;k++) if(w[k]<w[r]) return;
  nw++;
  A(aF,needF,topsF,w,J,p); A(aM,needM,1,w,J,p);
  int W=(N+63)/64;
  for(int Z=0;Z<N;Z++){ if(aF[Z]>=INF) continue; seen[Z]=1;
    if(!init_[Z]){ init_[Z]=1; for(int i=0;i<W;i++) cand[Z][i]=~0ULL; }
    for(int Y=0;Y<N;Y++) if(aM[Y]>aF[Z]) cand[Z][Y>>6]&=~(1ULL<<(Y&63)); }
}
static void rec(int J,int p,int k){
  if(k==J){ eval(J,p); return; }
  if(k==0){ for(int b=0;b<=L+1;b++){ w[0]=b; rec(J,p,1);} return; }
  for(int d=-1;d<=1;d+=2){ if(k==p && d==1) continue; int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; rec(J,p,k+1); }
}
static void show(int x,int nlegs,const int *ls){ int s=0; for(int i=0;i<nlegs;i++){ if(i) putchar('|'); for(int j=0;j<ls[i];j++) putchar(x>>(s+j)&1?'1':'.'); s+=ls[i]; } }
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  JMAX=atoi(argv[2]); VAL=argc>3?atoi(argv[3]):0; int dump=argc>4?atoi(argv[4]):0;
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L;
  for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsF=0; for(int i=0;i<nc;i++){ topsF|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needF[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needM[v]= v+1<L?1<<(v+1):0;
  aF=malloc(sizeof(int)*N); aM=malloc(sizeof(int)*N);
  for(int J=2;J<=JMAX;J++) for(int p=1;p<J;p++) rec(J,p,0);
  int ns=0,bad=0; for(int Z=0;Z<N;Z++) if(seen[Z]){ ns++; int any=0; for(int Y=0;Y<N;Y++) if(cand[Z][Y>>6]>>(Y&63)&1) any=1; if(!any){ bad++; if(bad<=10){printf("  NONE: "); show(Z,nc,len); printf("\n");} } }
  printf("legs=%s JMAX=%d valley=%d walks=%ld boards=%d no-dominator=%d\n",argv[1],JMAX,VAL,nw,ns,bad);
  if(dump) for(int Z=0;Z<N;Z++) if(seen[Z]){ printf("  "); show(Z,nc,len); printf(" ->"); int c=0;
    for(int Y=0;Y<N;Y++) if(cand[Z][Y>>6]>>(Y&63)&1){ if(c++<64 && pc[Y]==pc[Z]){ putchar(' '); show(Y,1,&L);} } if(!c) printf(" NONE"); printf("\n"); }
  return 0;
}
