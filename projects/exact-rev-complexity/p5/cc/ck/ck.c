/* 2CM_k の一般化（検問つきの歩み）: 鎖の森 P（各鎖の頂上を検問で要求）と，1 本に併合した Q（v_0 だけを要求）．
   歩み w（隣は ±1，β ≥ 0），検問は切り替え位置の集合（k 個）．始めと終わりは空．最小手数 OPT_P, OPT_Q を比べる．
   さらに 2CM の規則版（検問で予算が u の置く/外すに応じて −1/+1，それ以外の切り替えは ±1 自由）も mode=1 で．
   使い方: ck "a,b[,c..]" K JMAX [mode]   出力: 破れ（OPT_Q > OPT_P）の数と例 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define INF 1000000
static int L,N,nc,len[8],st[8],needP[16],needQ[16],topsP,topQ,pc[1<<16];
static int K,JMAX,MODE;
static long rows=0,viol=0,eq=0;
static int *dp,*tmp;
static void relax(int *d,const int *need,int B){
  /* 単位重みの多始点: Bellman 風に収束まで */
  int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF||pc[x]>B) continue;
    for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>B) continue;
      if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } }
}
static int solve(const int *need,int req,const int *w,int J,const int *cp){
  int *d=malloc(sizeof(int)*N); for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){
    if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if(cp[k] && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF;
    relax(d,need,w[k]);
  }
  int r=d[0]; free(d); return r;
}
static int w[32],cp[32];
static void rec(int J,int k,int ncp){
  if(k==J){ if(ncp!=K) return;
    int op=solve(needP,topsP,w,J,cp), oq=solve(needQ,topQ,w,J,cp);
    if(op>=INF) return; rows++;
    if(oq>op){ viol++; if(viol<=5){ printf("  viol P=%d Q=%d w=",op,oq); for(int i=0;i<J;i++) printf("%s%d",cp[i]?"|":" ",w[i]); printf("\n"); } }
    if(oq==op) eq++;
    return; }
  for(int c=0;c<=1;c++){
    if(c && (k==0 || ncp==K)) continue;
    if(MODE==1 && c){ /* 検問 = u の手．奇数番目は置く（予算 −1），偶数番目は外す（+1） */
      int nb=w[k-1]+((ncp%2==0)?-1:1); if(nb<0||nb>L+1) continue;
      w[k]=nb; cp[k]=1; rec(J,k+1,ncp+1); cp[k]=0; continue; }
    if(k==0){ for(int b=0;b<=L+1;b++){ w[0]=b; cp[0]=0; rec(J,1,ncp);} return; }
    if(c){ for(int d=-1;d<=1;d+=2){ int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; cp[k]=1; rec(J,k+1,ncp+1);} cp[k]=0; continue; }
    for(int d=-1;d<=1;d+=2){ int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; cp[k]=0; rec(J,k+1,ncp); }
  }
}
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  K=atoi(argv[2]); JMAX=atoi(argv[3]); MODE=argc>4?atoi(argv[4]):0;
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L;
  for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsP=0; for(int i=0;i<nc;i++){ topsP|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needP[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needQ[v]= v+1<L?1<<(v+1):0; topQ=1;
  for(int J=K+1;J<=JMAX;J++) rec(J,0,0);
  printf("legs=%s K=%d J<=%d mode=%d rows=%ld viol=%ld eq=%ld\n",argv[1],K,JMAX,MODE,rows,viol,eq);
  return 0;
}
