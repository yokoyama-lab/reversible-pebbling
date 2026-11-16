/* 2CM_2 の 1 列: 森と 1 本の最短．使い方: one LEGS "b0,b1,..." p q  （境目は相 p の前と相 q の前） */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define INF 1000000
static int L,N,nc,len[8],st[8],needF[16],needM[16],topsF,pc[1<<16];
static void closure(int *d,const int *need,int b){ int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF) continue;
  for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>b) continue; if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } } }
static int solve(const int *need,int req,const int *w,int J,int p,int q){
  int *d=malloc(sizeof(int)*N); for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){ if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if((k==p||k==q) && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF; closure(d,need,w[k]); }
  int r=d[0]; free(d); return r; }
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  int w[64],J=0; strncpy(buf,argv[2],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) w[J++]=atoi(t);
  int p=atoi(argv[3]),q=atoi(argv[4]);
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L; for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsF=0; for(int i=0;i<nc;i++){ topsF|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needF[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needM[v]= v+1<L?1<<(v+1):0;
  int f=solve(needF,topsF,w,J,p,q), m=solve(needM,1,w,J,p,q);
  printf("legs=%s w=%s p=%d q=%d forest=%d merged=%d %s\n",argv[1],argv[2],p,q,f,m, m>f?"VIOLATION":"ok");
}
