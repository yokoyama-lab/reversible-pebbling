/* CK.md §8.2．片側の歩み（境目 p で森は全頂上，1 本は v0．最後の相で盤 Z）で，全頂上を含み各脚の区間が上から短い順の Z（脚の中で整列）に限って
   A^1本(sorted(Z)) <= A^森(Z) を調べる．
   mode 0: ±1 の歩み（境目は -1），谷の条件なし / 1: ±1，谷の条件つき / 2: 予算を [0,L+1] で自由（境目は下がる），谷なし /
   3: 自由，境目は下がる，谷つき / 4: 自由，境目で下がらなくてよい，谷つき．
   使い方: g5 LEGS JMAX MODE */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define INF 1000000
static int L,N,nc,len[8],st[8],needF[16],needM[16],topsF,pc[1<<16],JMAX,MODE;
static void closure(int *d,const int *need,int b){ int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF) continue;
  for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>b) continue; if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } } }
static void A(int *d,const int *need,int req,const int *w,int J,int p){
  for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){ if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if(k==p && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF; closure(d,need,w[k]); } }
static int w[32],*aF,*aM,sortedOf[1<<16]; static char legsorted[1<<16]; static long walks=0,pts=0,bad=0,eq=0;
static void eval(int J,int p){
  if(MODE==1||MODE==3||MODE==4){ for(int k=p;k<J;k++) if(w[k]<w[J-1]) return; }
  walks++; A(aF,needF,topsF,w,J,p); A(aM,needM,1,w,J,p);
  for(int Z=0;Z<N;Z++){ if((Z&topsF)!=topsF||aF[Z]>=INF||!legsorted[Z]) continue; pts++; int y=aM[sortedOf[Z]];
    if(y>aF[Z]){ bad++; if(bad<=5){ printf("  BAD Z="); int s2=0; for(int i=0;i<nc;i++){ if(i) putchar('|'); for(int j=0;j<len[i];j++) putchar(Z>>(s2+j)&1?'1':'.'); s2+=len[i]; }
      printf(" F=%d 1=%d w=",aF[Z],y); for(int k=0;k<J;k++) printf("%s%d",k==p?"|":" ",w[k]); printf("\n"); } }
    else if(y==aF[Z]) eq++; } }
static void rec(int J,int p,int k){
  if(k==J){ eval(J,p); return; }
  if(MODE>=2){ for(int b=0;b<=L+1;b++){ if((MODE==2||MODE==3) && k==p && b>w[k-1]-1) continue; w[k]=b; rec(J,p,k+1);} return; }
  if(k==0){ for(int b=0;b<=L+1;b++){ w[0]=b; rec(J,p,1);} return; }
  for(int d=-1;d<=1;d+=2){ if(k==p&&d==1) continue; int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; rec(J,p,k+1); } }
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  JMAX=atoi(argv[2]); MODE=atoi(argv[3]);
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L; for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsF=0; for(int i=0;i<nc;i++){ topsF|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needF[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needM[v]= v+1<L?1<<(v+1):0;
  for(int Z=0;Z<N;Z++){ if((Z&topsF)!=topsF) continue; int seg[32],ns=0;
    for(int i=0;i<nc;i++){ int prev=-1; for(int j=0;j<len[i];j++) if(Z>>(st[i]+j)&1){ if(prev>=0) seg[ns++]=j-prev; prev=j; } seg[ns++]=len[i]-prev; }
    { int ok=1,s0=0; for(int i=0;i<nc;i++){ int prev=-1,last=0; for(int j=0;j<=len[i];j++) if(j==len[i]||(Z>>(st[i]+j)&1)){ if(prev>=0){ int sl=j-prev; if(sl<last) ok=0; last=sl; } prev=j; } } legsorted[Z]=ok; (void)s0; }
    for(int a=0;a<ns;a++) for(int b=a+1;b<ns;b++) if(seg[b]<seg[a]){int t=seg[a];seg[a]=seg[b];seg[b]=t;}
    int Y=0,pos=0; for(int a=0;a<ns;a++){ Y|=1<<pos; pos+=seg[a]; } sortedOf[Z]=Y; }
  aF=malloc(4*N); aM=malloc(4*N);
  for(int J=2;J<=JMAX;J++) for(int p=1;p<J;p++) rec(J,p,0);
  printf("legs=%s J<=%d mode=%d walks=%ld points=%ld bad=%ld equal=%ld\n",argv[1],JMAX,MODE,walks,pts,bad,eq);
}
