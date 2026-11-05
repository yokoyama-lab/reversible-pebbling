// Check (R'), (S) and (R*) for the gap-merge potential, p given, gaps in [1,G], all lengths m<=p.
// phi(B) via DP over states (r = number of surviving blocks from the left, boundary mask).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int p, G;
static long T(int m){ return 1L<<(p-m); }
#define MAXM 8
// state: blocks described by an array of lengths; we memoize by (deleted-suffix start, boundary mask).
// Implementation: recursive with memo keyed by a 32-bit code: top (0..m) and mask (m-1 bits).
static long memo[MAXM+1][1<<(MAXM-1)];
static int B0[MAXM]; static int m0;
static long phi_state(int top, int mask){
  // blocks: original indices 0..top-1 partitioned by boundaries in mask (bit j set => boundary between j and j+1 present, j<top-1)
  if(top==0) return 0;
  if(memo[top][mask]>=0) return memo[top][mask];
  // list blocks
  int cnt=0; int start[MAXM], endi[MAXM];
  int s=0;
  for(int j=0;j<top;j++){
    if(j==top-1 || (mask>>j)&1){ start[cnt]=s; endi[cnt]=j; cnt++; s=j+1; }
  }
  long best=-1;
  for(int i=0;i<cnt;i++){
    long content=0; for(int j=start[i];j<=endi[i];j++) content+=B0[j];
    long c = content - T(cnt); if(c<0) c=0;
    long rest;
    if(i==cnt-1){ rest=phi_state(start[i], mask & ((1<<(start[i]>0?start[i]-1:0))-1) ); }
    else { rest=phi_state(top, mask & ~(1<<endi[i])); }
    if(best<0 || c+rest<best) best=c+rest;
  }
  return memo[top][mask]=best;
}
static long phi(int *B, int m){
  m0=m; memcpy(B0,B,sizeof(int)*m);
  for(int t=0;t<=m;t++) for(int k=0;k<(1<<(MAXM-1));k++) memo[t][k]=-1;
  int full = (m>=2)?((1<<(m-1))-1):0;
  return phi_state(m, full);
}
int main(int argc,char**argv){
  p=atoi(argv[1]); G=atoi(argv[2]);
  long nR=0,fR=0,nS=0,fS=0,fRs=0; long Q=1L<<(p-2);
  for(int m=1;m<=p;m++){
    int B[MAXM]; for(int j=0;j<m;j++) B[j]=1;
    while(1){
      long f=phi(B,m);
      for(int i=0;i<m;i++){
        int B2[MAXM]; int m2=m-1;
        if(i==m-1){ memcpy(B2,B,sizeof(int)*(m-1)); }
        else { memcpy(B2,B,sizeof(int)*m); B2[i]+=B2[i+1]; for(int j=i+1;j<m-1;j++) B2[j]=B2[j+1]; }
        long f2=(m2==0)?0:phi(B2,m2);
        long E=B[i]-T(m); if(E<0) E=0;
        nS++;
        if(f2>f+E){ fS++; if(fS<=5){printf("S FAIL p=%d B=",p); for(int j=0;j<m;j++)printf("%d ",B[j]); printf("i=%d phi=%ld phi'=%ld E=%ld\n",i,f,f2,E);} }
        if(f2>f+(E<Q?E:Q)){ fRs++; }
        if(B[i]<=T(m)){ nR++; if(f2>f){ fR++; if(fR<=5){printf("R' FAIL p=%d B=",p); for(int j=0;j<m;j++)printf("%d ",B[j]); printf("i=%d\n",i);} } }
      }
      int j=0; while(j<m && B[j]==G){ B[j]=1; j++; } if(j==m) break; B[j]++;
    }
  }
  printf("p=%d G=%d: R' checked %ld fails %ld | S checked %ld fails %ld | R*(min(E,2^(p-2))) fails %ld\n",p,G,nR,fR,nS,fS,fRs);
  return 0;
}
