/* CK.md §7，§8.3（pair_s.c に「脚の中で整列した最適な切り口があるか」の集計を足したもの）．2CM_2 規則版の各列で，間の予算が最小の相 r（すべて）と，そこで森の最適解を切った盤 Z（A^森+B^森 = OPT^森 となる Z すべて）について:
   (1) 1 本の盤 Y で A^1本(Y) ≤ A^森(Z) かつ B^1本(Y) ≤ B^森(Z) となるものがあるか（列ごと．pair.c と同じ）．
   (2) Z ごとに，Z が最適な切り口になるすべての列で両側を支配する Y があるか（歩みによらない対応．"without walk-independent g"）．
   (3) 規則 S（頂上の空きの和を一番上，その下に区間を短い順）と対照 2 種（区間を長い順，空きを一番下）が (2) の候補に入るか．
   使い方: pair_s LEGS JMAX [dump]   dump=1 で Z ごとに大きさ |Z| の候補を最大 40 個表示 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define INF 1000000
static int DUMP; static int L,N,nc,len[8],st[8],needF[16],needM[16],topsF,pc[1<<16],JMAX;
static void closure(int *d,const int *need,int b){ int ch=1; while(ch){ch=0; for(int x=0;x<N;x++){ if(d[x]>=INF) continue;
  for(int v=0;v<L;v++){ if((x&need[v])!=need[v]) continue; int y=x^(1<<v); if(pc[y]>b) continue; if(d[x]+1<d[y]){d[y]=d[x]+1;ch=1;} } } } }
static void A(int *d,const int *need,int req,const int *w,int J,int p){
  for(int x=0;x<N;x++) d[x]=INF; d[0]=0;
  for(int k=0;k<J;k++){ if(k>0){ int lim=w[k-1]<w[k]?w[k-1]:w[k];
      for(int x=0;x<N;x++){ if(pc[x]>lim) d[x]=INF; if(k==p && (x&req)!=req) d[x]=INF; } }
    for(int x=0;x<N;x++) if(pc[x]>w[k]) d[x]=INF; closure(d,need,w[k]); } }
static int w[32]; static long rows=0,okall=0,oksome=0,failall=0,failsome=0;
static int *aF,*aM,*bF,*bM; static unsigned char *cand; static char *seenZ,*lsort; static long rows_nosorted=0,rows_nosorted0=0;
static void eval(int J,int p,int q){
  int m=INF; for(int k=p;k<q;k++) if(w[k]<m) m=w[k];
  int any_ok=0, any_fail=0, feasible=0, has_sorted=0, has_sorted0=0;
  for(int r=p;r<q;r++){ if(w[r]!=m) continue;
    int R[32]; for(int i=0;i<J-r;i++) R[i]=w[J-1-i];
    A(aF,needF,topsF,w,r+1,p); A(aM,needM,1,w,r+1,p);
    A(bF,needF,topsF,R,J-r,J-q); A(bM,needM,1,R,J-r,J-q);
    int opt=INF; for(int Z=0;Z<N;Z++) if(aF[Z]<INF&&bF[Z]<INF&&aF[Z]+bF[Z]<opt) opt=aF[Z]+bF[Z];
    if(opt>=INF) continue; feasible=1;
    for(int Z=0;Z<N;Z++){ if(aF[Z]>=INF||bF[Z]>=INF||aF[Z]+bF[Z]!=opt) continue;
      if(lsort[Z]){ has_sorted=1; if(lsort[Z]==2) has_sorted0=1; }
      if(!seenZ[Z]){ seenZ[Z]=1; for(int Y=0;Y<N;Y++) cand[(long)Z*N+Y]=1; }
      for(int Y=0;Y<N;Y++) if(!(aM[Y]<=aF[Z]&&bM[Y]<=bF[Z])) cand[(long)Z*N+Y]=0;
      int ok=0; for(int Y=0;Y<N;Y++) if(aM[Y]<=aF[Z]&&bM[Y]<=bF[Z]){ok=1;break;}
      if(ok) any_ok=1; else { any_fail=1; if(failsome<3){ printf("  fail-some r=%d Z=%d opt=%d w=",r,Z,opt); for(int k=0;k<J;k++) printf("%s%d",(k==p||k==q)?"|":" ",w[k]); printf("\n"); } } }
  }
  if(!feasible) return; rows++; if(!has_sorted){ rows_nosorted++; if(rows_nosorted<=3){ printf("  no leg-sorted optimal cut w="); for(int k=0;k<J;k++) printf("%s%d",(k==p||k==q)?"|":" ",w[k]); printf("\n"); } } if(!has_sorted0) rows_nosorted0++;
  if(any_ok) oksome++; else { failall++; if(failall<=5){ printf("  FAIL-ALL w="); for(int k=0;k<J;k++) printf("%s%d",(k==p||k==q)?"|":" ",w[k]); printf("\n"); } }
  if(any_fail) failsome++;
}
static void rec(int J,int p,int q,int k){
  if(k==J){ eval(J,p,q); return; }
  if(k==0){ for(int b=0;b<=L+1;b++){ w[0]=b; rec(J,p,q,1);} return; }
  for(int d=-1;d<=1;d+=2){ if(k==p&&d==1) continue; if(k==q&&d==-1) continue; int nb=w[k-1]+d; if(nb<0||nb>L+1) continue; w[k]=nb; rec(J,p,q,k+1); } }
int main(int argc,char**argv){
  char buf[64]; strncpy(buf,argv[1],63); for(char*t=strtok(buf,",");t;t=strtok(NULL,",")) len[nc++]=atoi(t);
  JMAX=atoi(argv[2]); DUMP=argc>3?atoi(argv[3]):0;
  L=0; for(int i=0;i<nc;i++){st[i]=L;L+=len[i];} N=1<<L; for(int x=0;x<N;x++) pc[x]=__builtin_popcount(x);
  topsF=0; for(int i=0;i<nc;i++){ topsF|=1<<st[i]; for(int j=0;j<len[i];j++){int v=st[i]+j; needF[v]= j+1<len[i]?1<<(v+1):0;} }
  for(int v=0;v<L;v++) needM[v]= v+1<L?1<<(v+1):0;
  cand=calloc((long)N*N,1); lsort=calloc(N,1);
  for(int Z=0;Z<N;Z++){ int tau=0,ok=1; for(int i=0;i<nc;i++){ int prev=-1,last=0; for(int j=0;j<=len[i];j++) if(j==len[i]||(Z>>(st[i]+j)&1)){ if(prev<0) tau+=j; else { int sl=j-prev; if(sl<last) ok=0; last=sl; } prev=j; } }
    lsort[Z]= ok ? (tau==0?2:1) : 0; } seenZ=calloc(N,1); aF=malloc(4*N);aM=malloc(4*N);bF=malloc(4*N);bM=malloc(4*N);
  for(int J=3;J<=JMAX;J++) for(int p=1;p<J;p++) for(int q=p+1;q<J;q++) rec(J,p,q,0);
  int nz=0,bad=0; for(int Z=0;Z<N;Z++) if(seenZ[Z]){ nz++; int c=0; for(int Y=0;Y<N;Y++) c+=cand[(long)Z*N+Y];
    if(!c){ bad++; if(bad<=5){ printf("  NO-G Z="); int s2=0; for(int i=0;i<nc;i++){ if(i) putchar('|'); for(int j=0;j<len[i];j++) putchar(Z>>(s2+j)&1?'1':'.'); s2+=len[i]; } printf("\n"); } }
    else if(DUMP){ printf("  Z="); int s2=0; for(int i=0;i<nc;i++){ if(i) putchar('|'); for(int j=0;j<len[i];j++) putchar(Z>>(s2+j)&1?'1':'.'); s2+=len[i]; } printf(" ->"); int k=0;
      for(int Y=0;Y<N;Y++) if(cand[(long)Z*N+Y] && __builtin_popcount(Y)==__builtin_popcount(Z) && k++<40){ putchar(' '); for(int j=0;j<L;j++) putchar(Y>>j&1?'1':'.'); } printf("\n"); } }
  printf("optimal-cut boards=%d without walk-independent g=%d\n",nz,bad);
  { int t0=0,t0uns=0,tp=0,tpuns=0; for(int Z=0;Z<N;Z++){ if(!seenZ[Z]) continue; int tau=0,ok=1;
      for(int i=0;i<nc;i++){ int prev=-1,last=0; for(int j=0;j<=len[i];j++) if(j==len[i]||(Z>>(st[i]+j)&1)){ if(prev<0) tau+=j; else { int sl=j-prev; if(sl<last) ok=0; last=sl; } prev=j; } if(prev<0) ok=ok; }
      if(tau==0){ t0++; if(!ok){ t0uns++; if(t0uns<=5){ printf("  unsorted tau0 Z="); int s2=0; for(int i=0;i<nc;i++){ if(i) putchar('|'); for(int j=0;j<len[i];j++) putchar(Z>>(s2+j)&1?'1':'.'); s2+=len[i]; } printf("\n"); } } }
      else { tp++; if(!ok) tpuns++; } }
    printf("tau0 optimal cuts=%d leg-unsorted=%d ; tau>0 cuts=%d leg-unsorted(below gap)=%d\n",t0,t0uns,tp,tpuns); }
  /* 規則 S: 頂上の空きの和 τ を一番上に，その下に区間（石から次の石の前まで，最後は脚の底まで）を短い順．
     対照 S_desc: 区間を長い順．対照 S_top0: 空きを一番下（τ を底へ）＝区間を短い順に上から詰める */
  for(int rule=0;rule<3;rule++){ int fails=0,firstZ=-1;
    for(int Z=0;Z<N;Z++){ if(!seenZ[Z]) continue; int seg[32],ns=0,tau=0;
      for(int i=0;i<nc;i++){ int prev=-1; for(int j=0;j<len[i];j++) if(Z>>(st[i]+j)&1){ if(prev<0) tau+=j; else seg[ns++]=j-prev; prev=j; }
        if(prev<0) tau+=len[i]; else seg[ns++]=len[i]-prev; }
      for(int a=0;a<ns;a++) for(int b=a+1;b<ns;b++) if(rule==1 ? seg[b]>seg[a] : seg[b]<seg[a]){int t=seg[a];seg[a]=seg[b];seg[b]=t;}
      int Y=0,pos=(rule==2)?0:tau; for(int a=0;a<ns;a++){ Y|=1<<pos; pos+=seg[a]; }
      if(!cand[(long)Z*N+Y]){ fails++; if(firstZ<0) firstZ=Z; } }
    printf("  rule %s fails=%d", rule==0?"S":rule==1?"S_desc":"S_top0", fails);
    if(firstZ>=0){ printf(" e.g. Z="); int s2=0; for(int i=0;i<nc;i++){ if(i) putchar('|'); for(int j=0;j<len[i];j++) putchar(firstZ>>(s2+j)&1?'1':'.'); s2+=len[i]; } }
    printf("\n"); }
  printf("rows without leg-sorted optimal cut=%ld ; without tau0 leg-sorted optimal cut=%ld\n",rows_nosorted,rows_nosorted0);
  printf("legs=%s J<=%d rows=%ld some-optimal-cut-ok=%ld fail-all=%ld rows-with-some-failing-cut=%ld\n",argv[1],JMAX,rows,oksome,failall,failsome);
}
