/* 補題 M の検査: 固定した S で Δ(n,S) = F(n,S-1) - F(n,S) が n について非減少か（F は Knill の再帰，∞ は INF）．
   F(n,S) = [n==1] 1, else min_{1<=m<n} F(m,S)+F(m,S-1)+F(n-m,S-1)．F(n,0)=∞．
   使い方: lemM NMAX SMAX [mut]   mut は検出力の確認用の変異（1〜3．下の main の注） */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
#define INF (1LL<<60)
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]),SMAX=atoi(argv[2]); int mut=argc>3?atoi(argv[3]):0; /* 1: F(m,S-1)→F(m,S)，2: F(1,S)=S（S に依存させる），3: 3 項目を F(n-m,S) に */
  ll **F=malloc(sizeof(ll*)*(SMAX+1));
  for(int S=0;S<=SMAX;S++){F[S]=malloc(sizeof(ll)*(NMAX+1)); for(int n=0;n<=NMAX;n++)F[S][n]=INF;}
  for(int S=1;S<=SMAX;S++) for(int n=1;n<=NMAX;n++){
    if(n==1){F[S][n]=(mut==2)?S:1;continue;}
    ll best=INF;
    for(int m=1;m<n;m++){ ll a=F[S][m],b=F[S-1][m],c=F[S-1][n-m];
      if(mut==1){ b=F[S][m]; } if(mut==3){ c=F[S][n-m]; }
      if(a>=INF||b>=INF||c>=INF)continue; ll v=a+b+c; if(v<best)best=v; }
    F[S][n]=best; }
  long viol=0,chk=0;
  for(int S=2;S<=SMAX;S++) for(int y=1;y<=NMAX;y++) for(int x=y+1;x<=NMAX;x++){
    /* 主張: F(y,S)+F(x,S-1) >= F(x,S)+F(y,S-1) */
    ll l1=F[S][y],l2=F[S-1][x],r1=F[S][x],r2=F[S-1][y];
    if(l2>=INF) continue; /* 左辺 ∞ */
    chk++;
    if(r1>=INF||r2>=INF){viol++; if(viol<5)printf("inf-viol S=%d y=%d x=%d\n",S,y,x); continue;}
    if(l1+l2<r1+r2){viol++; if(viol<10)printf("viol S=%d y=%d x=%d: %lld+%lld < %lld+%lld\n",S,y,x,l1,l2,r1,r2);}
  }
  long strict=0,rev=0;
  for(int S=2;S<=SMAX;S++) for(int y=1;y<=NMAX;y++) for(int x=y+1;x<=NMAX;x++){
    ll l1=F[S][y],l2=F[S-1][x],r1=F[S][x],r2=F[S-1][y];
    if(l2>=INF) continue;
    if(l1+l2>r1+r2) strict++;
    /* 対照: 向きを逆にした主張 F(x,S)+F(y,S-1) >= F(y,S)+F(x,S-1) の破れ */
    if(r1+r2<l1+l2) rev++;
  }
  printf("strict=%ld reverse_claim_viol=%ld\n",strict,rev);
  printf("NMAX=%d SMAX=%d checked=%ld viol=%ld %s\n",NMAX,SMAX,chk,viol,mut?"(mutant)":"");
  printf("F(4,3)=%lld F(8,4)=%lld F(12,5)=%lld F(16,5)=%lld\n",F[3][4],F[4][8],F[5][12],F[5][16]);
  return 0;}
