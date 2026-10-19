// Exact E[max_x H_n(x)] and E[min_x H_n(x)] over all K^n drop words (DFS), cyclic BD rule
#include <stdio.h>
#include <stdlib.h>
int K, N; long long Hs[20][16]; double sumMax[20], sumMin[20]; long long cnt[20];
void dfs(int d){
  long long mx=0, mn=1LL<<60; for(int x=0;x<K;x++){ if(Hs[d][x]>mx) mx=Hs[d][x]; if(Hs[d][x]<mn) mn=Hs[d][x]; }
  sumMax[d]+=mx; sumMin[d]+=mn; cnt[d]++;
  if(d==N) return;
  for(int j=0;j<K;j++){
    for(int x=0;x<K;x++) Hs[d+1][x]=Hs[d][x];
    long long a=Hs[d][(j+K-1)%K], b=Hs[d][j], c=Hs[d][(j+1)%K], m=a>b?a:b; if(c>m) m=c;
    Hs[d+1][j]=m+1; dfs(d+1);
  }
}
int main(int argc,char**argv){ K=atoi(argv[1]); N=atoi(argv[2]); dfs(0);
  for(int n=1;n<=N;n++) printf("K=%d n=%d  E[min]/n=%.5f  E[max]/n=%.5f   (x K: %.4f .. %.4f)\n",K,n,sumMin[n]/cnt[n]/n,sumMax[n]/cnt[n]/n,K*sumMin[n]/cnt[n]/n,K*sumMax[n]/cnt[n]/n);
}
