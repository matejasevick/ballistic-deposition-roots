// Cross moments E[D_i D_j] on the cycle by exhaustive enumeration (global min fixed at 0).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int K; int perm[16]; long long S1[16], S2[16][16], cnt;
static void process(void){
  int r[16], R=0;
  for(int j=0;j<K;j++){ int l=perm[(j+K-1)%K], c=perm[j], rr=perm[(j+1)%K]; if(c<l && c<rr) r[R++]=j; }
  int D[16]; memset(D,0,sizeof D);
  for(int k=0;k<R;k++){ int d=(k+1<R)? r[k+1]-r[k] : r[0]+K-r[k]; if(d>=2) D[d-1]++; }
  for(int i=1;i<8;i++){ S1[i]+=D[i]; for(int j=1;j<8;j++) S2[i][j]+=(long long)D[i]*D[j]; }
  cnt++;
}
static void rec(int pos,int used){ if(pos==K){process();return;} for(int v=1;v<K;v++) if(!(used>>v&1)){perm[pos]=v;rec(pos+1,used|(1<<v));} }
int main(int argc,char**argv){ K=atoi(argv[1]); perm[0]=0; rec(1,1);
  printf("K %d %lld\n",K,cnt); for(int i=1;i<8;i++){ printf("S1 %d %lld\n",i,S1[i]); for(int j=1;j<8;j++) printf("S2 %d %d %lld\n",i,j,S2[i][j]); } return 0; }
