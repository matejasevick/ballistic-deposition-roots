// Exhaustive check on the cycle Z_K: over all (K-1)! relative orders with the global
// minimum at site 0 (rotation invariance), compute root set (cyclic local minima),
// D_{i,K} for all i, and exact sums of D and D^2.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int K; int perm[16];
long long S1[16], S2[16], cnt;
static void process(void){
  int root[16], r[16], R=0;
  for(int j=0;j<K;j++){ int l=perm[(j+K-1)%K], c=perm[j], rr=perm[(j+1)%K]; root[j]=(c<l && c<rr); if(root[j]) r[R++]=j; }
  int D[16]; memset(D,0,sizeof D);
  for(int k=0;k<R;k++){ int d = (k+1<R)? r[k+1]-r[k] : r[0]+K-r[k]; if(d>=2 && d-1<16) D[d-1]++; }
  for(int i=1;i<16;i++){ S1[i]+=D[i]; S2[i]+=(long long)D[i]*D[i]; }
  cnt++;
}
static void rec(int pos, int used){ // perm[0]=0 fixed
  if(pos==K){ process(); return; }
  for(int v=1; v<K; v++) if(!(used>>v & 1)){ perm[pos]=v; rec(pos+1, used|(1<<v)); }
}
int main(int argc,char**argv){
  K=atoi(argv[1]); perm[0]=0; rec(1,1);
  printf("K=%d orders=%lld\n",K,cnt);
  for(int i=1;i<=K-2 && i<8;i++) printf("i=%d sum=%lld sumsq=%lld\n",i,S1[i],S2[i]);
  return 0;
}
