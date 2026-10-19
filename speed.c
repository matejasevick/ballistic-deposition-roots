#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint64_t s; static inline uint64_t rnd(){s^=s<<13;s^=s>>7;s^=s<<17;return s;}
int main(int argc,char**argv){int K=atoi(argv[1]); long long n=atoll(argv[2]); int reps=atoi(argv[3]); s=88172645463325252ULL ^ ((uint64_t)atoll(argv[4])*0x9E3779B97F4A7C15ULL);
 for(int r=0;r<reps;r++){ long long *H=calloc(K,sizeof(long long));
  for(long long t=0;t<n;t++){int j=rnd()%K; long long a=H[(j+K-1)%K],b=H[j],c=H[(j+1)%K]; long long m=a>b?a:b; if(c>m)m=c; H[j]=m+1;}
  long long mx=0; for(int j=0;j<K;j++) if(H[j]>mx) mx=H[j];
  printf("%d %.5f\n",K,(double)mx*K/n); free(H);} return 0;}
