// independent simulator of M from blank tape; start state given; checkpoints = C reading 0 arrived by left move
// usage: sim START_STATE(0=A,3=D) MAXCK TARGET_CONF.txt   -- simulates until the tape equals the target config
// (compared as a trimmed string incl. head letter); prints checkpoint count and step count on MATCH.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<24)
static unsigned char tape[N];
// M = 1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA
static const char *MS="1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA";
int W[6][2],D[6][2],S[6][2];
static char *target; static long tlen;
static void trim(const char*s,long n,long*a,long*b){long i=0,j=n-1;while(i<n&&(s[i]=='.'||s[i]=='0'))i++;while(j>=0&&(s[j]=='.'||s[j]=='0'||s[j]=='\n'))j--;*a=i;*b=j;}
int main(int argc,char**argv){
  int st=atoi(argv[1]); long maxck=atol(argv[2]); FILE*f=fopen(argv[3],"r");
  target=malloc(1<<22); tlen=fread(target,1,1<<22,f); long ta,tb; trim(target,tlen,&ta,&tb); long L=tb-ta+1;
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=MS+s*7+r*3; if(t[0]=='-'){S[s][r]=-1;continue;}
    W[s][r]=t[0]-'0'; D[s][r]=t[1]=='R'?1:-1; S[s][r]=t[2]-'A';}
  long h=N/2,lo=h,hi=h; long long steps=0; long ck=0; int s=st;
  char *buf=malloc(N+2);
  for(;;){
    int r=tape[h]; if(S[s][r]<0){printf("HALT at %lld\n",steps);return 0;}
    int d=D[s][r]; tape[h]=W[s][r]; h+=d; s=S[s][r]; steps++;
    if(h<lo)lo=h; if(h>hi)hi=h; if(h<=0||h>=N-1){printf("tape overflow\n");return 1;}
    if(d<0 && s==2 && tape[h]==0){ ck++;
      long span=hi-lo+1;
      if(span>=L && span<=L+20){ // build trimmed string and compare
        long k=0; for(long i=lo;i<=hi;i++){int c=tape[i]; buf[k++]= (i==h)? (c?"abcdef"[s]:"ABCDEF"[s]) : (c?'1':'.');}
        long a,b; trim(buf,k,&a,&b);
        if(b-a+1==L && memcmp(buf+a,target+ta,L)==0){printf("MATCH checkpoint %ld steps %lld len %ld\n",ck,steps,L);fflush(stdout);return 0;}
      }
      if(ck%5000==0){printf("ck %ld steps %lld span %ld\n",ck,steps,hi-lo+1);fflush(stdout);}
      if(ck>=maxck){printf("no match by ck %ld steps %lld\n",ck,steps);return 0;}
    }
  }
}
