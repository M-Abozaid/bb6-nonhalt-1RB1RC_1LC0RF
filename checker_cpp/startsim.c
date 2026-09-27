// direct TM simulation from blank tape; at every checkpoint (state C reads 0, previous move L, head at the
// leftmost cell ever visited) with index >= E0, test the config against a DFA (format: certificate/FORMAT.md). Report first hit.
// usage: startsim DFA E0 EMAX [start_state 0..5 (0=A, 3=D)] [out_file=found_conf.txt]
// The first accepted config is written as text (.=0, 1=1, A-F head reading 0, a-f head reading 1) with 4 blanks each side.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define NS 14
int TW[6][2],TD[6][2],TS[6][2];
int main(int argc,char**argv){
  if(argc<4){fprintf(stderr,"usage: startsim DFA E0 EMAX [start_state] [out_file]\n");return 2;}
  const char*M="1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA";
  for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=M+s*7+r*3; if(t[0]=='-'){TS[s][r]=-1;continue;} TW[s][r]=t[0]-'0';TD[s][r]=t[1]=='R'?1:-1;TS[s][r]=t[2]-'A';}
  FILE*f=fopen(argv[1],"r"); int n,s0; if(fscanf(f,"%d %d",&n,&s0)!=2)return 2; int(*T)[NS]=malloc(sizeof(int)*NS*n); char*acc=malloc(n);
  for(int q=0;q<n;q++){int a; if(fscanf(f,"%d",&a)!=1)return 2; acc[q]=a; for(int c=0;c<NS;c++) if(fscanf(f,"%d",&T[q][c])!=1)return 2;} fclose(f);
  long E0=atol(argv[2]), EMAX=atol(argv[3]);
  long L=1<<22; unsigned char*tape=calloc(L,1); long h=L/2, lo=h, hi=h; int s=(argc>4?atoi(argv[4]):0), dprev=0; long long steps=0; long ev=0;
  while(1){
    int r=tape[h];
    if(TS[s][r]<0){ printf("HALT at step %lld\n",steps); return 1; }
    if(s==2 && r==0 && dprev==-1 && h<=lo){
      ev++;
      if(ev>=E0){
        int q=s0; for(long i=lo-4;i<=hi+4 && q>=0;i++){ int c= i==h? 2+2*s+r : tape[i]; q=T[q][c]; }
        int in = q>=0 && acc[q];
        if(in || ev%1000==0) { printf("checkpoint %ld step %lld in=%d len=%ld\n",ev,steps,in,hi-lo+1); fflush(stdout);}
        if(in){
          FILE*o=fopen(argc>5?argv[5]:"found_conf.txt","w"); for(long i=lo-4;i<=hi+4;i++){ int c=i==h?2+2*s+r:tape[i]; fputc(c<2?".1"[c]:(c%2?'a':'A')+(c-2)/2, o);} fputc('\n',o); fclose(o);
          return 0; }
        if(ev>=EMAX) return 3;
      }
    }
    int w=TW[s][r],d=TD[s][r]; tape[h]=w; s=TS[s][r]; h+=d; dprev=d; steps++;
    if(h<lo)lo=h; if(h>hi)hi=h;
    if(h<8||h>L-8){ printf("tape overflow\n"); return 2; }
  }
}
