// gcs: generalized crossing-sequence checker (no link tracking).
// Machine 1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA.
// Configurations = strings over 14 letters: 0,1 (cells) and head letters 2+2s+b (head in state s on content b).
// A config language is given as a DFA (format: certificate/FORMAT.md) and is required to be closed under 0-padding (tapes).
//
// A SEGMENT of the run starts at the config's head (START visit) and ends at the first visit satisfying the
// END predicate (mode):
//   rev   : micro sweep: END = a visit whose next move goes back to the side the head entered from
//           (entered from the left and TD=L, or from the right and TD=R). Halting visits are forbidden.
//   event : old checkpoint event: END = state C reads 0 at a cell whose left boundary was never crossed during the
//           event and which is not right of... (i.e. <= every visited cell), START visit exempt. START must be (C,0).
// A labeling assigns a crossing sequence (from SIGMA) to every boundary, outer boundaries empty, every cell
// locally consistent (cellsim), exactly one START and one END cell.  By the crossing-sequence matching lemma
// (see README.md, "Soundness") a labeling is exactly the real segment run: every x has at most one labeling and it exists iff
// the real segment ends inside the string with all crossing sequences in SIGMA.
//  (T) totality: every x in L(I) with >=PAD blank cells on both sides has a labeling.
//  (I) image   : for every x in L(I) and labeling, the end config y is in L(J)  (J = target, default I).
#include <bits/stdc++.h>
using namespace std;
static const char* MACH="1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA";
int TW[6][2],TD[6][2],TS[6][2];
void initMachine(const char*m){ for(int s=0;s<6;s++)for(int r=0;r<2;r++){const char*t=m+s*7+r*3; if(t[0]=='-'){TS[s][r]=-1;TD[s][r]=0;TW[s][r]=0;continue;} TW[s][r]=t[0]-'0';TD[s][r]=t[1]=='R'?1:-1;TS[s][r]=t[2]-'A';} }
const int NSYM=14;
struct Cr{ int8_t dir; int8_t st; };
vector<vector<Cr>> SIG; int EMPTYCS=-1;
int MODE=0; // 0 rev, 1 event

struct CellRes{ bool ok; int y; bool isEnd; int endSt; };
// L,R: crossing sequences of the left/right boundary of this cell (time ordered).
// x: content; startSt>=0 iff this is the START cell; startLeft: START cell lies left of this cell.
CellRes cellsim(const vector<Cr>&L,const vector<Cr>&R,int x,int startSt,bool startLeft){
  CellRes res; res.ok=false; res.isEnd=false; res.endSt=-1;
  bool isStart=startSt>=0;
  int pos = isStart?0 : (startLeft?-1:1);
  size_t i=0,j=0; int content=x; int st=isStart?startSt:-1; bool first=true; int entry=0; // entry: +1 from left, -1 from right
  while(true){
    if(pos==-1){ if(i==L.size())break; if(L[i].dir!=1)return res; st=L[i].st; i++; pos=0; entry=+1; }
    else if(pos==1){ if(j==R.size())break; if(R[j].dir!=-1)return res; st=R[j].st; j++; pos=0; entry=-1; }
    int rd=content; bool isEnd=false;
    if(!(isStart&&first)){
      if(MODE==0){ if(TS[st][rd]>=0 && TD[st][rd]== -entry) isEnd=true; }
      else { if(st==2 && rd==0 && i==0 && !startLeft) isEnd=true; }
    }
    if(isEnd){ if(i!=L.size()||j!=R.size())return res; res.ok=true; res.isEnd=true; res.endSt=st; res.y=content; return res; }
    if(TS[st][rd]<0) return res; // halting visit: no labeling
    int w=TW[st][rd],d=TD[st][rd],ns=TS[st][rd]; content=w; first=false;
    if(d>0){ if(j>=R.size()||R[j].dir!=1||R[j].st!=ns)return res; j++; pos=1; }
    else  { if(i>=L.size()||L[i].dir!=-1||L[i].st!=ns)return res; i++; pos=-1; }
  }
  if(i!=L.size()||j!=R.size())return res;
  res.ok=true; res.y=content; return res;
}
// NFA state = cs*4 + sS*2 + eS
inline int NSt(int cs,bool sS,bool eS){ return cs*4+(sS?2:0)+(eS?1:0); }
vector<vector<pair<int,int>>> tcache; vector<char> tdone;
const vector<pair<int,int>>& trans(int n,int xs){
  size_t key=(size_t)n*NSYM+xs;
  if(tdone.size()<=key){ tdone.resize(key+1,0); tcache.resize(key+1); }
  if(tdone[key]) return tcache[key];
  vector<pair<int,int>> out; int cs=n/4; bool sS=n&2, eS=n&1;
  bool isStart= xs>=2; int x= xs>=2?(xs-2)%2:xs; int sst= xs>=2?(xs-2)/2:-1;
  if(!(isStart&&sS) && !(isStart && MODE==1 && !(sst==2&&x==0))){
    const vector<Cr>&L=SIG[cs];
    for(int r=0;r<(int)SIG.size();r++){
      CellRes c=cellsim(L,SIG[r],x,sst,sS); if(!c.ok)continue;
      if(c.isEnd&&eS)continue;
      int y=c.isEnd? 2+2*c.endSt+c.y : c.y;
      out.push_back({NSt(r,sS||isStart,eS||c.isEnd),y});
    }
  }
  tcache[key]=out; tdone[key]=1; return tcache[key];
}
bool nfinal(int n){ return n/4==EMPTYCS && (n&2) && (n&1); }

struct DFA{ int start; vector<array<int,NSYM>> T; vector<char> acc; };
DFA loadDFA(const char*fn){ DFA D; FILE*f=fopen(fn,"r"); if(!f){fprintf(stderr,"cannot open %s\n",fn);exit(2);} int n,s0; if(fscanf(f,"%d %d",&n,&s0)!=2)exit(2);
  D.start=s0; D.T.resize(n); D.acc.resize(n); for(int q=0;q<n;q++){ int a; if(fscanf(f,"%d",&a)!=1)exit(2); D.acc[q]=a; for(int c=0;c<NSYM;c++) if(fscanf(f,"%d",&D.T[q][c])!=1)exit(2);} fclose(f); return D; }
inline int dstep(const DFA&D,int q,int c){ return q<0?-1:D.T[q][c]; }

void loadSigma(const char*fn){ ifstream in(fn); string l; while(getline(in,l)){ size_t p=l.find('|'); if(p==string::npos)continue; l=l.substr(0,p); vector<Cr> v;
    for(char c:l){ if(c>='A'&&c<='F')v.push_back({1,(int8_t)(c-'A')}); else if(c>='a'&&c<='f')v.push_back({-1,(int8_t)(c-'a')}); else {fprintf(stderr,"bad cs\n");exit(2);} }
    if(v.empty())EMPTYCS=SIG.size(); SIG.push_back(v);}
  if(EMPTYCS<0){ EMPTYCS=SIG.size(); SIG.push_back({}); } }
void genSigma(int K){ // all direction-alternating sequences of length <=K
  SIG.push_back({}); EMPTYCS=0; vector<vector<Cr>> cur={{}};
  for(int k=1;k<=K;k++){ vector<vector<Cr>> nx; for(auto&v:cur) for(int d:{1,-1}){ if(!v.empty()&&v.back().dir==d)continue; for(int s=0;s<6;s++){ auto w=v; w.push_back({(int8_t)d,(int8_t)s}); nx.push_back(w);} }
    for(auto&v:nx)SIG.push_back(v); cur=nx; } }
string sym(int c){ if(c<2) return c?"1":"."; int s=(c-2)/2,b=(c-2)%2; return string(1,(char)((b?'a':'A')+s)); }

int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage: gcs MODE(rev|event) I.dfa SIGMA(file|K=<n>) PAD [J.dfa] [machine]\n");return 2;}
  MODE= string(argv[1])=="rev"?0:1;
  initMachine(argc>6?argv[6]:MACH);
  DFA I=loadDFA(argv[2]); string sg=argv[3]; if(sg.substr(0,2)=="K=") genSigma(atoi(sg.c_str()+2)); else loadSigma(argv[3]);
  int PAD=atoi(argv[4]); DFA J= (argc>5 && string(argv[5])!="-")? loadDFA(argv[5]) : I;
  int NV=getenv("NV")?atoi(getenv("NV")):5;
  fprintf(stderr,"mode %s SIGMA %zu  I %zu states  J %zu states PAD %d\n",argv[1],SIG.size(),I.T.size(),J.T.size(),PAD);
  int n0=NSt(EMPTYCS,false,false); int rc=0;
  // ---- single head check: L(I) must contain only strings with exactly one head letter ----
  { set<pair<int,int>> seen; deque<pair<int,int>> q; q.push_back({I.start,0}); seen.insert({I.start,0}); long bad=0;
    while(!q.empty()){ auto [s,k]=q.front(); q.pop_front(); if(I.acc[s]&&k!=1)bad++;
      for(int c=0;c<NSYM;c++){ int s2=I.T[s][c]; if(s2<0)continue; int k2=min(2,k+(c>=2)); if(seen.insert({s2,k2}).second)q.push_back({s2,k2}); } }
    printf("(H) head count: %s\n",bad?"FAIL (strings with 0 or >=2 heads)":"ok"); if(bad) rc=1; }
  // ---- (P) blank-padding closure of I: 0.L(I) ⊆ L(I) and L(I).0 ⊆ L(I) ----
  { long bad=0; int q0=I.T[I.start][0];
    // right: every reachable accepting state has an accepting 0-successor
    vector<char> rs(I.T.size(),0); deque<int> q; q.push_back(I.start); rs[I.start]=1;
    while(!q.empty()){ int a=q.front(); q.pop_front(); if(I.acc[a]){ int b=I.T[a][0]; if(b<0||!I.acc[b])bad++; } for(int c=0;c<NSYM;c++){int b=I.T[a][c]; if(b>=0&&!rs[b]){rs[b]=1;q.push_back(b);}} }
    // left: pairs (delta(start,w), delta(q0,w)); acc(first) => acc(second)
    set<pair<int,int>> seen; deque<pair<int,int>> pq; pq.push_back({I.start,q0}); seen.insert({I.start,q0});
    while(!pq.empty()){ auto [a,b]=pq.front(); pq.pop_front(); if(I.acc[a]&&(b<0||!I.acc[b]))bad++;
      for(int c=0;c<NSYM;c++){ int a2=I.T[a][c]; if(a2<0)continue; int b2=b<0?-1:I.T[b][c]; if(seen.insert({a2,b2}).second)pq.push_back({a2,b2}); } }
    printf("(P) blank padding closure: %s\n",bad?"FAIL":"ok"); if(bad) rc=1; }
  // ---- (I) image ----
  { map<tuple<int,int,int>,tuple<int,int,int,int,int>> par; deque<tuple<int,int,int>> q;
    auto k0=make_tuple(I.start,n0,J.start); par[k0]=make_tuple(-1,-1,-1,0,0); q.push_back(k0); long viol=0,fin=0;
    while(!q.empty()){ auto k=q.front(); q.pop_front(); auto [qx,n,qy]=k;
      if(nfinal(n)&&I.acc[qx]){ fin++; if(qy<0||!J.acc[qy]){ viol++; if(viol<=NV){ string xs,ys; auto kk=k; while(get<0>(kk)>=0){ auto p=par[kk]; if(get<0>(p)<0)break; xs=sym(get<3>(p))+xs; ys=sym(get<4>(p))+ys; kk=make_tuple(get<0>(p),get<1>(p),get<2>(p)); } fprintf(stderr,"IMAGE VIOLATION\n x=%s\n y=%s\n",xs.c_str(),ys.c_str()); } } }
      for(int xs=0;xs<NSYM;xs++){ int qx2=I.T[qx][xs]; if(qx2<0)continue; for(auto&[n2,ys]:trans(n,xs)){ int qy2=dstep(J,qy,ys); auto k2=make_tuple(qx2,n2,qy2); if(!par.count(k2)){ par[k2]=make_tuple(qx,n,qy,xs,ys); q.push_back(k2);} } } }
    printf("(I) image: product states %zu, final %ld, violations %ld\n",par.size(),fin,viol); if(viol) rc=1; }
  // ---- (T) totality on L(I) with >=PAD blanks on both sides ----
  { // pad state: phase 0 = leading blanks counted (c<=PAD); phase 1 = after first nonblank, c = trailing blanks (<=PAD)
    auto padstep=[&](int ps,int xs)->int{ int ph=ps>>8,c=ps&255; if(ph==0){ if(xs==0)return min(c+1,PAD); return c>=PAD? (1<<8)|0 : -1; } if(xs==0)return (1<<8)|min(c+1,PAD); return (1<<8)|0; };
    auto padacc=[&](int ps){ return (ps>>8)==1 && (ps&255)>=PAD; };
    typedef pair<pair<int,int>,vector<int>> TK; map<TK,pair<TK,int>> seen; deque<TK> q;
    TK k0=make_pair(make_pair(I.start,0),vector<int>{n0}); seen[k0]={make_pair(make_pair(-1,-1),vector<int>{}),-1}; q.push_back(k0);
    long viol=0; size_t maxS=0;
    while(!q.empty()){ TK k=q.front(); q.pop_front(); int qx=k.first.first,ps=k.first.second; const vector<int> S=k.second; maxS=max(maxS,S.size());
      if(I.acc[qx]&&padacc(ps)){ bool ok=false; for(int n:S) if(nfinal(n))ok=true; if(!ok){ viol++; if(viol<=NV){ string w; TK kk=k; while(kk.first.first>=0){ auto p=seen[kk]; if(p.second<0)break; w=sym(p.second)+w; kk=p.first;} fprintf(stderr,"TOTALITY VIOLATION\n x=%s\n",w.c_str()); } } }
      for(int xs=0;xs<NSYM;xs++){ int ps2=padstep(ps,xs); if(ps2<0)continue; int qx2=I.T[qx][xs]; if(qx2<0)continue;
        vector<int> S2; for(int n:S) for(auto&[n2,ys]:trans(n,xs)) S2.push_back(n2); sort(S2.begin(),S2.end()); S2.erase(unique(S2.begin(),S2.end()),S2.end());
        TK k2=make_pair(make_pair(qx2,ps2),S2); if(!seen.count(k2)){ seen[k2]={k,xs}; q.push_back(k2);} } }
    printf("(T) totality: subset states %zu, max subset %zu, violations %ld\n",seen.size(),maxS,viol); if(viol) rc=1; }
  printf(rc?"FAIL\n":"OK: every config of I (single head) completes its segment inside SIGMA without halting, and lands in J.\n");
  return rc;
}
