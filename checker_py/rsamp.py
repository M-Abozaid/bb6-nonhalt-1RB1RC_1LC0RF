#!/usr/bin/env python3
# Uniform random sampling of accepted words (length 96..400) + direct one-sweep simulation.
# usage: python3 rsamp.py [DFA]
import random, os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'brute.py')).read().split('cnt = 0; bad = 0')[0])
random.seed(1)
# counts of completions: C[l][q] = #words of length l from q accepted
LM=400
C=[[1 if ACC[q] else 0 for q in range(n)]]
for l in range(1,LM+1):
    prev=C[-1]; C.append([sum(prev[T[q][a]] for a in range(NS) if T[q][a]>=0) for q in range(n)])
bad=0; tot=0; hd={}
for it in range(20000):
    l=random.randint(96,LM); q=q0; w=[]
    if C[l][q0]==0: continue
    for i in range(l,0,-1):
        x=random.randrange(C[i][q]); 
        for a in range(NS):
            p=T[q][a]
            if p<0: continue
            if x<C[i-1][p]: w.append(a); q=p; break
            x-=C[i-1][p]
    assert ACC[q]
    tot+=1; res=sweep(w)
    h=[c for c in w if c>=2][0]; hd[h]=hd.get(h,0)+1
    if isinstance(res,str) or not acceptsw(res): bad+=1
print("random samples",tot,"bad",bad,"head letters seen",{ 'ABCDEF'[dec(k)[0]]+str(dec(k)[1]):v for k,v in hd.items()})
