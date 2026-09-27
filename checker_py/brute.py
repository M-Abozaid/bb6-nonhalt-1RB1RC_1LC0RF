#!/usr/bin/env python3
# Brute-force: all words of I up to length LMAX, direct simulation of one sweep.
# usage: python3 brute.py [DFA] [LMAX=20]
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE, 'v.py')).read().split('# ---- (H)')[0])
rev=[[] for _ in range(n)]
for q in range(n):
    for a in range(NS):
        if T[q][a]>=0: rev[T[q][a]].append((a,q))   # machine + DFA loading only
LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 20
def acceptsw(w):
    q = q0
    for c in w:
        q = T[q][c]
        if q < 0: return False
    return bool(ACC[q])
def sweep(w):
    tape = [0]*8 + list(w) + [0]*8
    h = [i for i, c in enumerate(tape) if c >= 2]; assert len(h) == 1; h = h[0]
    s, r = dec(tape[h]); tape[h] = r
    t = M[(s, r)]
    if t is None: return 'HALT'
    d0 = t[1]; steps = 0
    while True:
        t = M[(s, tape[h])]
        if t is None: return 'HALT'
        if steps > 0 and t[1] != d0: break
        tape[h] = t[0]; h += t[1]; s = t[2]; steps += 1
        if h < 0 or h >= len(tape): return 'RUNOFF'
    tape[h] = HL(s, tape[h])
    return tape
INF=10**9; dist=[INF]*n
from collections import deque
dq=deque()
for q in range(n):
    if ACC[q]: dist[q]=0; dq.append(q)
while dq:
    p=dq.popleft()
    for a,q in rev[p]:
        if dist[q]==INF: dist[q]=dist[p]+1; dq.append(q)
cnt = 0; bad = 0
stack = [(q0, [])]
while stack:
    q, w = stack.pop()
    if ACC[q]:
        cnt += 1
        res = sweep(w)
        if isinstance(res, str) or not acceptsw(res):
            bad += 1
            if bad < 5: print("BAD", w, res if isinstance(res, str) else '')
    if len(w) < LMAX:
        for a in range(NS):
            p = T[q][a]
            if p >= 0 and len(w)+1+dist[p] <= LMAX: stack.append((p, w + [a]))
print("LMAX", LMAX, "words", cnt, "bad", bad)
