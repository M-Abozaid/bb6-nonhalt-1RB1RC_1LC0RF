#!/usr/bin/env python3
# Independent verifier for cw100.dfa invariant of M (written from spec only).
import sys, os, itertools
from collections import deque
sys.setrecursionlimit(100000)
NS = 14
import os
MSTR = os.environ.get("MSTR","1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA")

def parse_machine(ms):
    T = {}
    for s, part in enumerate(ms.split('_')):
        for r in range(2):
            t = part[3*r:3*r+3]
            if t[0] == '-': T[(s, r)] = None
            else: T[(s, r)] = (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T
def mirror(T):
    return {k: (None if v is None else (v[0], -v[1], v[2])) for k, v in T.items()}
M = parse_machine(MSTR)
def HL(s, r): return 2 + 2*s + r
def dec(c): return ((c-2)//2, (c-2) % 2)

# ---- load DFA
L = open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'certificate', 'cw100.dfa')).read().split()
n, q0 = int(L[0]), int(L[1]); T = []; ACC = []; k = 2
for q in range(n):
    ACC.append(int(L[k])); T.append([int(v) for v in L[k+1:k+1+NS]]); k += 1+NS
assert k == len(L)
print("DFA states", n, "start", q0)
# reachable / coreachable
reach = {q0}; dq = [q0]
while dq:
    q = dq.pop()
    for a in range(NS):
        p = T[q][a]
        if p >= 0 and p not in reach: reach.add(p); dq.append(p)
rev = [[] for _ in range(n)]
for q in range(n):
    for a in range(NS):
        p = T[q][a]
        if p >= 0: rev[p].append((a, q))
coreach = {q for q in range(n) if ACC[q]}; dq = list(coreach)
while dq:
    p = dq.pop()
    for a, q in rev[p]:
        if q not in coreach: coreach.add(q); dq.append(q)
live = reach & coreach
print("reachable", len(reach), "live", len(live))

# ---- (H) exactly one head letter: product with counter 0,1,2(=>=2)
bad = False; seen = {(q0, 0)}; dq = [(q0, 0)]
while dq:
    q, c = dq.pop()
    if ACC[q] and c != 1: bad = True; print("H FAIL: accepted word with", c, "heads")
    for a in range(NS):
        p = T[q][a]
        if p < 0: continue
        nc = min(2, c + (1 if a >= 2 else 0))
        if (p, nc) not in seen: seen.add((p, nc)); dq.append((p, nc))
print("(H) exactly one head:", "FAILED" if bad else "VERIFIED")

# ---- (P) padding closure
# trailing: for every reachable q, ACC[q] == ACC(delta(q,0))
def acc_(q): return q >= 0 and ACC[q]
ptrail = all(acc_(q) == acc_(T[q][0]) for q in reach)
# leading: L(q0) == L(delta(q0,0)) via pairwise equivalence BFS
def equiv(a, b):
    seen = {(a, b)}; dq = [(a, b)]
    while dq:
        x, y = dq.pop()
        if acc_(x) != acc_(y): return False
        for c in range(NS):
            nx = T[x][c] if x >= 0 else -1; ny = T[y][c] if y >= 0 else -1
            # treat -1 and dead (non-coreachable) states alike
            if nx >= 0 and nx not in coreach: nx = -1
            if ny >= 0 and ny not in coreach: ny = -1
            if (nx, ny) not in seen: seen.add((nx, ny)); dq.append((nx, ny))
    return True
plead = equiv(q0, T[q0][0])
print("(P) trailing-blank closure:", ptrail, " leading-blank closure:", plead)

# ---- (I+T) via transducer image.
# Input automaton given as NFA: starts, delta(q)->list of (a, q'), acc(q), co(q)=q co-reachable
def sweep_image(starts, edges, accf, cof, Mach, tag):
    """Right-moving sweep transducer (for Mach) applied to input NFA.
    Returns (fail_list, image NFA as (states, starts, edges, accs)) over output words."""
    # modes: ('P',) pre-head, ('C',s) carrying state s, ('Q',) post
    fails = []
    ist = {}; ilist = []; iedges = []; iacc = set()
    def gid(x):
        if x not in ist: ist[x] = len(ilist); ilist.append(x); iedges.append([])
        return ist[x]
    st0 = [gid((q, 'P', -1)) for q in starts]
    dq = list(range(len(ilist)))
    extra = 0
    while dq:
        i = dq.pop(); q, mode, s = ilist[i]
        if accf(q):
            # end of input
            if mode == 'Q': iacc.add(i)
            elif mode == 'C':
                # run on blank tape
                out = []; cur = s; seenS = set(); ok = False
                while True:
                    t = Mach[(cur, 0)]
                    if t is None: fails.append((tag, 'halt-on-blank-end', cur)); break
                    if t[1] == -1: out.append(HL(cur, 0)); ok = True; break
                    if cur in seenS: fails.append((tag, 'runs-forever-on-blanks', cur)); break
                    seenS.add(cur); out.append(t[0]); cur = t[2]
                if ok:
                    prev = i
                    for j, a in enumerate(out):
                        nid = gid(('X', extra, j)); iedges[prev].append((a, nid)); prev = nid
                    extra += 1; iacc.add(prev)
            else:
                fails.append((tag, 'accepted word w/o head (pre mode at end)', q))
        for a, q2 in edges(q):
            if not cof(q2): continue
            if mode == 'P':
                if a < 2: nx = (q2, 'P', -1); o = a
                else:
                    t = Mach[dec(a)]
                    if t is None: fails.append((tag, 'halt head letter in I', dec(a))); continue
                    if t[1] != 1: continue      # not this pass's direction
                    o = t[0]; nx = (q2, 'C', t[2])
            elif mode == 'C':
                if a >= 2: fails.append((tag, 'second head letter', a)); continue
                t = Mach[(s, a)]
                if t is None: fails.append((tag, 'halt during sweep', (s, a))); continue
                if t[1] == 1: o = t[0]; nx = (q2, 'C', t[2])
                else: o = HL(s, a); nx = (q2, 'Q', -1)
            else:
                if a >= 2: fails.append((tag, 'second head letter', a)); continue
                o = a; nx = (q2, 'Q', -1)
            new = nx not in ist; j = gid(nx); iedges[i].append((o, j))
            if new: dq.append(j)
    return fails, (len(ilist), st0, iedges, iacc)

def included_in_I(nst, starts, edges, accs, reverse):
    """check L(NFA) (reversed if reverse) subset of L(DFA I)"""
    if reverse:
        redg = [[] for _ in range(nst)]
        for i in range(nst):
            for a, j in edges[i]: redg[j].append((a, i))
        starts, accs, edges = list(accs), set(starts), redg
    seen = set(); dq = []
    for s in starts:
        x = (s, q0); seen.add(x); dq.append(x)
    while dq:
        i, q = dq.pop()
        if i in accs and not acc_(q): return False, (i, q)
        for a, j in edges[i]:
            p = T[q][a] if q >= 0 else -1
            if (j, p) not in seen: seen.add((j, p)); dq.append((j, p))
    return True, len(seen)

# Right pass: input = I itself (DFA), left-to-right
fR, imgR = sweep_image([q0], lambda q: [(a, T[q][a]) for a in range(NS) if T[q][a] >= 0],
                       lambda q: bool(ACC[q]), lambda q: q in coreach, M, 'R')
okR = included_in_I(imgR[0], imgR[1], imgR[2], imgR[3], False)
print("Right-sweep pass: fails", len(fR), fR[:5], "image states", imgR[0], "image in I:", okR)
# Left pass: input = reverse(I) as NFA (starts=accepting, edges reversed), mirrored machine
fL, imgL = sweep_image([q for q in range(n) if ACC[q]], lambda q: rev[q],
                       lambda q: q == q0, lambda q: q in reach, mirror(M), 'L')
okL = included_in_I(imgL[0], imgL[1], imgL[2], imgL[3], True)
print("Left-sweep pass: fails", len(fL), fL[:5], "image states", imgL[0], "image in I:", okL)
print("(I+T):", "VERIFIED" if not fR and not fL and okR[0] and okL[0] else "FAILED")
