#!/usr/bin/env python3
# Check that configuration strings are accepted by the certificate DFA.
# Config text: '.'=0, '1'=1, head letter 'A'..'F' (state, reading 0) or 'a'..'f' (state, reading 1).
# usage: python3 inlang.py DFA conf1.txt [conf2.txt ...]
import sys
NS = 14
def load(fn):
    L = open(fn).read().split(); n, q0 = int(L[0]), int(L[1]); T, ACC, k = [], [], 2
    for q in range(n):
        ACC.append(int(L[k])); T.append([int(v) for v in L[k+1:k+1+NS]]); k += 1 + NS
    assert k == len(L); return q0, T, ACC
def code(ch):
    if ch == '.': return 0
    if ch == '1': return 1
    if 'A' <= ch <= 'F': return 2 + 2*(ord(ch) - 65)
    if 'a' <= ch <= 'f': return 3 + 2*(ord(ch) - 97)
    raise ValueError(ch)
q0, T, ACC = load(sys.argv[1]); allok = True
for fn in sys.argv[2:]:
    s = open(fn).read().strip(); w = [code(c) for c in s]
    heads = [i for i, c in enumerate(w) if c >= 2]
    q = q0
    for c in w:
        q = T[q][c]
        if q < 0: break
    ok = q >= 0 and ACC[q] == 1 and len(heads) == 1
    allok &= ok
    print(f"{fn}: {len(w)} cells, head '{s[heads[0]]}' at {heads[0]}, ones {s.count('1')+s.count('a')+s.count('b')+s.count('c')+s.count('d')+s.count('e')+s.count('f')}: {'ACCEPTED' if ok else 'REJECTED'}")
sys.exit(0 if allok else 1)
