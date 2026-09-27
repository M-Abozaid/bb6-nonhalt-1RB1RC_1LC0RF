#!/usr/bin/env python3
# Check that the DFA string embedded in the Lean proof (lean/cert/Cert/Data.lean) is byte-identical
# to certificate/cw100.dfa, so the Lean theorem and the C++/Python checks are about the same certificate.
import os, re, sys, hashlib
H = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(H, '..', 'lean', 'cert', 'Cert', 'Data.lean')).read()
m = re.search(r'def cw100 : String := "((?:[^"\\]|\\.)*)"', src, re.S)
s = m.group(1).replace('\\n', '\n')
assert '\\' not in s
f = open(os.path.join(H, '..', 'certificate', 'cw100.dfa')).read()
ok = s == f
print("Data.lean string sha256", hashlib.sha256(s.encode()).hexdigest())
print("cw100.dfa        sha256", hashlib.sha256(f.encode()).hexdigest())
print("MATCH" if ok else "MISMATCH"); sys.exit(0 if ok else 1)
