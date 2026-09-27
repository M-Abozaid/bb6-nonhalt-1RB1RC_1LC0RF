# cw100.dfa — certificate format

A plain-text deterministic finite automaton over a 14-letter alphabet of tape symbols.

```
n q0                      # number of states, start state
acc t0 t1 ... t13         # one line per state q = 0..n-1
```

- `acc` is 1 if state `q` is accepting, 0 otherwise.
- `tc` is the successor of `q` on letter `c`, or `-1` (no transition = reject).
- `cw100.dfa`: n = 3495, q0 = 0.

## Alphabet

| code | meaning | text form (start configs) |
|------|---------|---------------------------|
| 0 | blank cell | `.` |
| 1 | cell holding 1 | `1` |
| 2 + 2s + b | head in state s (A=0 .. F=5) on a cell holding b | `A`..`F` (b = 0), `a`..`f` (b = 1) |

A word is a finite tape segment, left to right, with exactly one head letter. The language is closed
under adding blanks on either side, so it describes tapes, not strings. The same file, byte for byte, is
embedded as a string in `lean/cert/Cert/Data.lean`; `checker_py/lean_data_matches.py` checks this.
