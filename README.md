# Nonhalting proof: BB(6) holdouts `1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA` and its mirror

## Result

Neither machine halts when started on the blank tape:

| | machine | start |
|---|---|---|
| **M** | `1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA` | state A |
| **N** | `1RB0RA_1RC0LE_1LD0RA_---1LE_0RE0LF_1LB1LC` | state A |

Both are in the bbchallenge BB(6) holdout list of 2026-09-24 (815 classes). M's equivalence class also
contains `1RB0LD_1LC0RF_---1LD_0RD0LE_1LA1LB_1RA0RF`.

Three independent verifications are included: a C++ checker, a Python checker written from the spec
alone, and a Lean 4 proof (`Cert.nonhalt`, `Cert.nonhalt_N`). The Lean proof has no hypotheses and no
`sorry`. Its trust base is the Lean kernel plus three `native_decide` evaluations.

## How the machine behaves

M is a bouncer with a growing counter. At each checkpoint the head is in state C on the leftmost blank,
and the tape reads `(11.)^n W`. One event is two round trips. The left edge advances by 3 cells, n grows
to about 2e after e events, and the step count grows to about 12e². `W` is a short word on a period-3
background that works like a lazy decimal counter, and its length grows as about log e. M can halt only
through E0, and E is entered only from C0. So M halts only if the right-going B→F→A cycle over the
`11.` units meets a `111..` in the wrong phase. The certificate shows that this never happens.

## Method: a regular language closed under sweeps

A configuration is a word over 14 letters: `0`, `1`, and one head letter `2+2s+b` (state s, reading b).
A **sweep** is a maximal run of steps in the same direction. It ends at the first configuration whose next
move reverses direction. The certificate `certificate/cw100.dfa` is a DFA with 3,495 states. Its
language I is a set of configurations. The checkers verify four properties:

- **(H)** every word in I has exactly one head letter.
- **(P)** I is closed under blank padding: 0·I ⊆ I and I·0 ⊆ I. So I describes tapes, not strings.
- **(T) totality:** from every c ∈ I, the sweep ends after finitely many steps without halting. It also
  never walks off into blank tape forever (for example, F0 moving left). Such a walk counts as a failure.
- **(I) image closure:** the configuration at the end of that sweep is again in I.

If I contains a configuration that M reaches from blank, then by induction M's run is an infinite chain of
finite sweeps, and M never halts.

**Soundness of the C++ checker (crossing-sequence matching).** `gcs` labels each cell boundary with a
crossing sequence. Within one sweep a boundary is crossed at most once, so K=1 suffices. It also runs a
local simulation for each cell that consumes the crossings on its two sides. The simulation must match
entries and exits by (direction, state). It forbids halting visits. It stops at the first visit where the
sweep reverses, and that visit must consume every crossing. The proof of the matching lemma is by
induction on real time. The invariant is that each boundary's real crossings so far are a common prefix of
its labelled sequence, and each cell not under the head waits on the head's side. The lemma then says an
accepted labelling is exactly the real run. The run stays inside the segment and reaches the end visit,
and the final cell contents are the local final contents. This makes the labelling unique, and the image is
the real end configuration. With at least 4 blanks on each side, a missing labelling means a real halt or
an endless walk into blanks. Both count as failures, so the check is conservative, and (P) makes the
padding harmless. The C++ checker computes (I) and (T) as an NFA product and a subset construction
over the DFA.

**The Python checker and the Lean proof** use a different method. They model a right sweep as a
finite transducer applied to the DFA and check that the image language is included in I. Left sweeps are
the same check on the reversed language with the mirrored machine.

## Reaching the language from the blank tape

- **M from state A.** Direct simulation reaches a checkpoint after **37,052,378,806 steps** with no
  halt. That configuration is in I. The file is `checker_cpp/startconf.txt`: 333,403 cells, 4 blanks
  of padding on each side, head `C` reading 0.
- **M from state D.** The checkpoint comes after 37,051,045,206 steps. The file is
  `checker_cpp/startconfD.txt`, also in I.
- **Lean.** The Lean proof does not replay 3.7·10¹⁰ steps. It runs 79 direct steps (159 from D) and
  then 55,565 events (55,563 from D) using a lemma that jumps one whole event at a time. That lemma is
  proved in `lean/m23` for every body length n.

## The mirror argument

N is M mirrored (L↔R) with the states renamed A→F, B→B, C→C, D→A, E→D, F→E. So N started in A on the
blank tape runs as the mirror image of M started in **D**. N never halts because M never halts from state
D. Lean proves this as `N_mirror_M`, `N_run`, and `N_halted`. Both `startconfD.txt` and `startD_ok` cover
the state-D start.

## Trust base

1. `checker_cpp/gcs.cpp` (about 140 lines) together with the matching lemma above, and `startsim.c` for
   the start configuration.
2. `checker_py/v.py` checks (H), (P), and (I+T) independently. `checker_py/sim.c` independently
   re-simulates the run to the start configurations.
3. The Lean 4 proof (v4.33.1, no Mathlib). `#print axioms` gives only `propext`, `Classical.choice`,
   `Quot.sound`, and the `native_decide` axioms of `B_ok` (all DFA checks for M and for the mirrored
   sweeps), `startA_ok`, and `startD_ok`. `Cert/Data.lean` embeds `cw100.dfa` byte for byte, and
   `checker_py/lean_data_matches.py` checks that.

## Reproduce

These commands need g++/gcc, Python 3 (standard library only), and [elan](https://github.com/leanprover/elan)
for Lean. Timings are from a 32-core x86-64 machine.

```sh
# C++ checker: expect (H) ok, (P) ok, (I) 0 violations, (T) 0 violations, "OK"  (< 1 s)
cd checker_cpp && g++ -O2 -std=c++17 -o gcs gcs.cpp && ./gcs rev ../certificate/cw100.dfa K=1 4

# Start configurations: direct simulation from blank (about 95 s each), output compared to the shipped files
gcc -O2 -o startsim startsim.c
./startsim ../certificate/cw100.dfa 55000 60000 0 foundA.txt && cmp foundA.txt startconf.txt
#   -> checkpoint 55568 step 37052378806 in=1
./startsim ../certificate/cw100.dfa 55000 60000 3 foundD.txt && cmp foundD.txt startconfD.txt
#   -> checkpoint 55567 step 37051045206 in=1

# Python checker: expect (H) VERIFIED, (P) True True, (I+T): VERIFIED  (< 1 s)
cd ../checker_py && python3 v.py
python3 inlang.py ../certificate/cw100.dfa ../checker_cpp/startconf.txt ../checker_cpp/startconfD.txt  # ACCEPTED x2
python3 brute.py ../certificate/cw100.dfa 104   # all 431,041 accepted words of length <= 104: bad 0
python3 rsamp.py                                  # 20,000 uniform random words of length 96..400: bad 0
python3 lean_data_matches.py                      # MATCH
gcc -O2 -o sim sim.c && ./sim 0 200000 ../checker_cpp/startconf.txt   # MATCH ... steps 37052378806

# Lean: builds both packages; about 2.5 min from scratch, most of it B_ok
cd ../lean/cert && lake build && lake env lean Check.lean
```

## Layout

- `certificate/`: `cw100.dfa` and `FORMAT.md`
- `checker_cpp/`: `gcs.cpp`, `startsim.c`, `startconf.txt`, `startconfD.txt`
- `checker_py/`: `v.py`, `inlang.py`, `brute.py`, `rsamp.py`, `lean_data_matches.py`, `sim.c`
- `lean/m23/`: the machine's exact semantics, with body sweeps and event acceleration (`M23.event_map`)
  proved for every n
- `lean/cert/`: the DFA checker and its soundness, the reversed DFA, the start certificates, the mirror
  argument, and `Main.lean`

## SHA-256

See `SHA256SUMS` (check it with `sha256sum -c SHA256SUMS`). Key files:

```
46185e7098ec5dd71e54243f9345f05955f6a22d815037f60f5efa541a258d7c  ./certificate/cw100.dfa
8a6354e4db93a207eefc20d076c0d6b677c9b0c4cfa535443d57806cb9c85841  ./checker_cpp/gcs.cpp
01da487a59ae1799497393bbf6a7e9d0373f045f1fbe238ee669836e0e8dda53  ./checker_cpp/startconfD.txt
5028b0c8c1c57be8b94416865a6e590bff03b44ea92b06eea5e46fc70ca57608  ./checker_cpp/startconf.txt
dd6a0bd4049a82d6063dd8e8a0119a031aca6c27153dc3d335f6e8474a37b7eb  ./checker_cpp/startsim.c
482cff60a5fd9015c7baf9ff158d02ca72b4eec56759d19093d59ba5fe18879e  ./checker_py/v.py
caa83ac161e6f21c19853a8d6ec376edab6cbfbaba032784f7d29b98c8a7884f  ./lean/cert/Cert/Data.lean
56bac1b56259c8185e3b0af2ee6edd88cc29b5f6c5f7dc1556552169c6bf8c10  ./lean/cert/Cert/Main.lean
```
