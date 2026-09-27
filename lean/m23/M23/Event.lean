import M23.Body

namespace M23
open List

/-! ## One event = two round trips, reduced to a bounded word window.

Checkpoint `ckpt n W`: `C` on the leftmost blank, then `(11.)^n`, then the word `W`.
The word always starts with `0` (units are counted greedily), so write `W = 0 :: W'`.

Round trip 1 (word-independent): right sweep, bounce on the word's leading `0` (turned to 1),
left sweep, turn at the left end.  Round trip 2: right sweep up to the word `1 :: W'`, then
the only word-dependent part `wordHyp`, then the left sweep and the left end grows the tape
by 3 cells.  The word part is a `runB` run on an explicit window: `J` body units on the left,
the (blank-padded) word on the right; it must return in left-sweep form. -/

/-- The word interaction of round trip 2, on a finite window: starting with `A` just left
of the word `1 :: W'`, with `J` right-swept units `(1..)^J` to the left, after `a` steps the
machine is in left-sweep form `B` on a blank with left tape `1 (1..)^J'`, word part now `V`. -/
def wordHyp (W' : List Bool) (a J J' : Nat) (V : List Bool) : Prop :=
  runB a ⟨.A, pw J X, false, true :: W'⟩ = some ⟨.B, true :: pw J' X, false, V⟩

/-- steps spent in one event -/
def evSteps (k a m : Nat) : Nat := 3 + 3 * (k + 1) + 4 + 3 * k + 5 + 3 * (k + 1) + a + 3 * m + 4

/-- **Event theorem.** For every body length `n = k + 2 ≥ J`, the body contributes exactly
`3 + 3(k+1) + 4 + 3k + 5 + 3(k+1) + 3m + 4` steps (linear in `n`) and the word part exactly `a`
steps, independent of `n`; the next checkpoint has body `n - J + J' + 1` and word `1 :: V`. -/
theorem event (k J J' a : Nat) (W' V : List Bool) (hJ : J ≤ k + 2)
    (hw : wordHyp W' a J J' V) :
    run (evSteps k a (J' + (k + 2 - J))) (ckpt (k + 2) (false :: W'))
      = ckpt (J' + (k + 2 - J) + 1) (true :: V) := by
  -- round trip 1
  have e1 : run 3 (ckpt (k + 2) (false :: W'))
      = ⟨.A, [false, true, true], false, pw (k + 1) U ++ false :: W'⟩ := by
    rw [ckpt, pw_succ, append_assoc, start]
  have e2 := rsweep (k + 1) [false, true, true] (false :: W')
  have e3 : run 4 ⟨.A, pw (k + 1) X ++ [false, true, true], false, false :: W'⟩
      = ⟨.B, pw k Y ++ [true, false, true, true], false, Z ++ W'⟩ := by
    rw [pw_succ, append_assoc, bounce1, rotX]
  have e4 := lsweep k [true, false, true, true] (Z ++ W')
  have e5 : run 5 ⟨.B, [true, false, true, true], false, pw k Z ++ (Z ++ W')⟩
      = ⟨.A, [false, false, true], false, pw (k + 1) U ++ true :: W'⟩ := by
    rw [← append_assoc, ← pw_succ', splitZ, leftEnd1, pw_succ, append_assoc]
  -- round trip 2
  have e6 := rsweep (k + 1) [false, false, true] (true :: W')
  have e7 : run a ⟨.A, pw (k + 1) X ++ [false, false, true], false, true :: W'⟩
      = ⟨.B, pw (J' + (k + 2 - J)) Y ++ [true], false, V⟩ := by
    have hsplit : pw (k + 1) X ++ [false, false, true] = pw J X ++ pw (k + 2 - J) X := by
      rw [← pw_succ', ← pw_add]; congr 1; omega
    have hf := runB_frame a (pw (k + 2 - J) X) [] hw
    simp only [ext, append_nil] at hf
    rw [hsplit, hf, ← rotX, pw_add, append_nil, cons_append]
  have e8 := lsweep (J' + (k + 2 - J)) [true] V
  have e9 : run 4 ⟨.B, [true], false, pw (J' + (k + 2 - J)) Z ++ V⟩
      = ckpt (J' + (k + 2 - J) + 1) (true :: V) := by
    rw [leftEnd2, rotZ, ckpt, pw_succ, append_assoc]
  simp only [evSteps, run_add]
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]

end M23
