import M23.Frame

namespace M23
open List

/-! ## Body patterns (all as lists, nearest cell first).
* `U = [1,1,0]` : body unit on the right list at a checkpoint / before a right sweep
* `X = [0,0,1]` : unit left behind by the right sweep (on the left list)
* `Y = [1,0,0]` : the same cells re-phased, as the left sweep sees them
* `Z = [1,0,1]` : unit left behind by the left sweep (on the right list) -/
abbrev X : List Bool := [false, false, true]
abbrev Y : List Bool := [true, false, false]
abbrev Z : List Bool := [true, false, true]

/-- rotation: `x :: (l ++ [x])^k = (x :: l)^k ++ [x]` -/
theorem rot (x : Bool) (l : List Bool) (k : Nat) (T : List Bool) :
    x :: (pw k (l ++ [x]) ++ T) = pw k (x :: l) ++ x :: T := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]

theorem rotX (k : Nat) (T : List Bool) : true :: (pw k X ++ T) = pw k Y ++ true :: T :=
  rot true [false, false] k T

theorem rotZ (k : Nat) (T : List Bool) : true :: (pw k Z ++ T) = pw k U ++ true :: T :=
  rot true [true, false] k T

theorem splitZ (k : Nat) (T : List Bool) :
    pw (k + 1) Z ++ T = true :: false :: (pw k U ++ true :: T) := by
  rw [pw_succ, ← rotZ]; simp

/-! ## Right sweep: state A turns `(11.)^k` into `(1..)^k` (3 steps per unit), any tape. -/
theorem rsweep (k : Nat) (L R : List Bool) :
    run (3 * k) ⟨.A, L, false, pw k U ++ R⟩ = ⟨.A, pw k X ++ L, false, R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 + 3 * k by omega, run_add]
    have h3 : run 3 ⟨.A, L, false, pw (k + 1) U ++ R⟩ = ⟨.A, X ++ L, false, pw k U ++ R⟩ := by
      simp [run, step, mR]
    rw [h3, ih, pw_succ', append_assoc]

/-! ## Left sweep: state B turns the units back (3 steps per unit), any tape. -/
theorem lsweep (k : Nat) (L R : List Bool) :
    run (3 * k) ⟨.B, pw k Y ++ L, false, R⟩ = ⟨.B, L, false, pw k Z ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 + 3 * k by omega, run_add]
    have h3 : run 3 ⟨.B, pw (k + 1) Y ++ L, false, R⟩ = ⟨.B, pw k Y ++ L, false, Z ++ R⟩ := by
      simp [run, step, mL]
    rw [h3, ih, pw_succ', append_assoc]

/-! ## Fixed boundary segments (word-independent). -/

/-- leave the checkpoint: `C` on the leftmost blank enters the first unit. -/
theorem start (R : List Bool) :
    run 3 ⟨.C, [], false, U ++ R⟩ = ⟨.A, [false, true, true], false, R⟩ := by
  simp [run, step, mR]

/-- first bounce: the right sweep hits the word's leading `0`, writes it to `1` and turns. -/
theorem bounce1 (L W' : List Bool) :
    run 4 ⟨.A, X ++ L, false, false :: W'⟩ = ⟨.B, true :: L, false, Z ++ W'⟩ := by
  simp [run, step, mR, mL]

/-- left end, first round trip: turn without growing the tape. -/
theorem leftEnd1 (R : List Bool) :
    run 5 ⟨.B, [true, false, true, true], false, true :: false :: R⟩
      = ⟨.A, [false, false, true], false, U ++ R⟩ := by
  simp [run, step, mR, mL]

/-- left end, second round trip: grow the tape by 3 cells and reach the next checkpoint. -/
theorem leftEnd2 (R : List Bool) :
    run 4 ⟨.B, [true], false, R⟩ = ⟨.C, [], false, U ++ true :: R⟩ := by
  simp [run, step, mR, mL]

end M23
