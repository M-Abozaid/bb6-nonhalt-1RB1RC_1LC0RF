import M23.Event

namespace M23
open List

/-! ## The word map as a computable function (fuel-bounded search), with soundness. -/

/-- `some j` iff `L = 1 :: (0 0 1)^j` (left-sweep return form) -/
def isRet : List Bool → Option Nat
  | true :: rest => if rest = pw (rest.length / 3) X then some (rest.length / 3) else none
  | _ => none

theorem isRet_sound {L : List Bool} {j : Nat} (h : isRet L = some j) : L = true :: pw j X := by
  match L, h with
  | true :: rest, h =>
    simp only [isRet] at h
    split at h
    · cases h; rename_i hr; rw [← hr]
    · cases h

/-- Run the bounded window until the first left-sweep return; returns (steps, J', V). -/
def seek : Nat → Cfg → Option (Nat × Nat × List Bool)
  | 0, _ => none
  | f + 1, c =>
    match c.st, c.h, isRet c.L with
    | .B, false, some j => some (0, j, c.R)
    | _, _, _ => (stepB c).bind fun c' => (seek f c').map fun r => (r.1 + 1, r.2)

theorem seek_sound (f : Nat) : ∀ {c : Cfg} {a j : Nat} {V : List Bool},
    seek f c = some (a, j, V) → runB a c = some ⟨.B, true :: pw j X, false, V⟩ := by
  induction f with
  | zero => intro c a j V h; simp [seek] at h
  | succ f ih =>
    intro c a j V h
    obtain ⟨s, L, x, R⟩ := c
    simp only [seek] at h
    split at h
    · rename_i jj hj
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [isRet_sound hj]; rfl
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨c', h1, ⟨a', j', V'⟩, h2, h3⟩ := h
      simp only [Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl, rfl⟩ := h3
      simp only [runB, h1, Option.bind_some]
      exact ih h2

/-- The window used for the word interaction: 2 body units suffice
(checked on all 12,907 real events with `n ≥ 2`, see scratch/Check.lean). -/
def win (W' : List Bool) : Cfg := ⟨.A, pw 2 X, false, true :: W'⟩

/-- `wordMap fuel W'`: (word steps `a`, returned units `J'`, new word tail `V`). -/
def wordMap (fuel : Nat) (W' : List Bool) : Option (Nat × Nat × List Bool) := seek fuel (win W')

/-- **Event theorem, function form.** If the word map of `0 :: W'` is defined, then for every
body length `n = k + 2` the checkpoint `(11.)^n 0 W'` goes in exactly
`evSteps k a (J' + k)` steps to the checkpoint `(11.)^(J' + k + 1) 1 V`. -/
theorem event_map (k fuel a J' : Nat) (W' V : List Bool)
    (h : wordMap fuel W' = some (a, J', V)) :
    run (evSteps k a (J' + k)) (ckpt (k + 2) (false :: W')) = ckpt (J' + k + 1) (true :: V) := by
  have := event k 2 J' a W' V (by omega) (seek_sound fuel h)
  simpa using this

end M23
