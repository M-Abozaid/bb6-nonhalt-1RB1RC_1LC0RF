/-! Generic two-symbol Turing machines (bbchallenge semantics).
Tape: `L` = cells left of the head (nearest first), `h` = scanned cell, `R` = cells right of
the head (nearest first); cells beyond the lists are blank (`false`).
A machine maps (state, read) to `some (write, moveRight, next)` or `none` (undefined = halt). -/
namespace Cert

abbrev Machine := Nat → Bool → Option (Bool × Bool × Nat)

structure Cfg where
  q : Nat
  L : List Bool
  h : Bool
  R : List Bool
  deriving DecidableEq, Repr

def halted (M : Machine) (c : Cfg) : Prop := M c.q c.h = none

instance (M : Machine) (c : Cfg) : Decidable (halted M c) :=
  inferInstanceAs (Decidable (M c.q c.h = none))

/-- One step; a halted configuration is left unchanged. -/
def step (M : Machine) (c : Cfg) : Cfg :=
  match M c.q c.h with
  | none => c
  | some (w, true, s) => ⟨s, w :: c.L, c.R.headD false, c.R.tail⟩
  | some (w, false, s) => ⟨s, c.L.tail, c.L.headD false, w :: c.R⟩

def run (M : Machine) : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => run M n (step M c)

/-- blank tape, state `q` -/
def blank (q : Nat) : Cfg := ⟨q, [], false, []⟩

theorem run_add (M : Machine) (m n : Nat) (c : Cfg) :
    run M (m + n) c = run M n (run M m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => rw [Nat.succ_add]; simp only [run]; exact ih _

theorem run_succ' (M : Machine) (n : Nat) (c : Cfg) : run M (n + 1) c = step M (run M n c) := by
  rw [run_add]; rfl

theorem step_of_halted {M : Machine} {c : Cfg} (h : halted M c) : step M c = c := by
  unfold halted at h; simp [step, h]

theorem run_of_halted {M : Machine} {c : Cfg} (h : halted M c) : ∀ n, run M n c = c := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp only [run, step_of_halted h, ih]

/-- once halted, stays halted -/
theorem halted_mono {M : Machine} {c : Cfg} {n n' : Nat} (hn : n ≤ n')
    (h : halted M (run M n c)) : halted M (run M n' c) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [run_add, run_of_halted h]; exact h

/-! ## Tapes up to trailing blanks -/

/-- drop trailing blanks -/
def strip : List Bool → List Bool
  | [] => []
  | x :: xs => let t := strip xs; if x = false ∧ t = [] then [] else x :: t

def eqv (x y : List Bool) : Prop := strip x = strip y

theorem strip_headD (x : List Bool) : (strip x).headD false = x.headD false := by
  cases x with
  | nil => rfl
  | cons r rs => simp only [strip]; split <;> simp_all

theorem strip_tail (x : List Bool) : (strip x).tail = strip x.tail := by
  cases x with
  | nil => rfl
  | cons r rs => simp only [strip, List.tail_cons]; split <;> simp_all

theorem eqv_headD {x y : List Bool} (h : eqv x y) : x.headD false = y.headD false := by
  rw [← strip_headD x, h, strip_headD]

theorem eqv_tail {x y : List Bool} (h : eqv x y) : eqv x.tail y.tail := by
  unfold eqv; rw [← strip_tail, ← strip_tail, h]

theorem eqv_cons {x y : List Bool} (w : Bool) (h : eqv x y) : eqv (w :: x) (w :: y) := by
  unfold eqv at *; simp only [strip, h]

theorem eqv_headD_tail (R : List Bool) : eqv (R.headD false :: R.tail) R := by
  cases R with
  | nil => rfl
  | cons r rs => rfl

theorem eqv_cons_inv {h a : Bool} {R z : List Bool} (e : eqv (h :: R) (a :: z)) :
    h = a ∧ eqv R z := by
  have e1 := eqv_headD e; have e2 := eqv_tail e
  simp at e1 e2; exact ⟨e1, e2⟩

theorem eqv_cons_nil {h : Bool} {R : List Bool} (e : eqv (h :: R) []) : h = false ∧ eqv R [] := by
  have e1 := eqv_headD e; have e2 := eqv_tail e
  simp at e1 e2; exact ⟨e1, e2⟩

theorem strip_strip (x : List Bool) : strip (strip x) = strip x := by
  induction x with
  | nil => rfl
  | cons b ys ih =>
    by_cases hc : b = false ∧ strip ys = []
    · simp only [strip, hc, and_self, if_true]
    · simp only [strip, hc, if_false, ih]

theorem strip_append (x y : List Bool) : strip (x ++ y) = strip (x ++ strip y) := by
  induction x with
  | nil => simp [strip_strip]
  | cons b xs ih => simp only [List.cons_append, strip, ih]

theorem strip_replicate (k : Nat) : strip (List.replicate k false) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, strip, ih]

theorem eqv_pad (x : List Bool) (k : Nat) : eqv (x ++ List.replicate k false) x := by
  unfold eqv; rw [strip_append, strip_replicate, List.append_nil]

theorem eqv_append {x y y' : List Bool} (h : eqv y y') : eqv (x ++ y) (x ++ y') := by
  unfold eqv at *; rw [strip_append, h, ← strip_append]

theorem eqv_strip (x : List Bool) : eqv (strip x) x := strip_strip x

/-- configurations equal up to trailing blanks on both sides -/
def eqvC (c d : Cfg) : Prop := c.q = d.q ∧ c.h = d.h ∧ eqv c.L d.L ∧ eqv c.R d.R

instance (c d : Cfg) : Decidable (eqvC c d) := by unfold eqvC eqv; infer_instance

theorem eqvC_trans {c d e : Cfg} (h1 : eqvC c d) (h2 : eqvC d e) : eqvC c e := by
  obtain ⟨a1, b1, c1, d1⟩ := h1; obtain ⟨a2, b2, c2, d2⟩ := h2
  exact ⟨a1.trans a2, b1.trans b2, Eq.trans c1 c2, Eq.trans d1 d2⟩

theorem step_eqvC (M : Machine) {c d : Cfg} (h : eqvC c d) : eqvC (step M c) (step M d) := by
  obtain ⟨q, L, x, R⟩ := c
  obtain ⟨q', L', x', R'⟩ := d
  obtain ⟨hq, hh, hL, hR⟩ := h
  simp only at hq hh; subst hq; subst hh
  unfold step
  cases M q x with
  | none => exact ⟨rfl, rfl, hL, hR⟩
  | some t =>
    obtain ⟨w, d, s⟩ := t
    cases d
    · exact ⟨rfl, eqv_headD hL, eqv_tail hL, eqv_cons _ hR⟩
    · exact ⟨rfl, eqv_headD hR, eqv_cons _ hL, eqv_tail hR⟩

theorem run_eqvC (M : Machine) (n : Nat) : ∀ {c d : Cfg}, eqvC c d → eqvC (run M n c) (run M n d) := by
  induction n with
  | zero => intro c d h; exact h
  | succ n ih => intro c d h; exact ih (step_eqvC M h)

/-! ## Mirror + state renaming -/

/-- mirror image (swap left and right) with states renamed by `π` -/
def mir (π : Nat → Nat) (c : Cfg) : Cfg := ⟨π c.q, c.R, c.h, c.L⟩

/-- `N` is the mirror image of `M` under renaming `π` -/
def IsMirror (π : Nat → Nat) (M N : Machine) : Prop :=
  ∀ q h, N (π q) h = (M q h).map (fun t => (t.1, !t.2.1, π t.2.2))

theorem step_mir {π : Nat → Nat} {M N : Machine} (hm : IsMirror π M N) (c : Cfg) :
    step N (mir π c) = mir π (step M c) := by
  obtain ⟨q, L, x, R⟩ := c
  unfold step mir; simp only [hm q x]
  cases hM : M q x with
  | none => rfl
  | some t =>
    obtain ⟨w, d, s⟩ := t
    cases d <;> rfl

theorem run_mir {π : Nat → Nat} {M N : Machine} (hm : IsMirror π M N) (n : Nat) (c : Cfg) :
    run N n (mir π c) = mir π (run M n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [run, step_mir hm, ih]

theorem halted_mir {π : Nat → Nat} {M N : Machine} (hm : IsMirror π M N) (c : Cfg) :
    halted N (mir π c) ↔ halted M c := by
  unfold halted mir; simp only [hm c.q c.h]; cases M c.q c.h <;> simp

end Cert
