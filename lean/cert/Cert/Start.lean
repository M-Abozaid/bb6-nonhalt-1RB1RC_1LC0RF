import Cert.Machines
import Cert.DFA
import M23
/-! Start-configuration reachability via the (previously proven) event acceleration of `M23`:
`M23.event_map` turns one checkpoint into the next in closed form for ANY body length, with the
word-dependent part computed by `M23.wordMap` (proved sound there). -/
namespace Cert

/-- bridge from the `M23` encoding (`H` = halted, only ever entered from `E0`) -/
def stIdx : M23.St → Nat
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5 | .H => 4

def fC (c : M23.Cfg) : Cfg := ⟨stIdx c.st, c.L, c.h, c.R⟩

def goodC (c : M23.Cfg) : Prop := c.st = .H → c.h = false

theorem step_f (c : M23.Cfg) (hg : goodC c) :
    fC (M23.step c) = step M (fC c) ∧ goodC (M23.step c) := by
  obtain ⟨s, L, x, R⟩ := c
  unfold goodC at *
  cases s <;> cases x <;> simp_all [M23.step, M23.mR, M23.mL, step, M, fC, stIdx]

theorem run_f (n : Nat) : ∀ (c : M23.Cfg), goodC c → fC (M23.run n c) = run M n (fC c) := by
  induction n with
  | zero => intro c _; rfl
  | succ n ih =>
    intro c hg
    obtain ⟨h1, h2⟩ := step_f c hg
    simp only [M23.run, run]; rw [ih _ h2, h1]

/-- checkpoint: `C` on the leftmost blank, `n` units `11.`, then word `W` -/
def ck (n : Nat) (W : List Bool) : Cfg := ⟨2, [], false, M23.pw n M23.U ++ W⟩

theorem ck_f (n : Nat) (W : List Bool) : fC (M23.ckpt n W) = ck n W := rfl

/-- greedy strip of leading units -/
def units : List Bool → Nat × List Bool
  | true :: true :: false :: r => let p := units r; (p.1 + 1, p.2)
  | l => (0, l)

theorem units_spec (l : List Bool) : M23.pw (units l).1 M23.U ++ (units l).2 = l := by
  induction l using units.induct with
  | case1 r ih => simp only [units, M23.pw_succ, List.append_assoc, ih]; rfl
  | case2 l h => unfold units; split
                 · rename_i r; exact absurd rfl (h r)
                 · rfl

def PAD : Nat := 40

def evStep (p : Nat × List Bool) : Option (Nat × List Bool) :=
  match p.2 with
  | false :: W' =>
    if 2 ≤ p.1 then
      match M23.wordMap 3000 (W' ++ List.replicate PAD false) with
      | some (_, J', V) => some (J' + (p.1 - 2) + 1 + (units (true :: V)).1,
                                strip (units (true :: V)).2)
      | none => none
    else none
  | _ => none

theorem eqvC_refl (c : Cfg) : eqvC c c := ⟨rfl, rfl, rfl, rfl⟩

theorem evStep_sound {p p' : Nat × List Bool} (h : evStep p = some p') :
    ∃ m, eqvC (run M m (ck p.1 p.2)) (ck p'.1 p'.2) := by
  obtain ⟨n, W⟩ := p
  rcases W with _ | ⟨b, W'⟩
  · simp [evStep] at h
  cases b
  case true => simp [evStep] at h
  by_cases hn : 2 ≤ n
  case neg => simp [evStep, hn] at h
  cases hw : M23.wordMap 3000 (W' ++ List.replicate PAD false) with
  | none => simp [evStep, hn, hw] at h
  | some r =>
    obtain ⟨a, J', V⟩ := r
    simp only [evStep, hn, if_true, hw, Option.some.injEq] at h
    subst h
    exact aux n W' a J' V hn hw
where
  aux (n : Nat) (W' : List Bool) (a J' : Nat) (V : List Bool) (hn : 2 ≤ n)
      (hw : M23.wordMap 3000 (W' ++ List.replicate PAD false) = some (a, J', V)) :
      ∃ m, eqvC (run M m (ck n (false :: W')))
        (ck (J' + (n - 2) + 1 + (units (true :: V)).1) (strip (units (true :: V)).2)) := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        have ev := M23.event_map k 3000 a J' (W' ++ List.replicate PAD false) V hw
        have hr := run_f (M23.evSteps k a (J' + k)) (M23.ckpt (k + 2) (false :: (W' ++ List.replicate PAD false))) (by unfold goodC M23.ckpt; intro h; cases h)
        rw [ev, ck_f, ck_f] at hr
        refine ⟨M23.evSteps k a (J' + k), ?_⟩
        have e1 : eqvC (ck (k + 2) (false :: W'))
            (ck (k + 2) (false :: (W' ++ List.replicate PAD false))) := by
          refine ⟨rfl, rfl, rfl, ?_⟩
          show eqv _ _
          apply eqv_append
          show strip _ = strip _
          rw [← List.cons_append]; exact (eqv_pad _ _).symm
        have e2 := run_eqvC M (M23.evSteps k a (J' + k)) e1
        rw [← hr] at e2
        refine eqvC_trans e2 ⟨rfl, rfl, rfl, ?_⟩
        show eqv _ _
        have hu := units_spec (true :: V)
        simp only [ck]
        rw [show k + 2 - 2 = k by omega]
        have e3 : M23.pw (J' + k + 1) M23.U ++ (true :: V)
            = M23.pw (J' + k + 1 + (units (true :: V)).1) M23.U ++ (units (true :: V)).2 := by
          rw [M23.pw_add (J' + k + 1), List.append_assoc, hu]
        rw [e3]
        exact eqv_append (eqv_strip _).symm

def evIter : Nat → Nat × List Bool → Option (Nat × List Bool)
  | 0, p => some p
  | k + 1, p => (evStep p).bind (evIter k)

theorem evIter_sound (k : Nat) : ∀ {p p' : Nat × List Bool}, evIter k p = some p' →
    ∃ m, eqvC (run M m (ck p.1 p.2)) (ck p'.1 p'.2) := by
  induction k with
  | zero => intro p p' h; simp [evIter] at h; subst h; exact ⟨0, eqvC_refl _⟩
  | succ k ih =>
    intro p p' h
    simp only [evIter, Option.bind_eq_some_iff] at h
    obtain ⟨p1, h1, h2⟩ := h
    obtain ⟨m1, e1⟩ := evStep_sound h1
    obtain ⟨m2, e2⟩ := ih h2
    exact ⟨m1 + m2, by rw [run_add]; exact eqvC_trans (run_eqvC M m2 e1) e2⟩

/-- the start certificate: a direct prefix of `m0` steps from blank state `q` to a checkpoint,
then `K` events, landing on a checkpoint whose word is accepted by `D` -/
def startOK (D : DFA) (q m0 n0 : Nat) (W0 : List Bool) (K : Nat) : Bool :=
  decide (eqvC (run M m0 (blank q)) (ck n0 W0)) &&
  match evIter K (n0, W0) with
  | some (n, W) => D.acc (D.run D.q0 (HL 2 false :: (M23.pw n M23.U ++ W).map b2n))
  | none => false

theorem startOK_sound {D : DFA} {q m0 n0 : Nat} {W0 : List Bool} {K : Nat}
    (h : startOK D q m0 n0 W0 K = true) : ∃ m, Inv D (run M m (blank q)) := by
  simp only [startOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  split at h1
  · rename_i n W hk
    obtain ⟨m, e⟩ := evIter_sound K hk
    refine ⟨m0 + m, ?_⟩
    rw [run_add]
    refine Inv_of_eqvC (eqvC_trans (run_eqvC M m h0) e) ⟨[], M23.pw n M23.U ++ W, rfl, rfl, ?_⟩
    exact h1
  · cases h1

end Cert
