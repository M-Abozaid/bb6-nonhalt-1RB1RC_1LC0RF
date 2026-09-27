import Cert.TM
/-! Regular invariants of configurations and a verified checker for right sweeps.
Letters: 0,1 = cell contents, head letter `HL q h = 2 + 2q + h` (14 letters for 6 states). -/
namespace Cert

def b2n (b : Bool) : Nat := if b then 1 else 0
def HL (q : Nat) (h : Bool) : Nat := 2 + 2 * q + b2n h

/-- total DFA over letters `< 14`; states `≥ n` are the dead state `n` -/
structure DFA where
  n : Nat
  δ : Nat → Nat → Nat
  acc : Nat → Bool
  q0 : Nat
  δ_out : ∀ q a, (n ≤ q ∨ 14 ≤ a) → δ q a = n
  acc_out : ∀ q, n ≤ q → acc q = false

def DFA.run (A : DFA) (q : Nat) : List Nat → Nat
  | [] => q
  | a :: w => A.run (A.δ q a) w

theorem DFA.run_append (A : DFA) (q : Nat) (x y : List Nat) :
    A.run q (x ++ y) = A.run (A.run q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih => exact ih _

theorem DFA.run_out (A : DFA) {q : Nat} (h : A.n ≤ q) (w : List Nat) : A.n ≤ A.run q w := by
  induction w generalizing q with
  | nil => exact h
  | cons a w ih => exact ih (by rw [A.δ_out q a (Or.inl h)]; exact Nat.le_refl _)

theorem DFA.acc_run_out (A : DFA) {q : Nat} (h : A.n ≤ q) (w : List Nat) :
    A.acc (A.run q w) = false := A.acc_out _ (A.run_out h w)

/-- left part of the word: `u` is nearest-first, so reverse it -/
def lw (u : List Bool) : List Nat := u.reverse.map b2n

theorem lw_cons (w : Bool) (u : List Bool) : lw (w :: u) = lw u ++ [b2n w] := by
  simp [lw]

/-- the configuration is described by an accepted word (up to trailing blanks) -/
def Inv (A : DFA) (c : Cfg) : Prop :=
  ∃ u v : List Bool, eqv c.L u ∧ eqv c.R v ∧
    A.acc (A.run A.q0 (lw u ++ HL c.q c.h :: v.map b2n)) = true

theorem Inv_of_eqvC {A : DFA} {c d : Cfg} (e : eqvC c d) (h : Inv A d) : Inv A c := by
  obtain ⟨hq, hh, hL, hR⟩ := e
  obtain ⟨u, v, h1, h2, h3⟩ := h
  exact ⟨u, v, Eq.trans hL h1, Eq.trans hR h2, by rw [hq, hh]; exact h3⟩

/-- no halt strictly before step `k` -/
def NH (M : Machine) (k : Nat) (c : Cfg) : Prop := ∀ j < k, ¬ halted M (run M j c)

theorem NH_succ {M : Machine} {k : Nat} {c : Cfg} (h0 : ¬ halted M c) (h : NH M k (step M c)) :
    NH M (k + 1) c := by
  intro j hj
  cases j with
  | zero => exact h0
  | succ j => exact h j (by omega)

def Good (A : DFA) (M : Machine) (c : Cfg) : Prop := ∃ k, NH M k c ∧ Inv A (run M k c)

/-! ## The checker -/

section
variable (A : DFA) (M : Machine) (co : Nat → Bool)
  (memC : Nat × Nat × Nat → Bool) (memQ : Nat × Nat → Bool)

/-- `co` over-approximates co-reachability -/
def coOK : Bool :=
  (List.range A.n).all fun q =>
    (!A.acc q || co q) && (List.range 14).all fun a => !co (A.δ q a) || co q

/-- run on blanks to the right from state `s` until the first left move; output letters -/
def brun : Nat → Nat → Option (List Nat)
  | 0, _ => none
  | f + 1, s =>
    match M s false with
    | none => none
    | some (w, true, s') => (brun f s').map (b2n w :: ·)
    | some (_, false, _) => some [HL s false]

/-- head letter with a right move: enter carry mode -/
def entryOK : Bool :=
  (List.range A.n).all fun q => (List.range 6).all fun s => [false, true].all fun r =>
    match M s r with
    | some (w, true, s1) => !co (A.δ q (HL s r)) || memC (A.δ q (HL s r), s1, A.δ q (b2n w))
    | _ => true

/-- carry mode: input state, carried machine state, output state -/
def scOK (t : Nat × Nat × Nat) : Bool :=
  (!A.acc t.1 || match brun M 8 t.2.1 with
    | some out => A.acc (A.run t.2.2 out)
    | none => false) &&
  [false, true].all fun a => !co (A.δ t.1 (b2n a)) ||
    match M t.2.1 a with
    | none => false
    | some (w, true, s') => memC (A.δ t.1 (b2n a), s', A.δ t.2.2 (b2n w))
    | some (_, false, _) => memQ (A.δ t.1 (b2n a), A.δ t.2.2 (HL t.2.1 a))

/-- copy mode: language inclusion -/
def sqOK (t : Nat × Nat) : Bool :=
  (!A.acc t.1 || A.acc t.2) &&
  [false, true].all fun a => !co (A.δ t.1 (b2n a)) || memQ (A.δ t.1 (b2n a), A.δ t.2 (b2n a))

def rightOK (SC : List (Nat × Nat × Nat)) (SQ : List (Nat × Nat)) : Bool :=
  coOK A co && entryOK A M co memC && SC.all (scOK A M co memC memQ) && SQ.all (sqOK A co memQ)

/-- halting head letters are not co-reachable -/
def haltOK : Bool :=
  (List.range A.n).all fun q => (List.range 6).all fun s => [false, true].all fun r =>
    match M s r with
    | none => !co (A.δ q (HL s r))
    | _ => true
end

/-! ## Soundness -/

theorem co_sound {A : DFA} {co : Nat → Bool} (h : coOK A co = true) :
    ∀ (z : List Nat) (q : Nat), A.acc (A.run q z) = true → co q = true := by
  simp only [coOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  intro z
  induction z with
  | nil =>
    intro q hq
    have hn : q < A.n := by
      apply Classical.byContradiction; intro hn
      simp [DFA.run, A.acc_out q (by omega)] at hq
    rcases (h q hn).1 with h1 | h1
    · simp [DFA.run, h1] at hq
    · exact h1
  | cons a z ih =>
    intro q hq
    have h1 := ih _ hq
    by_cases hn : q < A.n ∧ a < 14
    · rcases (h q hn.1).2 a hn.2 with h2 | h2
      · rw [h1] at h2; cases h2
      · exact h2
    · have hd : A.δ q a = A.n := A.δ_out q a (by omega)
      simp only [DFA.run, hd, A.acc_run_out (Nat.le_refl _)] at hq
      cases hq

theorem acc_lt {A : DFA} {q : Nat} {w : List Nat} (h : A.acc (A.run q w) = true) : q < A.n := by
  apply Classical.byContradiction; intro hn
  rw [A.acc_run_out (by omega)] at h; cases h

section
variable {A : DFA} {M : Machine} {co : Nat → Bool}
  {memC : Nat × Nat × Nat → Bool} {memQ : Nat × Nat → Bool}
  {SC : List (Nat × Nat × Nat)} {SQ : List (Nat × Nat)}

theorem Q_sound (hco : coOK A co = true) (hQ : ∀ t ∈ SQ, sqOK A co memQ t = true)
    (hmQ : ∀ t, memQ t = true → t ∈ SQ) :
    ∀ (z : List Bool) (qi qo : Nat), (qi, qo) ∈ SQ →
      A.acc (A.run qi (z.map b2n)) = true → A.acc (A.run qo (z.map b2n)) = true := by
  intro z
  induction z with
  | nil =>
    intro qi qo hm ha
    have := hQ _ hm
    simp only [sqOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this.1 with h | h
    · simp [DFA.run, h] at ha
    · exact h
  | cons a z ih =>
    intro qi qo hm ha
    have := hQ _ hm
    simp only [sqOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at this
    have hc : co (A.δ qi (b2n a)) = true := co_sound hco (z.map b2n) _ ha
    rcases this.2 a (by cases a <;> simp) with h | h
    · rw [hc] at h; cases h
    · exact ih _ _ (hmQ _ h) ha

theorem brun_sound :
    ∀ (f s : Nat) (out : List Nat), brun M f s = some out →
      ∀ (c : Cfg) (u : List Bool), c.q = s → c.h = false → eqv c.R [] → eqv c.L u →
        A.acc (A.run (A.run A.q0 (lw u)) out) = true → Good A M c := by
  intro f
  induction f with
  | zero => intro s out h; simp [brun] at h
  | succ f ih =>
    intro s out hb c u hq hh hR hL ha
    simp only [brun] at hb
    cases hMs : M s false with
    | none => rw [hMs] at hb; cases hb
    | some t =>
      obtain ⟨w, d, s'⟩ := t
      rw [hMs] at hb
      cases d with
      | false =>
        simp only [Option.some.injEq] at hb; subst hb
        refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), u, [], hL, hR, ?_⟩
        simp only [run, List.map_nil]
        rw [hq, hh]; rw [DFA.run_append] at *; exact ha
      | true =>
        simp only [Option.map_eq_some_iff] at hb
        obtain ⟨out', hb', rfl⟩ := hb
        have hst : step M c = ⟨s', w :: c.L, c.R.headD false, c.R.tail⟩ := by
          unfold step; rw [hq, hh, hMs]
        have hR' := eqv_cons_nil (Eq.trans (eqv_headD_tail c.R) hR)
        obtain ⟨k, hk, hi⟩ := ih s' out' hb' (step M c) (w :: u) (by rw [hst])
          (by rw [hst]; exact hR'.1) (by rw [hst]; exact hR'.2)
          (by rw [hst]; exact eqv_cons w hL)
          (by rw [lw_cons, DFA.run_append]; exact ha)
        refine ⟨k + 1, NH_succ ?_ hk, hi⟩
        unfold halted; rw [hq, hh, hMs]; simp

theorem sweep_sound (hco : coOK A co = true)
    (hC : ∀ t ∈ SC, scOK A M co memC memQ t = true) (hmC : ∀ t, memC t = true → t ∈ SC)
    (hQ : ∀ t ∈ SQ, sqOK A co memQ t = true) (hmQ : ∀ t, memQ t = true → t ∈ SQ) :
    ∀ (z : List Bool) (qi s qo : Nat) (c : Cfg) (u : List Bool), (qi, s, qo) ∈ SC →
      A.acc (A.run qi (z.map b2n)) = true → c.q = s → eqv (c.h :: c.R) z → eqv c.L u →
      A.run A.q0 (lw u) = qo → Good A M c := by
  intro z
  induction z with
  | nil =>
    intro qi s qo c u hm ha hq he hL hqo
    have := hC _ hm
    simp only [scOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨h1, -⟩ := this
    rcases h1 with h1 | h1
    · simp [DFA.run, h1] at ha
    · have he' := eqv_cons_nil he
      cases hb : brun M 8 s with
      | none => simp [hb] at h1
      | some out =>
        simp only [hb] at h1
        exact brun_sound 8 s out hb c u hq he'.1 he'.2 hL (by rw [hqo]; exact h1)
  | cons a z ih =>
    intro qi s qo c u hm ha hq he hL hqo
    have := hC _ hm
    simp only [scOK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at this
    have hc : co (A.δ qi (b2n a)) = true := co_sound hco (z.map b2n) _ ha
    obtain ⟨hha, hRz⟩ := eqv_cons_inv he
    rcases this.2 a (by cases a <;> simp) with h | h
    · rw [hc] at h; cases h
    · cases hMs : M s a with
      | none => simp [hMs] at h
      | some t =>
        obtain ⟨w, d, s'⟩ := t
        simp only [hMs] at h
        cases d with
        | false =>
          refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), u, z, hL, hRz, ?_⟩
          simp only [run]
          rw [hq, hha, DFA.run_append, hqo]
          exact Q_sound hco hQ hmQ z _ _ (hmQ _ h) ha
        | true =>
          have hst : step M c = ⟨s', w :: c.L, c.R.headD false, c.R.tail⟩ := by
            unfold step; rw [hq, hha, hMs]
          obtain ⟨k, hk, hi⟩ := ih _ s' _ (step M c) (w :: u) (hmC _ h) ha (by rw [hst])
            (by rw [hst]; exact Eq.trans (eqv_headD_tail c.R) hRz)
            (by rw [hst]; exact eqv_cons w hL)
            (by rw [lw_cons, DFA.run_append, hqo]; rfl)
          refine ⟨k + 1, NH_succ ?_ hk, hi⟩
          unfold halted; rw [hq, hha, hMs]; simp

theorem head_lt {c : Cfg} {u v : List Bool}
    (h : A.acc (A.run A.q0 (lw u ++ HL c.q c.h :: v.map b2n)) = true) :
    A.run A.q0 (lw u) < A.n ∧ c.q < 6 ∧
      A.δ (A.run A.q0 (lw u)) (HL c.q c.h) < A.n := by
  rw [DFA.run_append] at h
  have h1 := acc_lt h
  have h2 := acc_lt (w := v.map b2n) h
  refine ⟨h1, ?_, h2⟩
  apply Classical.byContradiction; intro hq
  have : A.δ (A.run A.q0 (lw u)) (HL c.q c.h) = A.n := A.δ_out _ _ (Or.inr (by
    unfold HL; omega))
  omega

/-- **Right-sweep theorem**: from any invariant configuration whose next move is to the right,
the machine runs ≥ 1 steps without halting and lands in the invariant again. -/
theorem right_sound (hok : rightOK A M co memC memQ SC SQ = true)
    (hmC : ∀ t, memC t = true → t ∈ SC) (hmQ : ∀ t, memQ t = true → t ∈ SQ)
    (c : Cfg) (hi : Inv A c) {w : Bool} {s1 : Nat} (hM : M c.q c.h = some (w, true, s1)) :
    ∃ k, 1 ≤ k ∧ NH M k c ∧ Inv A (run M k c) := by
  simp only [rightOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨hco, hen⟩, hC⟩, hQ⟩ := hok
  obtain ⟨u, v, hL, hR, ha⟩ := hi
  obtain ⟨hqa, hq6, -⟩ := head_lt ha
  have ha' := ha
  rw [DFA.run_append] at ha'
  have hc : co (A.δ _ (HL c.q c.h)) = true := co_sound hco (v.map b2n) _ ha'
  simp only [entryOK, List.all_eq_true, List.mem_range] at hen
  have := hen _ hqa c.q hq6 c.h (by cases c.h <;> simp)
  simp only [hM, Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h | h
  · rw [hc] at h; cases h
  · have hst : step M c = ⟨s1, w :: c.L, c.R.headD false, c.R.tail⟩ := by
      unfold step; rw [hM]
    obtain ⟨k, hk, hi⟩ := sweep_sound hco hC hmC hQ hmQ v _ s1 _ (step M c) (w :: u) (hmC _ h)
      ha' (by rw [hst])
      (by rw [hst]; exact Eq.trans (eqv_headD_tail c.R) hR)
      (by rw [hst]; exact eqv_cons w hL) (by rw [lw_cons, DFA.run_append]; rfl)
    refine ⟨k + 1, by omega, NH_succ ?_ hk, hi⟩
    unfold halted; rw [hM]; simp

theorem halt_sound (hco : coOK A co = true) (hh : haltOK A M co = true)
    (c : Cfg) (hi : Inv A c) : ¬ halted M c := by
  intro hM
  obtain ⟨u, v, -, -, ha⟩ := hi
  obtain ⟨hqa, hq6, -⟩ := head_lt ha
  rw [DFA.run_append] at ha
  have hc : co (A.δ _ (HL c.q c.h)) = true := co_sound hco (v.map b2n) _ ha
  simp only [haltOK, List.all_eq_true, List.mem_range] at hh
  have := hh _ hqa c.q hq6 c.h (by cases c.h <;> simp)
  unfold halted at hM
  simp only [hM, Bool.not_eq_true'] at this
  rw [hc] at this; cases this
end

end Cert
