import Cert.DFA
/-! A DFA `Dr` for the reversed language of `D`, certified by a labelling `phi p q`
("state `q` of `D` belongs to the subset denoted by `Dr`-state `p`"). -/
namespace Cert

structure RevData where
  nr : Nat
  tr : Array Nat              -- tr[p*14+a]
  ph : Array (Array Bool)     -- ph[p][q]
  r0 : Nat

def RevData.phi (R : RevData) (n p q : Nat) : Bool :=
  if p < R.nr ∧ q < n then (R.ph.getD p #[]).getD q false else false

def RevData.toDFA (R : RevData) (D : DFA) : DFA where
  n := R.nr
  δ p a := if p < R.nr ∧ a < 14 then R.tr.getD (p * 14 + a) R.nr else R.nr
  acc p := R.phi D.n p D.q0
  q0 := R.r0
  δ_out p a h := by
    have : ¬ (p < R.nr ∧ a < 14) := by omega
    simp only [this, if_false]
  acc_out p h := by
    unfold RevData.phi
    have : ¬ (p < R.nr ∧ D.q0 < D.n) := by omega
    simp only [this, if_false]

/-- the checks: start labelling = accepting states, transitions = preimages -/
def revOK (D : DFA) (R : RevData) : Bool :=
  ((List.range D.n).all fun q => R.phi D.n R.r0 q == D.acc q) &&
  (List.range R.nr).all fun p => (List.range 14).all fun a =>
    (List.range D.n).all fun q =>
      R.phi D.n ((R.toDFA D).δ p a) q == R.phi D.n p (D.δ q a)

section
variable {D : DFA} {R : RevData}

theorem phi_out {p q : Nat} (h : D.n ≤ q) : R.phi D.n p q = false := by
  unfold RevData.phi; have : ¬ (p < R.nr ∧ q < D.n) := by omega
  simp only [this, if_false]

theorem pre_all (hok : revOK D R = true) (p a q : Nat) :
    R.phi D.n ((R.toDFA D).δ p a) q = R.phi D.n p (D.δ q a) := by
  simp only [revOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hok
  by_cases hq : q < D.n
  · by_cases hp : p < R.nr ∧ a < 14
    · exact hok.2 p hp.1 a hp.2 q hq
    · have e : (R.toDFA D).δ p a = R.nr := (R.toDFA D).δ_out p a (by simp [RevData.toDFA]; omega)
      rw [e]
      have l : R.phi D.n R.nr q = false := by
        unfold RevData.phi; simp
      rw [l]
      by_cases hp' : p < R.nr
      · have : 14 ≤ a := by omega
        rw [D.δ_out q a (Or.inr this), phi_out (Nat.le_refl _)]
      · unfold RevData.phi; simp [hp']
  · rw [phi_out (by omega), D.δ_out q a (Or.inl (by omega)), phi_out (Nat.le_refl _)]

theorem phi_run (hok : revOK D R = true) :
    ∀ (w : List Nat) (p q : Nat),
      R.phi D.n ((R.toDFA D).run p w) q = R.phi D.n p (D.run q w.reverse) := by
  intro w
  induction w with
  | nil => intro p q; rfl
  | cons a w ih =>
    intro p q
    show R.phi D.n ((R.toDFA D).run ((R.toDFA D).δ p a) w) q = _
    rw [ih, pre_all hok, List.reverse_cons, DFA.run_append]; rfl

theorem rev_accepts (hok : revOK D R = true) (w : List Nat) :
    (R.toDFA D).acc ((R.toDFA D).run (R.toDFA D).q0 w) = D.acc (D.run D.q0 w.reverse) := by
  show R.phi D.n _ D.q0 = _
  rw [phi_run hok]
  simp only [revOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hok
  by_cases h : D.run D.q0 w.reverse < D.n
  · exact hok.1 _ h
  · rw [phi_out (by omega), D.acc_out _ (by omega)]

theorem Inv_rev (hok : revOK D R = true) (c : Cfg) : Inv D c ↔ Inv (R.toDFA D) (mir id c) := by
  have key : ∀ u v : List Bool,
      (R.toDFA D).acc ((R.toDFA D).run (R.toDFA D).q0 (lw v ++ HL c.q c.h :: u.map b2n))
        = D.acc (D.run D.q0 (lw u ++ HL c.q c.h :: v.map b2n)) := by
    intro u v; rw [rev_accepts hok]; congr 2; simp [lw, List.map_reverse]
  constructor
  · rintro ⟨u, v, h1, h2, h3⟩; exact ⟨v, u, h2, h1, by simp only [mir, id]; rw [key]; exact h3⟩
  · rintro ⟨v, u, h2, h1, h3⟩
    simp only [mir, id] at h1 h2 h3; exact ⟨u, v, h1, h2, by rw [← key]; exact h3⟩
end

/-- mirror machine (same state names) -/
def mirM (M : Machine) : Machine := fun q h => (M q h).map fun t => (t.1, !t.2.1, t.2.2)

theorem isMirror_mirM (M : Machine) : IsMirror id M (mirM M) := fun _ _ => rfl

/-! ## All checks together -/

structure Bundle where
  M : Machine
  D : DFA
  R : RevData
  coD : Nat → Bool
  coR : Nat → Bool
  memC₁ : Nat × Nat × Nat → Bool
  memQ₁ : Nat × Nat → Bool
  SC₁ : List (Nat × Nat × Nat)
  SQ₁ : List (Nat × Nat)
  memC₂ : Nat × Nat × Nat → Bool
  memQ₂ : Nat × Nat → Bool
  SC₂ : List (Nat × Nat × Nat)
  SQ₂ : List (Nat × Nat)

def Bundle.ok (B : Bundle) : Bool :=
  revOK B.D B.R && haltOK B.D B.M B.coD && coOK B.D B.coD &&
  rightOK B.D B.M B.coD B.memC₁ B.memQ₁ B.SC₁ B.SQ₁ &&
  rightOK (B.R.toDFA B.D) (mirM B.M) B.coR B.memC₂ B.memQ₂ B.SC₂ B.SQ₂

structure Bundle.Mem (B : Bundle) : Prop where
  c1 : ∀ t, B.memC₁ t = true → t ∈ B.SC₁
  q1 : ∀ t, B.memQ₁ t = true → t ∈ B.SQ₁
  c2 : ∀ t, B.memC₂ t = true → t ∈ B.SC₂
  q2 : ∀ t, B.memQ₂ t = true → t ∈ B.SQ₂

theorem inv_step (B : Bundle) (hok : B.ok = true) (hm : B.Mem) (c : Cfg) (hi : Inv B.D c) :
    ∃ k, 1 ≤ k ∧ NH B.M k c ∧ Inv B.D (run B.M k c) := by
  simp only [Bundle.ok, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨hrev, hh⟩, hco⟩, hr1⟩, hr2⟩ := hok
  cases hM : B.M c.q c.h with
  | none => exact absurd hM (halt_sound hco hh c hi)
  | some t =>
    obtain ⟨w, d, s1⟩ := t
    cases d with
    | true => exact right_sound hr1 hm.c1 hm.q1 c hi hM
    | false =>
      have hM' : mirM B.M (mir id c).q (mir id c).h = some (w, true, s1) := by
        simp [mirM, mir, hM]
      obtain ⟨k, hk1, hk, hi'⟩ :=
        right_sound hr2 hm.c2 hm.q2 (mir id c) ((Inv_rev hrev c).1 hi) hM'
      refine ⟨k, hk1, ?_, ?_⟩
      · intro j hj h
        exact hk j hj (by rw [run_mir (isMirror_mirM B.M)]; exact (halted_mir (isMirror_mirM _) _).2 h)
      · rw [run_mir (isMirror_mirM B.M)] at hi'; exact (Inv_rev hrev _).2 hi'

theorem inv_forever (B : Bundle) (hok : B.ok = true) (hm : B.Mem) :
    ∀ n (c : Cfg), Inv B.D c → ¬ halted B.M (run B.M n c) := by
  have hh : haltOK B.D B.M B.coD = true ∧ coOK B.D B.coD = true := by
    simp only [Bundle.ok, Bool.and_eq_true] at hok; exact ⟨hok.1.1.1.2, hok.1.1.2⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hi
    obtain ⟨k, hk1, hk, hi'⟩ := inv_step B hok hm c hi
    by_cases hn : n < k
    · exact hk n hn
    · have : n = k + (n - k) := by omega
      rw [this, run_add]
      exact ih (n - k) (by omega) _ hi'

end Cert
