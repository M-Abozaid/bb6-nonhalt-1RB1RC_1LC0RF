import Cert.Rev
import Std.Data.HashMap
import Std.Data.HashSet
/-! Untrusted builders (parsing, co-reachability, reverse determinization, BFS of the
product certificates). Nothing here is trusted: every output is re-checked by the verified
`Bundle.ok`, and membership is a binary search whose `true` answers are proved correct. -/
namespace Cert
open Std

/-! ## Verified membership: binary search whose positive answers are sound -/

def bsFind {α : Type} [DecidableEq α] (cmp : α → α → Ordering) (arr : Array α) (x : α) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, lo, hi =>
    if lo < hi then
      match arr[(lo + hi) / 2]? with
      | none => false
      | some y =>
        match cmp x y with
        | .lt => bsFind cmp arr x f lo ((lo + hi) / 2)
        | .gt => bsFind cmp arr x f ((lo + hi) / 2 + 1) hi
        | .eq => decide (y = x)
    else false

theorem bsFind_sound {α : Type} [DecidableEq α] (cmp : α → α → Ordering) (arr : Array α)
    (x : α) : ∀ f lo hi, bsFind cmp arr x f lo hi = true → x ∈ arr.toList := by
  intro f
  induction f with
  | zero => intro lo hi h; simp [bsFind] at h
  | succ f ih =>
    intro lo hi h
    simp only [bsFind] at h
    split at h
    · split at h
      · cases h
      · rename_i y hy
        split at h
        · exact ih _ _ h
        · exact ih _ _ h
        · have e : y = x := of_decide_eq_true h
          subst e
          exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hy)
    · cases h

def cmp3 (a b : Nat × Nat × Nat) : Ordering :=
  (compare a.1 b.1).then ((compare a.2.1 b.2.1).then (compare a.2.2 b.2.2))
def cmp2 (a b : Nat × Nat) : Ordering := (compare a.1 b.1).then (compare a.2 b.2)

def sortArr {α : Type} (cmp : α → α → Ordering) (l : List α) : Array α :=
  (l.mergeSort (fun x y => cmp x y != .gt)).toArray

def memOf {α : Type} [DecidableEq α] (cmp : α → α → Ordering) (arr : Array α) (x : α) : Bool :=
  bsFind cmp arr x 64 0 arr.size

theorem memOf_sound {α : Type} [DecidableEq α] (cmp : α → α → Ordering) (arr : Array α) (x : α)
    (h : memOf cmp arr x = true) : x ∈ arr.toList := bsFind_sound cmp arr x _ _ _ h

/-! ## DFA from the text format -/

def mkDFA (n q0 : Nat) (tr : Array Nat) (acc : Array Bool) : DFA where
  n := n
  δ q a := if q < n ∧ a < 14 then tr.getD (q * 14 + a) n else n
  acc q := decide (q < n) && acc.getD q false
  q0 := q0
  δ_out q a h := by
    have : ¬ (q < n ∧ a < 14) := by omega
    simp only [this, if_false]
  acc_out q h := by simp; omega

def parseInt (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toString.toNat! : Int) else (s.toNat! : Int)

def parseDFA (txt : String) : DFA :=
  let toks := (txt.split (fun c => c == ' ' || c == '\n')).toList.map (·.toString)
    |>.filter (· ≠ "") |>.toArray
  let n := toks[0]!.toNat!
  let q0 := toks[1]!.toNat!
  Id.run do
    let mut tr : Array Nat := Array.mkEmpty (n * 14)
    let mut acc : Array Bool := Array.mkEmpty n
    for q in [0:n] do
      let base := 2 + q * 15
      acc := acc.push (toks[base]! == "1")
      for a in [0:14] do
        let v := parseInt toks[base + 1 + a]!
        tr := tr.push (if v < 0 then n else v.toNat)
    return mkDFA n q0 tr acc

/-! ## co-reachability (backward fixpoint) -/

def coArr (A : DFA) : Array Bool := Id.run do
  let mut rev : Array (List Nat) := Array.replicate (A.n + 1) []
  for q in [0:A.n] do
    for a in [0:14] do
      let p := A.δ q a
      if p < A.n then rev := rev.modify p (q :: ·)
  let mut co : Array Bool := Array.replicate A.n false
  let mut stack : List Nat := []
  for q in [0:A.n] do
    if A.acc q then co := co.set! q true; stack := q :: stack
  let mut fuel := A.n * 15 + 10
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => fuel := 0
    | p :: rest =>
      stack := rest
      for q in rev[p]! do
        if !co[q]! then co := co.set! q true; stack := q :: stack
  return co

def coFn (A : DFA) : Nat → Bool := let c := coArr A; fun q => c.getD q false

/-! ## reverse determinization -/

def revBuild (D : DFA) : RevData := Id.run do
  let n := D.n
  let s0 : Array Bool := Array.ofFn (n := n) fun q => D.acc q.1
  let mut idx : HashMap (Array Bool) Nat := HashMap.emptyWithCapacity 4096
  idx := idx.insert s0 0
  let mut sets : Array (Array Bool) := #[s0]
  let mut tr : Array Nat := #[]
  let mut i := 0
  let mut fuel := 1000000
  while i < sets.size && fuel > 0 do
    fuel := fuel - 1
    let S := sets[i]!
    for a in [0:14] do
      let T : Array Bool := Array.ofFn (n := n) fun q => S.getD (D.δ q.1 a) false
      match idx.get? T with
      | some j => tr := tr.push j
      | none =>
        let j := sets.size
        idx := idx.insert T j; sets := sets.push T; tr := tr.push j
    i := i + 1
  return { nr := sets.size, tr := tr, ph := sets, r0 := 0 }

/-! ## product certificates for a right-sweep pass -/

def buildCert (A : DFA) (M : Machine) (co : Nat → Bool) :
    List (Nat × Nat × Nat) × List (Nat × Nat) := Id.run do
  let mut seenC : HashSet (Nat × Nat × Nat) := {}
  let mut seenQ : HashSet (Nat × Nat) := {}
  let mut stC : List (Nat × Nat × Nat) := []
  let mut stQ : List (Nat × Nat) := []
  for q in [0:A.n] do
    for s in [0:6] do
      for r in [false, true] do
        match M s r with
        | some (w, true, s1) =>
          let qi := A.δ q (HL s r)
          if co qi then
            let t := (qi, s1, A.δ q (b2n w))
            if !seenC.contains t then seenC := seenC.insert t; stC := t :: stC
        | _ => pure ()
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    match stC with
    | t :: rest =>
      stC := rest
      for a in [false, true] do
        let qi' := A.δ t.1 (b2n a)
        if co qi' then
          match M t.2.1 a with
          | some (w, true, s') =>
            let t' := (qi', s', A.δ t.2.2 (b2n w))
            if !seenC.contains t' then seenC := seenC.insert t'; stC := t' :: stC
          | some (_, false, _) =>
            let t' := (qi', A.δ t.2.2 (HL t.2.1 a))
            if !seenQ.contains t' then seenQ := seenQ.insert t'; stQ := t' :: stQ
          | none => pure ()
    | [] =>
      match stQ with
      | t :: rest =>
        stQ := rest
        for a in [false, true] do
          let qi' := A.δ t.1 (b2n a)
          if co qi' then
            let t' := (qi', A.δ t.2 (b2n a))
            if !seenQ.contains t' then seenQ := seenQ.insert t'; stQ := t' :: stQ
      | [] => fuel := 0
  return (seenC.toList, seenQ.toList)

def mkBundle (M : Machine) (D : DFA) : Bundle :=
  let R := revBuild D
  let Dr := R.toDFA D
  let coD := coFn D
  let coR := coFn Dr
  let (c1, q1) := buildCert D M coD
  let (c2, q2) := buildCert Dr (mirM M) coR
  let a1 := sortArr cmp3 c1
  let b1 := sortArr cmp2 q1
  let a2 := sortArr cmp3 c2
  let b2 := sortArr cmp2 q2
  { M := M, D := D, R := R, coD := coD, coR := coR,
    memC₁ := memOf cmp3 a1, memQ₁ := memOf cmp2 b1, SC₁ := a1.toList, SQ₁ := b1.toList,
    memC₂ := memOf cmp3 a2, memQ₂ := memOf cmp2 b2, SC₂ := a2.toList, SQ₂ := b2.toList }

theorem mkBundle_mem (M : Machine) (D : DFA) : (mkBundle M D).Mem :=
  ⟨fun t h => memOf_sound _ _ _ h, fun t h => memOf_sound _ _ _ h,
   fun t h => memOf_sound _ _ _ h, fun t h => memOf_sound _ _ _ h⟩

end Cert
