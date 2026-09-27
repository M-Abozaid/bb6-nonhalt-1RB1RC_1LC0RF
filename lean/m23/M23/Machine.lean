/-! Machine m23 = 1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA, exact semantics.
Tape: `L` = cells left of the head (nearest first), `h` = scanned cell,
`R` = cells right of the head (nearest first); missing cells are blank (`false`). -/
namespace M23

inductive St | A | B | C | D | E | F | H
  deriving DecidableEq, Repr

structure Cfg where
  st : St
  L : List Bool
  h : Bool
  R : List Bool
  deriving DecidableEq, Repr

/-- write `w`, move right, enter `s` -/
def mR (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, w :: c.L, c.R.headD false, c.R.tail⟩
/-- write `w`, move left, enter `s` -/
def mL (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, c.L.tail, c.L.headD false, w :: c.R⟩

/-- One step. `E` scanning `0` is the undefined transition: enter `H` (halted). -/
def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | .A, false => mR .B true c
  | .A, true  => mR .C true c
  | .B, false => mL .C true c
  | .B, true  => mR .F false c
  | .C, false => mR .E true c
  | .C, true  => mL .D false c
  | .D, false => mL .B true c
  | .D, true  => mL .D false c
  | .E, false => { c with st := .H }
  | .E, true  => mR .F true c
  | .F, false => mL .F false c
  | .F, true  => mR .A false c
  | .H, _     => c

def run : Nat → Cfg → Cfg
  | 0, c => c
  | n + 1, c => run n (step c)

theorem run_add (m n : Nat) (c : Cfg) : run (m + n) c = run n (run m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [run]
    exact ih (step c)

/-- `pw k u` = `u` repeated `k` times. -/
def pw : Nat → List Bool → List Bool
  | 0, _ => []
  | k + 1, u => u ++ pw k u

@[simp] theorem pw_zero (u : List Bool) : pw 0 u = [] := rfl
@[simp] theorem pw_succ (k : Nat) (u : List Bool) : pw (k + 1) u = u ++ pw k u := rfl

theorem pw_comm (k : Nat) (u : List Bool) : u ++ pw k u = pw k u ++ u := by
  induction k with
  | zero => simp
  | succ k ih => rw [pw_succ, List.append_assoc, ← ih]

theorem pw_succ' (k : Nat) (u : List Bool) : pw (k + 1) u = pw k u ++ u := by
  rw [pw_succ, pw_comm]

theorem pw_add (a b : Nat) (u : List Bool) : pw (a + b) u = pw a u ++ pw b u := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, pw_succ, pw_succ, ih, List.append_assoc]

/-- Unit of the body on the right list: `11.` -/
abbrev U : List Bool := [true, true, false]

/-- Checkpoint: state C on a blank at the leftmost visited cell (everything left is blank),
then `n` body units `11.`, then the word `W`. -/
def ckpt (n : Nat) (W : List Bool) : Cfg := ⟨.C, [], false, pw n U ++ W⟩

end M23
