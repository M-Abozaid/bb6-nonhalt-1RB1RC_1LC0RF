import Cert.TM
/-! The two machines. Entries: `(write, moveRight, next)`; states A..F = 0..5. -/
namespace Cert

/-- `1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA` -/
def M : Machine
  | 0, false => some (true, true, 1)    -- A0 1RB
  | 0, true  => some (true, true, 2)    -- A1 1RC
  | 1, false => some (true, false, 2)   -- B0 1LC
  | 1, true  => some (false, true, 5)   -- B1 0RF
  | 2, false => some (true, true, 4)    -- C0 1RE
  | 2, true  => some (false, false, 3)  -- C1 0LD
  | 3, false => some (true, false, 1)   -- D0 1LB
  | 3, true  => some (false, false, 3)  -- D1 0LD
  | 4, false => none                    -- E0 ---
  | 4, true  => some (true, true, 5)    -- E1 1RF
  | 5, false => some (false, false, 5)  -- F0 0LF
  | 5, true  => some (false, true, 0)   -- F1 0RA
  | _, _ => none

/-- `1RB0RA_1RC0LE_1LD0RA_---1LE_0RE0LF_1LB1LC` -/
def N : Machine
  | 0, false => some (true, true, 1)    -- A0 1RB
  | 0, true  => some (false, true, 0)   -- A1 0RA
  | 1, false => some (true, true, 2)    -- B0 1RC
  | 1, true  => some (false, false, 4)  -- B1 0LE
  | 2, false => some (true, false, 3)   -- C0 1LD
  | 2, true  => some (false, true, 0)   -- C1 0RA
  | 3, false => none                    -- D0 ---
  | 3, true  => some (true, false, 4)   -- D1 1LE
  | 4, false => some (false, true, 4)   -- E0 0RE
  | 4, true  => some (false, false, 5)  -- E1 0LF
  | 5, false => some (true, false, 1)   -- F0 1LB
  | 5, true  => some (true, false, 2)   -- F1 1LC
  | _, _ => none

/-- renaming M-states to N-states: A→F, B→B, C→C, D→A, E→D, F→E -/
def piMN : Nat → Nat
  | 0 => 5 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 4 | n => n

theorem N_mirror_M : IsMirror piMN M N := by
  intro q h
  rcases q with _ | _ | _ | _ | _ | _ | q <;> cases h <;> rfl

theorem N_run (n : Nat) : run N n (blank 0) = mir piMN (run M n (blank 3)) :=
  run_mir N_mirror_M n (blank 3)

theorem N_halted (c : Cfg) : halted N (mir piMN c) ↔ halted M c := halted_mir N_mirror_M c

end Cert
