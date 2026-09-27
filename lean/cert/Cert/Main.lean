import Cert.Build
import Cert.Start
import Cert.Data
/-! Final theorems. The only non-kernel steps are the three `native_decide` evaluations below (B_ok, startA_ok, startD_ok). -/
namespace Cert

def D : DFA := parseDFA cw100
def B : Bundle := mkBundle M D

/-- all invariant checks on cw100.dfa (reverse-DFA certificate, halt exclusion, co-reachability,
right-sweep closure for `M` and for the mirrored machine). -/
theorem B_ok : B.ok = true := by native_decide

theorem D_forever (c : Cfg) (hi : Inv D c) (n : Nat) : ¬ halted M (run M n c) :=
  inv_forever B B_ok (mkBundle_mem M D) n c hi

theorem nonhalt_of_start {q : Nat} (h : ∃ m, Inv D (run M m (blank q))) :
    ∀ n, ¬ halted M (run M n (blank q)) := by
  obtain ⟨m, hm⟩ := h
  intro n hn
  by_cases hnm : m ≤ n
  · have : n = m + (n - m) := by omega
    rw [this, run_add] at hn
    exact D_forever _ hm _ hn
  · have := halted_mono (show n ≤ m + 0 by omega) hn
    rw [run_add] at this
    exact D_forever _ hm 0 this

/-- start from blank, state A: 79 direct steps to checkpoint `(11.)^3 ..11.1`, then 55,565
accelerated events (M23.event_map) to a checkpoint accepted by cw100 (≈3.7e10 steps). -/
theorem startA_ok : startOK D 0 79 3 [false, false, true, true, false, true] 55565 = true := by
  native_decide

/-- start from blank, state D: 159 steps, then 55,563 events. -/
theorem startD_ok :
    startOK D 3 159 3 [false, false, true, true, false, true, true, true, false, true] 55563 = true := by
  native_decide

/-- **M = 1RB1RC_1LC0RF_1RE0LD_1LB0LD_---1RF_0LF0RA does not halt from the blank tape.** -/
theorem nonhalt : ∀ n, ¬ halted M (run M n (blank 0)) :=
  nonhalt_of_start (startOK_sound startA_ok)

/-- M started in state D on the blank tape does not halt either. -/
theorem nonhalt_D : ∀ n, ¬ halted M (run M n (blank 3)) :=
  nonhalt_of_start (startOK_sound startD_ok)

/-- **The mirror machine N = 1RB0RA_1RC0LE_1LD0RA_---1LE_0RE0LF_1LB1LC does not halt from blank.** -/
theorem nonhalt_N : ∀ n, ¬ halted N (run N n (blank 0)) := by
  intro n; rw [N_run, N_halted]; exact nonhalt_D n

end Cert
