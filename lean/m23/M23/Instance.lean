import M23.Word

set_option maxRecDepth 100000

namespace M23

/-! ## A real checkpoint word (event 1000 of the actual run from the blank tape), kernel-checked.
Word `.11.11.111.111.11.111.111.11.111.11.111.11.11.111.11..11.11.1.11.1` (+ 6 blanks). The word map is evaluated by the kernel (`decide`); the event
theorem then holds for EVERY body length n = k + 2.  At n = 1979 (the real one) this gives
the next real checkpoint: 23963 steps, n' = 1981, word `11..11.11.111.111.11.111.111.11.111.11.111.11.11.111.11...11.111.1......` = 11. ++ event-1001 word. -/

def w1000 : List Bool := [true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false, false, false, false, false, false]
def v1000 : List Bool := [true, false, false, true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true, false, false, false, false, false, false]

theorem wordMap_1000 : wordMap 300 w1000 = some (211, 2, v1000) := by decide

theorem event_1000 (k : Nat) :
    run (evSteps k 211 (2 + k)) (ckpt (k + 2) (false :: w1000))
      = ckpt (2 + k + 1) (true :: v1000) :=
  event_map k 300 211 2 w1000 v1000 wordMap_1000

/-- the real instance: t = 12010395 → 12034358 in the actual run -/
example : evSteps 1977 211 (2 + 1977) = 23963 := by decide

end M23
