import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem Measured_L_meta_18357_size45 : (PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (x 0 && x 1 && x 5) || (x 0 && x 2 && x 6) || (x 0 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 2 && x 9) || (x 1 && x 3 && x 10) || (x 1 && x 4 && x 11) || (x 2 && x 3 && x 12) || (x 2 && x 4 && x 13) || (x 3 && x 4 && x 14) || (x 5 && x 6 && x 9) || (x 5 && x 7 && x 10) || (x 5 && x 8 && x 11) || (x 6 && x 7 && x 12) || (x 6 && x 8 && x 13) || (x 7 && x 8 && x 14) || (x 9 && x 10 && x 12) || (x 9 && x 11 && x 13) || (x 10 && x 11 && x 14) || (x 12 && x 13 && x 14)) 45) := by
  let C : Circuit := ⟨[⟨.and, [6, 8]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [3, 14]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [9, 11]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [8, 14]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [15, 26]⟩, ⟨.or, [24, 35]⟩, ⟨.and, [13, 36]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [16, 38]⟩, ⟨.and, [5, 39]⟩, ⟨.or, [17, 29]⟩, ⟨.or, [32, 41]⟩, ⟨.or, [21, 42]⟩, ⟨.and, [2, 43]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [30, 45]⟩, ⟨.and, [4, 46]⟩, ⟨.or, [25, 34]⟩, ⟨.or, [33, 48]⟩, ⟨.or, [19, 49]⟩, ⟨.and, [7, 50]⟩, ⟨.or, [23, 28]⟩, ⟨.or, [20, 52]⟩, ⟨.and, [10, 53]⟩, ⟨.or, [40, 44]⟩, ⟨.or, [37, 51]⟩, ⟨.or, [55, 56]⟩, ⟨.or, [47, 57]⟩, ⟨.or, [54, 58]⟩], 59⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [FanInTwo, C]
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14] := rfl
    have eAnd (w : List Bool) : GateOp.eval .and w = w.all id := rfl
    have eOr (w : List Bool) : GateOp.eval .or w = w.any id := rfl
    unfold Circuit.eval Circuit.wires
    rw [hx]
    simp (config := { maxSteps := 300000 }) [C, eAnd, eOr, Bool.and_or_distrib_left]
    ac_rfl
