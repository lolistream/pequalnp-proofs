import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n m : ℕ}

-- Permute only the input blocks; every gate or missing-wire index stays fixed.
private def permWire (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
  if hi : i < n then (e ⟨i, hi⟩).val
  else if hj : i < n + m then n + (d ⟨i - n, by omega⟩).val else i

private theorem readLeft (u : Fin n) (v : Fin m) (tail : List Bool) (i : Fin n) :
    (oneEach u v ++ tail).getD i.val false = decide (i = u) := by
  simp only [oneEach, List.append_assoc]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem readRight (u : Fin n) (v : Fin m) (tail : List Bool) (j : Fin m) :
    (oneEach u v ++ tail).getD (n + j.val) false = decide (j = v) := by
  simp only [oneEach, List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem readPerm (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m))
    (u : Fin n) (v : Fin m) (tail : List Bool) (i : ℕ) :
    (oneEach (e u) (d v) ++ tail).getD (permWire e d i) false =
      (oneEach u v ++ tail).getD i false := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (oneEach (e u) (d v) ++ tail).getD (permWire e d i) false =
      (oneEach u v ++ tail).getD j.val false
    rw [show permWire e d i = (e j).val by simp [permWire, hi, j], readLeft, readLeft]
    simp
  by_cases hj : i < n + m
  · let j : Fin m := ⟨i-n, by omega⟩
    have heq : n + j.val = i := by dsimp [j]; omega
    calc
      _ = decide (d j = d v) := by
        rw [show permWire e d i = n + (d j).val by simp [permWire, hi, hj, j], readRight]
      _ = decide (j = v) := by simp
      _ = _ := by rw [← readRight u v tail j, heq]
  · simp only [permWire, dite_eq_right hi, dite_eq_right hj]
    rw [List.getD_append_right _ _ _ _ (by simp [oneEach]; omega),
        List.getD_append_right _ _ _ _ (by simp [oneEach]; omega)]
    simp [oneEach]

private def mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
private def tick (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem replay (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m))
    (u : Fin n) (v : Fin m) (gs : List Gate) (tail : List Bool) (o : ℕ) :
    ((gs.map (mapGate (permWire e d))).foldl tick (oneEach (e u) (d v) ++ tail)).getD
      (permWire e d o) false = (gs.foldl tick (oneEach u v ++ tail)).getD o false := by
  induction gs generalizing tail with
  | nil => exact readPerm e d u v tail o
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (oneEach u v ++ tail).getD i false)
    have hb : (mapGate (permWire e d) g).op.eval ((mapGate (permWire e d) g).inputs.map
        fun i => (oneEach (e u) (d v) ++ tail).getD i false) = bit := by
      unfold bit mapGate
      simp only [List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i _
      exact readPerm e d u v tail i
    simp only [List.map_cons, List.foldl_cons, tick, hb, List.append_assoc]
    simpa only [bit] using ih (tail ++ [bit])

private theorem pullback {A : Fin n → Fin m → Bool} {s : ℕ}
    (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m)) (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun u v => A (e u) (d v)) s := by
  obtain ⟨C, mono, bound, correct⟩ := h
  let f := permWire e.symm d.symm
  let D : Circuit := ⟨C.gates.map (mapGate f), f C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using mono a ha
  · simpa [D, Circuit.size] using bound
  · intro u v
    have hrun := replay e.symm d.symm (e u) (d v) C.gates [] C.output
    simp only [Equiv.symm_apply_apply, List.append_nil] at hrun
    exact hrun.trans (correct (e u) (d v))

/-- Relabeling the two one-hot vertex blocks independently preserves every size bound. -/
theorem repSizeAtMost_perm_iff (A : Fin n → Fin m → Bool) (s : ℕ)
    (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m)) :
    RepSizeAtMost (fun u v => A (e u) (d v)) s ↔ RepSizeAtMost A s := by
  constructor
  · intro h
    simpa only [Equiv.apply_symm_apply] using pullback e.symm d.symm h
  · exact pullback e d

/-- In particular, the least size is constant on every row/column relabeling orbit. -/
theorem repSize_perm (A : Fin n → Fin m → Bool)
    (e : Equiv.Perm (Fin n)) (d : Equiv.Perm (Fin m)) :
    repSize (fun u v => A (e u) (d v)) = repSize A := by
  simp only [repSize, repSizeAtMost_perm_iff]

end PEqualNP.Represents
