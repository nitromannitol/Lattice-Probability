import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.MeasureTheory.Constructions.Pi

/-! Total variation for degenerate finite rectangles. -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- If one side of a finite half-open rectangle is empty, its image measure
and the corresponding length-scaled target are both zero. -/
theorem tvDist_map_restrict_rectangle_eq_zero_of_le {ι β : Type*} [Fintype ι]
    [MeasurableSpace β] (u v : ι → ℝ) (f : (ι → ℝ) → β) (ν : Measure β)
    (h : ∃ i, v i ≤ u i) :
    QuantumZipper.TV.tvDist
      (Measure.map f (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))))
      ((∏ i, ENNReal.ofReal (v i - u i)) • ν) = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  have hempty : (Set.univ.pi fun j => Ico (u j) (v j)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := hx i (Set.mem_univ i)
    exact (not_lt_of_ge (le_trans hi hx'.1)) hx'.2
  have hprod : (∏ j, ENNReal.ofReal (v j - u j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hi)
  simp [hempty, hprod, QuantumZipper.TV.tvDist_self]

end LatticeProb
