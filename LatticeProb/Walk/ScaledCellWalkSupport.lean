import LatticeProb.Walk.CellConfigVisitPathLaw
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Spatially scaled cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigWalk

/-- The canonical walk on a line-connected cell configuration has an unbounded
interpolated path after any nonzero spatial scaling of its cell representatives. -/
theorem ae_unbounded_scaled_walkPath
    (H : CellConfig) (hH : H.IsCellConfiguration) (hL : H.LineConnected)
    (K : H.cells) (p : H.cells → Plane)
    (hp : ∀ K : H.cells, p K ∈ ((K.1 : Cell) : Set Plane)) (c : ℝ) (hc : c ≠ 0) :
    letI : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
    ∀ᵐ (f : C(ℝ≥0, Plane)) ∂((CellConfigSRW.walkLaw H hH K).map
      (fun ω => ConstantStepInterpolation.continuousPlanePath 1 (fun n => c • p (ω n)))),
      ¬ Bornology.IsBounded (Set.range f) := by
  let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
  let : Infinite H.cells := CellMass.infinite_of_iUnion_eq_univ
    (by simpa only [iUnion_subtype] using hH.iUnion_eq_univ) (fun K => K.1.isCompact)
  have hadj := (graph_connected_of_lineConnected H hH hL).preconnected.exists_adj_of_nontrivial K
  obtain ⟨K', hKK'⟩ := hadj
  have hpi : 0 < H.pi K := pi_pos_of_adj hH hKK'.2.1
  have hQ := CellConfigSRW.isSRWLaw_walkLaw H hH hpi
  have hmeas : Measurable (fun ω : ℕ → H.cells => fun n => c • p (ω n)) := by
    apply Measurable.of_eval
    intro n
    exact (measurable_const : Measurable (fun _ : ℕ → H.cells => c)).smul
      ((measurable_of_countable p).comp (measurable_pi_apply n))
  apply (ae_map_iff (measurable_constantStepPath _ hmeas 1).aemeasurable
    (LatticeProb.measurableSet_continuousMap_unbounded_range (0 : Plane))).2
  filter_upwards [ae_infinite_range_of_lineConnected H hH hL hQ] with ω hω
  intro hb
  have hscaled : Bornology.IsBounded (Set.range (fun n => c • p (ω n))) := by
    apply hb.subset
    rintro _ ⟨n, rfl⟩
    refine ⟨ConstantStepInterpolation.knot 1 n, ?_⟩
    change ConstantStepInterpolation.path (1 : ℝ) (fun n => c • p (ω n))
      (ConstantStepInterpolation.knot 1 n) = c • p (ω n)
    exact ConstantStepInterpolation.path_knot (m := 1) (by norm_num) (fun n => c • p (ω n)) n
  have hunscaled : Bornology.IsBounded (Set.range (fun n => p (ω n))) := by
    apply (hscaled.smul₀ c⁻¹).subset
    rintro _ ⟨n, rfl⟩
    refine ⟨c • p (ω n), ⟨n, rfl⟩, ?_⟩
    simp [smul_smul, hc]
  exact (unbounded_range_representatives_of_infinite_range_cells H hH ω
    (fun n => p (ω n)) (fun n => hp (ω n)) hω) hunscaled

end LatticeProb.CellConfigWalk
end
