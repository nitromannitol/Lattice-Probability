import LatticeProb.Analysis.ConeExitTimeChange
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Dimension of cone vectors under time changes -/

set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- A Lipschitz increasing change of time transfers a unit-interval dimension
bound for backward cone vectors to the image interval. The joint drop condition
ensures the backward exits transform correctly. -/
theorem dimH_backwardConeVectors_interval_le_timeChange
    (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ) (c d : ℝ) {K : ℝ≥0}
    (he : LipschitzWith K e)
    (hne : ∀ s ∈ Ioo (e 0) (e 1),
      ∃ t < s, (∃ r ∈ Icc t s, X r < X s) ∧
        (∃ r ∈ Icc t s, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧ e 0 < z.1 ∧ z.2 < e 1} ≤
      dimH {z : ℝ × ℝ |
        z ∈ backwardConeVectors (fun t => X (e t) - c) (fun t => Y (e t) - d) ∧
        0 < z.1 ∧ z.2 < 1} := by
  let B : Set (ℝ × ℝ) := {z | z ∈ backwardConeVectors
    (fun t => X (e t) - c) (fun t => Y (e t) - d) ∧ 0 < z.1 ∧ z.2 < 1}
  let f : ℝ × ℝ → ℝ × ℝ := fun z => (e z.1, e z.2)
  have hf : LipschitzWith K f := by
    simpa only [f, max_self, mul_one, Function.comp_apply] using
      ((he.comp LipschitzWith.prod_fst).prodMk (he.comp LipschitzWith.prod_snd))
  have hsub : {z : ℝ × ℝ | z ∈ backwardConeVectors X Y ∧
      e 0 < z.1 ∧ z.2 < e 1} ⊆ f '' B := by
    rintro ⟨a, s⟩ ⟨hv, ha, hs⟩
    have has : a < s := by
      change a = coneJointExitBackward X Y s ∧
        coneJointExitBackward X Y s < coneFirstExitBackward X Y s ∧
        coneFirstExitBackward X Y s < s ∧ _ at hv
      linarith [hv.1, hv.2.1, hv.2.2.1]
    have hdrop := hne s ⟨lt_trans ha has, hs⟩
    refine ⟨(e.symm a, e.symm s), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · apply (mem_backwardConeVectors_timeChange X Y e c d (e.symm a) (e.symm s) ?_).2
        · simpa only [e.apply_symm_apply] using hv
        · simpa only [e.apply_symm_apply] using hdrop
      · simpa only [e.symm_apply_apply] using e.symm.strictMono ha
      · simpa only [e.symm_apply_apply] using e.symm.strictMono hs
    · simp only [f, e.apply_symm_apply]
  exact (dimH_mono hsub).trans (hf.dimH_image_le B)

end LatticeProb
