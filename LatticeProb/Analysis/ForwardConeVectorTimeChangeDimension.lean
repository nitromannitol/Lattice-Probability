import LatticeProb.Analysis.ForwardConeExitTimeChange
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Dimension of forward cone vectors under time changes -/

set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- A Lipschitz increasing time change transfers a negative-unit-interval
bound for forward cone vectors to the corresponding image interval. The joint
future drop condition ensures the forward exits transform correctly. -/
theorem dimH_forwardConeVectors_interval_le_timeChange
    (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ) (c d : ℝ) {K : ℝ≥0}
    (he : LipschitzWith K e)
    (hne : ∀ s ∈ Ioo (e (-1)) (e 0),
      ∃ t > s, (∃ r ∈ Icc s t, X r < X s) ∧
        (∃ r ∈ Icc s t, Y r < Y s)) :
    dimH {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧ e (-1) < z.2 ∧ z.1 < e 0} ≤
      dimH {z : ℝ × ℝ |
        z ∈ forwardConeVectors (fun t => X (e t) - c) (fun t => Y (e t) - d) ∧
        -1 < z.2 ∧ z.1 < 0} := by
  let B : Set (ℝ × ℝ) := {z | z ∈ forwardConeVectors
    (fun t => X (e t) - c) (fun t => Y (e t) - d) ∧ -1 < z.2 ∧ z.1 < 0}
  let f : ℝ × ℝ → ℝ × ℝ := fun z => (e z.1, e z.2)
  have hf : LipschitzWith K f := by
    simpa only [f, max_self, mul_one, Function.comp_apply] using
      ((he.comp LipschitzWith.prod_fst).prodMk (he.comp LipschitzWith.prod_snd))
  have hsub : {z : ℝ × ℝ | z ∈ forwardConeVectors X Y ∧
      e (-1) < z.2 ∧ z.1 < e 0} ⊆ f '' B := by
    rintro ⟨a, s⟩ ⟨hv, hs, ha⟩
    have hsa : s < a := by
      change a = coneFirstExit X Y s ∧ s < coneFirstExit X Y s ∧ _ at hv
      linarith [hv.1, hv.2.1]
    have hdrop := hne s ⟨hs, lt_trans hsa ha⟩
    refine ⟨(e.symm a, e.symm s), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · apply (mem_forwardConeVectors_timeChange X Y e c d (e.symm a) (e.symm s) ?_).2
        · simpa only [e.apply_symm_apply] using hv
        · simpa only [e.apply_symm_apply] using hdrop
      · simpa only [e.symm_apply_apply] using e.symm.strictMono hs
      · simpa only [e.symm_apply_apply] using e.symm.strictMono ha
    · simp only [f, e.apply_symm_apply]
  exact (dimH_mono hsub).trans (hf.dimH_image_le B)

end LatticeProb
