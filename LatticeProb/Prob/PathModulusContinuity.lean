import Mathlib
import LatticeProb.Prob.LawKernelTightness
import LatticeProb.Prob.PathSpaceTightness

/-!
# Continuity from above of the path modulus events

For `L > 0` the modulus event `pathModulusFailure L δ` of the path space `C(ℝ≥0, E)` is open and
increasing in the scale `δ`, and its intersection over the scales `δ > 0` is empty (every path is
uniformly continuous on `[0, L]`).  Hence the measure of the modulus event of a finite measure tends
to `0` as the scale tends to `0`.
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- The modulus event is open for the compact-open topology. -/
theorem isOpen_pathModulusFailure (L : ℝ) (δ : ℝ≥0) : IsOpen (pathModulusFailure (E := E) L δ) := by
  have h : pathModulusFailure (E := E) L δ = ⋃ (s : ℝ≥0) (t : ℝ≥0)
      (_ : (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ),
      {f : C(ℝ≥0, E) | 1 / L < dist (f s) (f t)} := by
    ext f
    simp only [pathModulusFailure, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]
  rw [h]
  refine isOpen_iUnion fun s => isOpen_iUnion fun t => isOpen_iUnion fun _ => ?_
  exact isOpen_lt continuous_const ((continuous_eval_const s).dist (continuous_eval_const t))

/-- The modulus event is increasing in the scale. -/
theorem pathModulusFailure_mono_scale (L : ℝ) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    pathModulusFailure (E := E) L δ ⊆ pathModulusFailure L δ' := by
  rintro f ⟨s, t, hs, ht, hst, hlt⟩
  exact ⟨s, t, hs, ht, hst.trans (by exact_mod_cast h), hlt⟩

/-- No path has a modulus failure of level `L > 0` at arbitrarily small scales. -/
theorem iInter_pathModulusFailure_eq_empty {L : ℝ} (hL : 0 < L) :
    (⋂ δ > (0 : ℝ), pathModulusFailure (E := E) L δ.toNNReal) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun f hf => ?_
  simp only [Set.mem_iInter] at hf
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := L.toNNReal)).uniformContinuousOn_of_continuous
    f.continuous.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / L) (by positivity)
  obtain ⟨s, t, hs, ht, hst, hlt⟩ := hf (δ / 2) (half_pos hδ)
  have hs' : s ∈ Icc (0 : ℝ≥0) L.toNNReal := ⟨zero_le, (Real.le_toNNReal_iff_coe_le hL.le).2 hs⟩
  have ht' : t ∈ Icc (0 : ℝ≥0) L.toNNReal := ⟨zero_le, (Real.le_toNNReal_iff_coe_le hL.le).2 ht⟩
  have hdist : dist s t < δ := by
    rw [NNReal.dist_eq]
    have : (((δ / 2).toNNReal : ℝ≥0) : ℝ) = δ / 2 := Real.coe_toNNReal _ (by linarith)
    linarith
  exact absurd hlt (not_lt.2 (hδf s hs' t ht' hdist).le)

/-- **The modulus event is negligible at small scales.**  For a finite measure on the path space the
measure of the modulus event of level `L > 0` tends to `0` with the scale. -/
theorem tendsto_measure_pathModulusFailure [MeasurableSpace C(ℝ≥0, E)]
    [OpensMeasurableSpace C(ℝ≥0, E)] (μ : Measure C(ℝ≥0, E)) [IsFiniteMeasure μ] {L : ℝ}
    (hL : 0 < L) :
    Tendsto (fun δ : ℝ => μ (pathModulusFailure L δ.toNNReal)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_measure_of_biInter_eq_empty μ (fun δ => pathModulusFailure L δ.toNNReal)
    (fun _ => (isOpen_pathModulusFailure L _).measurableSet.nullMeasurableSet)
    (fun _ _ h => pathModulusFailure_mono_scale L (Real.toNNReal_le_toNNReal h))
    (iInter_pathModulusFailure_eq_empty hL)

end LatticeProb
