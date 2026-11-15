import LatticeProb.Prob.NormalizedPhaseInterval
import LatticeProb.Prob.FiniteProductTVLimit
import LatticeProb.Prob.FiniteProductScaledMeasures
import LatticeProb.Prob.RectangleCoordinateMap
import LatticeProb.Prob.DegeneratePhaseRectangle
import LatticeProb.Prob.UnitCubeTVApproximation

/-! Equidistribution of coordinate phases on finite rectangles. -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Coordinate phases of Lebesgue measure on a finite half-open rectangle
converge in total variation to its mass times uniform measure on the cube. -/
theorem tendsto_tvDist_map_fract_mul_restrict_rectangle
    {τ : Type*} {l : Filter τ} (n : ℕ) (u v : Fin n → ℝ)
    (a : τ → ℝ) (c : τ → Fin n → ℝ) (ha : Tendsto a l atTop) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a t * x i - c t i))
        (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))))
      ((∏ i, ENNReal.ofReal (v i - u i)) • unitCubeMeasure (Fin n))) l (𝓝 0) := by
  classical
  by_cases h : ∃ i, v i ≤ u i
  · simpa only [tvDist_map_restrict_rectangle_eq_zero_of_le u v _ _ h] using
      (tendsto_const_nhds : Tendsto (fun _ : τ => (0 : ℝ≥0∞)) l (𝓝 0))
  · have huv : ∀ i, u i < v i := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
    let L : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal (v i - u i)
    let U : Measure ℝ := volume.restrict (Ico 0 1)
    let μ : Fin n → τ → Measure ℝ := fun i t =>
      (L i)⁻¹ • Measure.map (fun x : ℝ => Int.fract (a t * x - c t i))
        (volume.restrict (Ico (u i) (v i)))
    have hL0 (i) : L i ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv i)))
    have hLt (i) : L i ≠ ⊤ := ENNReal.ofReal_ne_top
    have hphase (i : Fin n) (t : τ) : Measurable (fun x : ℝ => Int.fract (a t * x - c t i)) :=
      measurable_fract.comp (by fun_prop)
    have hprob (i : Fin n) (t : τ) : IsProbabilityMeasure (μ i t) := by
      have : IsProbabilityMeasure ((L i)⁻¹ • volume.restrict (Ico (u i) (v i))) :=
        isProbabilityMeasure_normalized_restrict_Ico (huv i)
      change IsProbabilityMeasure ((L i)⁻¹ • Measure.map _ _)
      rw [← Measure.map_smul _ (hphase i t).aemeasurable]
      infer_instance
    have : ∀ i t, IsProbabilityMeasure (μ i t) := hprob
    have hU : IsProbabilityMeasure U := by
      constructor
      simp [U, Real.volume_Ico]
    have : IsProbabilityMeasure U := hU
    let ν : Fin n → τ → Measure ℝ := fun _ _ => U
    have : ∀ i t, IsProbabilityMeasure (ν i t) := fun _ _ => hU
    have hlim : Tendsto (fun t => QuantumZipper.TV.tvDist
        (Measure.pi fun i => μ i t) (Measure.pi fun i => ν i t)) l (𝓝 0) :=
      tendsto_tvDist_pi_fin n μ ν (fun i => by
        simpa only [μ, ν, U, L] using
          tendsto_tvDist_normalized_map_fract_mul_restrict_Ico (huv i) a (fun t => c t i) ha)
    have hprod : (∏ i, L i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hLt i
    have hscaled := ENNReal.Tendsto.const_mul hlim (a := ∏ i, L i) (Or.inr hprod)
    have hscaled' : Tendsto (fun t => (∏ i, L i) * QuantumZipper.TV.tvDist
        (Measure.pi fun i => μ i t) (Measure.pi fun i => ν i t)) l (𝓝 0) := by
      simpa only [mul_zero] using hscaled
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled'
    · exact Eventually.of_forall fun _ => bot_le
    · filter_upwards with t
      have hmap : Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a t * x i - c t i))
          (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))) =
          (∏ i, L i) • Measure.pi (fun i => μ i t) := by
        rw [map_restrict_rectangle_eq_pi u v _ (fun i => hphase i t)]
        rw [← pi_smul_finite (fun i => μ i t) L hLt]
        congr 1
        funext i
        simp only [μ, smul_smul, ENNReal.mul_inv_cancel (hL0 i) (hLt i), one_smul]
      have hcube : Measure.pi (fun i : Fin n => ν i t) = unitCubeMeasure (Fin n) := by
        simp only [ν, U, unitCubeMeasure, volume_pi, Measure.restrict_pi_pi]
      rw [hmap, ← hcube]
      exact tvDist_smul_le _ _ _

end LatticeProb
