import LatticeProb.Prob.PhaseRectangleLimit
import LatticeProb.Prob.FiniteProductTV

/-! A uniform estimate for phases of finite rectangles. -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- The total variation error of coordinate phases on a finite half-open
rectangle is bounded uniformly in the shift by a constant divided by the scale. -/
theorem tvDist_map_fract_mul_restrict_rectangle_le (n : ℕ) (u v : Fin n → ℝ)
    {a : ℝ} (ha : 0 < a) (c : Fin n → ℝ) :
    QuantumZipper.TV.tvDist
      (Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - c i))
        (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))))
      ((∏ i, ENNReal.ofReal (v i - u i)) • unitCubeMeasure (Fin n)) ≤
    ((∏ i, ENNReal.ofReal (v i - u i)) *
      (∑ i, (ENNReal.ofReal (v i - u i))⁻¹)) * ENNReal.ofReal a⁻¹ := by
  classical
  by_cases h : ∃ i, v i ≤ u i
  · rw [tvDist_map_restrict_rectangle_eq_zero_of_le u v _ _ h]
    exact bot_le
  · have huv : ∀ i, u i < v i := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
    let L : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal (v i - u i)
    let U : Measure ℝ := volume.restrict (Ico 0 1)
    let μ : Fin n → Measure ℝ := fun i =>
      (L i)⁻¹ • Measure.map (fun x : ℝ => Int.fract (a * x - c i))
        (volume.restrict (Ico (u i) (v i)))
    have hL0 (i) : L i ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv i)))
    have hLt (i) : L i ≠ ⊤ := ENNReal.ofReal_ne_top
    have hphase (i : Fin n) : Measurable (fun x : ℝ => Int.fract (a * x - c i)) :=
      measurable_fract.comp (by fun_prop)
    have hprob (i) : IsProbabilityMeasure (μ i) := by
      have : IsProbabilityMeasure ((L i)⁻¹ • volume.restrict (Ico (u i) (v i))) :=
        isProbabilityMeasure_normalized_restrict_Ico (huv i)
      change IsProbabilityMeasure ((L i)⁻¹ • Measure.map _ _)
      rw [← Measure.map_smul _ (hphase i).aemeasurable]
      infer_instance
    have : ∀ i, IsProbabilityMeasure (μ i) := hprob
    have hU : IsProbabilityMeasure U := by
      constructor
      simp [U, Real.volume_Ico]
    have : IsProbabilityMeasure U := hU
    have hbound (i : Fin n) : QuantumZipper.TV.tvDist (μ i) U ≤
        (L i)⁻¹ * ENNReal.ofReal a⁻¹ := by
      have h := tvDist_smul_le (L i)⁻¹
        (Measure.map (fun x : ℝ => Int.fract (a * x - c i))
          (volume.restrict (Ico (u i) (v i)))) (L i • U)
      have hb := tvDist_map_fract_mul_restrict_Ico_le ha (huv i).le (c i)
      change QuantumZipper.TV.tvDist _ (L i • U) ≤ _ at hb
      have hs : QuantumZipper.TV.tvDist (μ i) U ≤ (L i)⁻¹ *
          QuantumZipper.TV.tvDist
            (Measure.map (fun x : ℝ => Int.fract (a * x - c i))
              (volume.restrict (Ico (u i) (v i)))) (L i • U) := by
        simpa only [μ, smul_smul, ENNReal.inv_mul_cancel (hL0 i) (hLt i), one_smul] using h
      exact hs.trans (mul_le_mul_right hb _)
    have hmap : Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - c i))
        (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))) =
        (∏ i, L i) • Measure.pi μ := by
      rw [map_restrict_rectangle_eq_pi u v _ hphase]
      rw [← pi_smul_finite μ L hLt]
      congr 1
      funext i
      simp only [μ, smul_smul, ENNReal.mul_inv_cancel (hL0 i) (hLt i), one_smul]
    have hcube : Measure.pi (fun _ : Fin n => U) = unitCubeMeasure (Fin n) := by
      simp only [U, unitCubeMeasure, volume_pi, Measure.restrict_pi_pi]
    change QuantumZipper.TV.tvDist _ ((∏ i, L i) • unitCubeMeasure (Fin n)) ≤
      ((∏ i, L i) * ∑ i, (L i)⁻¹) * ENNReal.ofReal a⁻¹
    rw [hmap, ← hcube]
    calc
      _ ≤ (∏ i, L i) * QuantumZipper.TV.tvDist (Measure.pi μ)
          (Measure.pi (fun _ : Fin n => U)) := tvDist_smul_le _ _ _
      _ ≤ (∏ i, L i) * ∑ i, ((L i)⁻¹ * ENNReal.ofReal a⁻¹) := by
        apply mul_le_mul_right
        exact (tvDist_pi_fin_le_sum n μ (fun _ => U)).trans (Finset.sum_le_sum fun i _ => hbound i)
      _ = ((∏ i, L i) * ∑ i, (L i)⁻¹) * ENNReal.ofReal a⁻¹ := by
        rw [← Finset.sum_mul, mul_assoc]

end LatticeProb
