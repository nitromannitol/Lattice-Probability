import LatticeProb.Prob.PhaseRectangleBound

/-! Normalized Lebesgue measures on finite rectangles and their phases. -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Normalizing Lebesgue measure on a nonempty finite rectangle gives a
probability measure. -/
theorem isProbabilityMeasure_normalized_restrict_rectangle (n : ℕ)
    (u v : Fin n → ℝ) (huv : ∀ i, u i < v i) :
    IsProbabilityMeasure ((∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
      volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))) := by
  classical
  have h0 : (∏ i, ENNReal.ofReal (v i - u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv i)))
  have ht : (∏ i, ENNReal.ofReal (v i - u i)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  constructor
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    volume_pi_pi, Real.volume_Ico]
  exact ENNReal.inv_mul_cancel h0 ht

/-- The phase of normalized rectangle measure is uniformly close in total
variation to uniform cube measure, independently of the shift. -/
theorem tvDist_normalized_map_fract_mul_restrict_rectangle_le (n : ℕ)
    (u v : Fin n → ℝ) (huv : ∀ i, u i < v i)
    {a : ℝ} (ha : 0 < a) (c : Fin n → ℝ) :
    QuantumZipper.TV.tvDist
      (Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - c i))
        ((∏ i, ENNReal.ofReal (v i - u i))⁻¹ •
          volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))))
      (unitCubeMeasure (Fin n)) ≤
        (∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹ := by
  classical
  let M : ℝ≥0∞ := ∏ i, ENNReal.ofReal (v i - u i)
  have h0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ =>
    ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (huv i)))
  have ht : M ≠ ⊤ := ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  have hf : Measurable (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - c i)) := by
    exact Measurable.of_eval fun i => measurable_fract.comp (by fun_prop)
  rw [Measure.map_smul _ hf.aemeasurable]
  have hs := tvDist_smul_le M⁻¹
    (Measure.map (fun x : Fin n → ℝ => fun i => Int.fract (a * x i - c i))
      (volume.restrict (Set.univ.pi fun i => Ico (u i) (v i))))
    (M • unitCubeMeasure (Fin n))
  have hb := tvDist_map_fract_mul_restrict_rectangle_le n u v ha c
  change QuantumZipper.TV.tvDist _ (M • unitCubeMeasure (Fin n)) ≤
    (M * ∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹ at hb
  calc
    _ ≤ M⁻¹ * QuantumZipper.TV.tvDist _ (M • unitCubeMeasure (Fin n)) := by
      simpa only [smul_smul, ENNReal.inv_mul_cancel h0 ht, one_smul] using hs
    _ ≤ M⁻¹ * ((M * ∑ i, (ENNReal.ofReal (v i - u i))⁻¹) * ENNReal.ofReal a⁻¹) :=
      mul_le_mul_right hb _
    _ = _ := by rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]

end LatticeProb
