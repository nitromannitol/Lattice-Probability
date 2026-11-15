import LatticeProb.Prob.CorrelatedBMKernelDimension

/-! # Fixed-ray asymptotics and wedge survival bounds -/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- A finite power-ratio limit at zero and a global unit bound imply a global
power bound for a nonnegative exponent. -/
theorem exists_power_bound_of_tendsto_div {f : ℝ → ℝ} {p L : ℝ}
    (hp : 0 ≤ p) (hf : ∀ r, 0 < r → f r ≤ 1)
    (hlim : Tendsto (fun r => f r / r ^ p) (𝓝[>] 0) (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, 0 < r → f r ≤ B * r ^ p := by
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r / r ^ p < L + 1 :=
    hlim.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨max (|L| + 1) ((δ ^ p)⁻¹), le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro r hr
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr _
  by_cases h : r < δ
  · have hs : f r / r ^ p < L + 1 := hsmall ⟨hr, h⟩
    have hs' : f r ≤ (|L| + 1) * r ^ p := by
      have hL : L ≤ |L| := le_abs_self L
      exact (le_of_lt ((div_lt_iff₀ hrp).mp hs)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hrp.le)
    exact hs'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrp.le)
  · have hδp : 0 < δ ^ p := Real.rpow_pos_of_pos hδ _
    have hcomp : δ ^ p ≤ r ^ p := Real.rpow_le_rpow hδ.le (le_of_not_gt h) hp
    calc
      f r ≤ 1 := hf r hr
      _ = (δ ^ p)⁻¹ * δ ^ p := by field_simp
      _ ≤ (δ ^ p)⁻¹ * r ^ p := mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hδp.le)
      _ ≤ max (|L| + 1) ((δ ^ p)⁻¹) * r ^ p :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hrp.le

/-- A finite fixed-ray power-ratio limit for the wedge killed-heat mass gives
its corresponding uniform bound. The limit is an explicit assumption. -/
theorem exists_wedge_killedHeat_bound_of_tendsto {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hμ : IsCorrelatedBM2 γ μ)
    {p L : ℝ} (hp : 0 ≤ p)
    (hlim : Tendsto (fun r : ℝ =>
      (∫⁻ w, ENNReal.ofReal (killedHeat
        (complexSymmetricWedge (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
          (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2)) 1
        (r / (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) : ℝ) w)).toReal / r ^ p)
      (𝓝[>] 0) (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ w, ENNReal.ofReal (killedHeat
        (complexSymmetricWedge (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
          (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2)) 1
        (r / (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2) : ℝ) w)) ≤
        ENNReal.ofReal (B * r ^ p) := by
  let a := Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2
  let b := Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2
  let K := fun r : ℝ => ∫⁻ w, ENNReal.ofReal (killedHeat
    (complexSymmetricWedge a b) 1 (r / a : ℝ) w)
  have ha : 0 < a := div_pos (Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])) (by norm_num)
  have hK : ∀ r, K r ≤ 1 := by
    intro r
    have hk := measure_openSymmetricWedgeBarrier_whitened_eq_lintegral_killedHeat
      hγ0 hγ2 hμ 0 a b r ha.ne' 1 (by norm_num)
    let _ : IsProbabilityMeasure (μ.map (whitenAt γ 0)) :=
      (isCorrelatedBM2_map_whitenAt hγ0 hγ2 0 hμ).isProbabilityMeasure
    change (∫⁻ w, ENNReal.ofReal (killedHeat
      (complexSymmetricWedge a b) 1 (r / a : ℝ) w)) ≤ 1
    rw [← hk]
    exact prob_le_one
  have hreal : ∀ r, 0 < r → (K r).toReal ≤ 1 := by
    intro r hr
    have h := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) (hK r)
    simpa using h
  obtain ⟨B, hB, hbound⟩ := exists_power_bound_of_tendsto_div hp hreal hlim
  refine ⟨B, hB, ?_⟩
  intro r hr
  have hfin : K r ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (hK r)
  calc
    K r = ENNReal.ofReal (K r).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (B * r ^ p) := ENNReal.ofReal_le_ofReal (hbound r hr)

end LatticeProb.CorrelatedBM
