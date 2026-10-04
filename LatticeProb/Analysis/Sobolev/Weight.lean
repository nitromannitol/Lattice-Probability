import LatticeProb.Analysis.Sobolev.Basic

open MeasureTheory
open scoped ENNReal FourierTransform

namespace LatticeProb.Sobolev

/-- The pointwise weight comparison behind the high-frequency bound: on
`Λ ≤ ‖ξ‖` the weight at `s₀` is at most `(1 + (2πΛ)²)^{s₀ - s}` times the
weight at `s`, for `s₀ ≤ s`. -/
theorem weight_le {d : ℕ} {s₀ s Λ : ℝ} (h : s₀ ≤ s) (hΛ : 0 ≤ Λ)
    {ξ : Space d} (hξ : Λ ≤ ‖ξ‖) :
    (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
      ≤ (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
  have hbase : (1 : ℝ) ≤ 1 + (2 * Real.pi * Λ) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * Λ)]
  have hpos : (0 : ℝ) < 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hmono : (1 + (2 * Real.pi * Λ) ^ 2) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) := by
    have h2 : (2 * Real.pi * Λ) ≤ (2 * Real.pi * ‖ξ‖) := by
      have := mul_le_mul_of_nonneg_left hξ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      linarith
    nlinarith [sq_nonneg (2 * Real.pi * Λ), sq_nonneg (2 * Real.pi * ‖ξ‖),
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * Real.pi * Λ) h2]
  have hpow : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
      ≤ (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmono (by linarith)
  have hsplit : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
      = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
    rw [← Real.rpow_add hpos]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpow (le_of_lt (Real.rpow_pos_of_pos hpos s))

/-- The high-frequency tail of the `H^{s₀}` norm is bounded by
`(1 + (2πΛ)²)^{s₀-s}` times the full `H^s` norm, for `s₀ ≤ s`.  This is the
frequency-truncation step of the Rellich–Kondrachov compactness argument. -/
theorem sobolevNormSqHigh_le_mul {d : ℕ} {s₀ s Λ : ℝ} (h : s₀ ≤ s) (hΛ : 0 ≤ Λ)
    (φ : Space d → ℝ) :
    sobolevNormSqHigh d s₀ Λ φ ≤
      ENNReal.ofReal ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s)) * sobolevNormSq d s φ := by
  set c : ℝ := (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s) with hcdef
  have hc : 0 ≤ c := by rw [hcdef]; positivity
  have hset : MeasurableSet {ξ : Space d | Λ < ‖ξ‖} :=
    measurableSet_lt measurable_const measurable_norm
  have key : ∀ ξ : Space d, Λ < ‖ξ‖ →
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2
        ≤ c * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ hξ
    rw [hcdef]
    have hw := mul_le_mul_of_nonneg_right (weight_le h hΛ (le_of_lt hξ))
      (sq_nonneg ‖𝓕 (fun x => (φ x : ℂ)) ξ‖)
    simpa only [mul_assoc] using hw
  calc sobolevNormSqHigh d s₀ Λ φ
      = ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖},
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀ *
            ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := rfl
    _ ≤ ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖},
          ENNReal.ofReal (c * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
            ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hset] with ξ hξ
        exact ENNReal.ofReal_le_ofReal (key ξ hξ)
    _ = ENNReal.ofReal c * ∫⁻ ξ in {ξ : Space d | Λ < ‖ξ‖},
          ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
            ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        simp_rw [ENNReal.ofReal_mul hc]
        rw [lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c * sobolevNormSq d s φ := by
        apply mul_le_mul_of_nonneg_left
        · rw [sobolevNormSq]
          exact setLIntegral_le_lintegral _ _
        · positivity

/-- For `s₀ < s` and `η > 0` there is a frequency cutoff `Λ ≥ 0` beyond which the
`H^{s₀}` tail of every `H^s`-unit test function is at most `η²`.  This is the
cutoff choice of the Rellich–Kondrachov compactness argument. -/
theorem exists_sobolevNormSqHigh_le {d : ℕ} {s₀ s : ℝ} (h : s₀ < s) (η : ℝ) (hη : 0 < η) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ φ : Space d → ℝ, sobolevNormSq d s φ ≤ 1 →
      sobolevNormSqHigh d s₀ Λ φ ≤ ENNReal.ofReal (η ^ 2) := by
  have hneg : s₀ - s < 0 := by linarith
  set A : ℝ := (η ^ 2) ^ (1 / (s₀ - s)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨Real.sqrt A / (2 * Real.pi), by positivity, fun φ hφ => ?_⟩
  have hbase : A ≤ 1 + (2 * Real.pi * (Real.sqrt A / (2 * Real.pi))) ^ 2 := by
    have hs : (2 * Real.pi * (Real.sqrt A / (2 * Real.pi))) ^ 2 = A := by
      rw [mul_div_cancel₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Real.sq_sqrt (le_of_lt hApos)]
    linarith [hs]
  have hc : (1 + (2 * Real.pi * (Real.sqrt A / (2 * Real.pi))) ^ 2) ^ (s₀ - s)
      ≤ A ^ (s₀ - s) :=
    Real.rpow_le_rpow_of_nonpos hApos hbase (le_of_lt hneg)
  have hAs : A ^ (s₀ - s) = η ^ 2 := by
    rw [hA, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ η ^ 2)]
    rw [show 1 / (s₀ - s) * (s₀ - s) = 1 by
      rw [one_div, inv_mul_cancel₀ (ne_of_lt hneg)]]
    rw [Real.rpow_one]
  calc sobolevNormSqHigh d s₀ (Real.sqrt A / (2 * Real.pi)) φ
      ≤ ENNReal.ofReal ((1 + (2 * Real.pi * (Real.sqrt A / (2 * Real.pi))) ^ 2) ^ (s₀ - s)) *
          sobolevNormSq d s φ := sobolevNormSqHigh_le_mul (le_of_lt h) (by positivity) φ
    _ ≤ ENNReal.ofReal (η ^ 2) * 1 := by
        apply mul_le_mul
        · exact ENNReal.ofReal_le_ofReal (le_trans hc (le_of_eq hAs))
        · exact hφ
        · positivity
        · positivity
    _ = ENNReal.ofReal (η ^ 2) := mul_one _

end LatticeProb.Sobolev
