import LatticeProb.Prob.CorrelatedBMUnitPowerDimension

/-! # Direct-excursion dimension from subcritical barrier estimates -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

/-- Barrier estimates at every positive subcritical exponent yield the endpoint
bound for pairs of distinct direct-excursion partners. The constant may depend
on the exponent, but is uniform in the barrier and the Brownian law. -/
theorem ae_dimH_direct_excursion_pairs_le_of_subcritical_unit_power
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (d : ℝ≥0) (p : ℝ) (hp : 0 < p) (hd : 1 - p / 2 ≤ (d : ℝ))
    (hJ : ∀ r : ℝ, 0 < r → r < p → ∃ B : ℝ, 0 ≤ B ∧
      ∀ (q : ℝ), 0 < q → ∀ ν : Measure Path2, IsCorrelatedBM2 γ ν →
        ν (jointZeroBarrier q 1) ≤ ENNReal.ofReal (B * q ^ r)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ d := by
  let r : ℕ → ℝ := fun n => p - p / ((n : ℝ) + 2)
  let D : ℕ → ℝ≥0 := fun n => d + ⟨(p / 2) / ((n : ℝ) + 1), by positivity⟩
  have hdim (n : ℕ) : ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ D n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hr0 : 0 < r n := by
      dsimp [r]
      have : p / ((n : ℝ) + 2) < p := by
        apply (div_lt_iff₀ (by positivity)).2
        nlinarith
      linarith
    have hrp : r n < p := by
      dsimp [r]
      have hpos : 0 < p / ((n : ℝ) + 2) := by positivity
      linarith
    obtain ⟨B, hB, hbound⟩ := hJ (r n) hr0 hrp
    have hineq : 1 - r n / 2 ≤ (D n : ℝ) := by
      change 1 - (p - p / ((n : ℝ) + 2)) / 2 ≤
        (d : ℝ) + (p / 2) / ((n : ℝ) + 1)
      have hdiv : p / ((n : ℝ) + 2) ≤ p / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_left hp.le (by positivity) (by linarith)
      have heq : (p / 2) / ((n : ℝ) + 1) = (p / ((n : ℝ) + 1)) / 2 := by ring
      rw [heq]
      linarith
    exact ae_dimH_direct_excursion_pairs_le_of_unit_power hμ (D n) B (r n) hB hineq hbound
  filter_upwards [ae_all_iff.2 hdim] with ω hω
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((d : ℝ) + (p / 2) / ((n : ℝ) + 1)))
      atTop (𝓝 (ENNReal.ofReal (d : ℝ))) := by
    apply ENNReal.tendsto_ofReal
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (p / 2)
    simpa only [mul_one_div, mul_zero, add_zero] using h.const_add (d : ℝ)
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (d : ℝ) = (d : ℝ≥0∞))]
  apply ge_of_tendsto' hlim
  intro n
  have heq : (D n : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) + (p / 2) / ((n : ℝ) + 1)) := by
    change (D n : ℝ≥0∞) = ENNReal.ofReal ((D n : ℝ))
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [← heq]
  exact hω n

end LatticeProb.CorrelatedBM
