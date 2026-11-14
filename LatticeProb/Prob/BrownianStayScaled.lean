import LatticeProb.Prob.BrownianStepTimeScaled

/-!
# Staying in a ball up to the `K`-th displacement time at every spatial scale

`measure_stays_in_ball_superpoly` bounds the probability that a Brownian motion `B` on `ℝ ^ d`
started at `0` stays in the unit ball up to its `K`-th displacement time of size `r`, for
`K = ⌊r ^ -(2 + ζ)⌋`, by `C r ^ p` for every `p`. By Brownian scaling the same bound holds, with the
same constant, for the ball of radius `a` and displacements of size `a r`, for every `a > 0`
(`measure_stays_in_ball_superpoly_scaled`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

universe u

namespace LatticeProb

/-- **Staying in a ball at scale `a`.** For a Brownian motion `B` on `ℝ ^ d` started at `0`,
`0 < ζ < 1` and `p ∈ ℕ`, there is `C` such that for all `a > 0` and `0 < r < 1` the probability
that `B` stays in the ball of radius `a` up to its `K`-th displacement time of size `a r`,
`K = ⌊r ^ -(2 + ζ)⌋`, is at most `C r ^ p`. The constant does not depend on `a`. -/
theorem measure_stays_in_ball_superpoly_scaled (d : ℕ) (hd : 0 < d) {ζ : ℝ} (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (p : ℕ) :
    ∃ C : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d 0 B P →
      ∀ a : ℝ≥0, 0 < a → ∀ r : ℝ≥0, 0 < r → r < 1 →
      P {ω | ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime (fun t => B t ω) ((a : ℝ) * r)
            ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊ → ‖B t ω‖ < a}
        ≤ ENNReal.ofReal (C * (r : ℝ) ^ p) := by
  obtain ⟨C, hC⟩ := measure_stays_in_ball_superpoly.{u} d hd hζ0 hζ1 p
  refine ⟨C, fun Ω _ P _ B hB a ha r hr0 hr1 => ?_⟩
  have ha' : (0 : ℝ) < a := ha
  have hc : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have hsq : √(((a ^ 2 : ℝ≥0)) : ℝ) = a := by
    rw [NNReal.coe_pow, Real.sqrt_sq a.coe_nonneg]
  have hB' := hB.timeScale hc
  rw [hsq] at hB'
  refine le_trans (measure_mono ?_) (hC Ω P _ hB' r hr0 hr1)
  intro ω hω t ht
  set φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (a ^ 2) (pow_pos ha 2) with hφ
  have hfun : (fun s => (a : ℝ)⁻¹ • B (a ^ 2 * s) ω) = (fun s => (a : ℝ)⁻¹ • B s ω) ∘ φ := by
    funext s
    rfl
  have hst : stepTime (fun s => (a : ℝ)⁻¹ • B s ω) (r : ℝ) ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊ =
      stepTime (fun s => B s ω) ((a : ℝ) * r) ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊ := by
    have := stepTime_const_smul (fun s => B s ω) (inv_pos.2 ha') ((a : ℝ) * r)
      ⌊(r : ℝ) ^ (-(2 + ζ))⌋₊
    rwa [inv_mul_cancel_left₀ ha'.ne'] at this
  rw [hfun, coe_lt_stepTime_comp_iff, hst] at ht
  have h1 : ‖B (φ t) ω‖ < a := hω (φ t) ht
  have h2 : φ t = a ^ 2 * t := rfl
  show ‖(a : ℝ)⁻¹ • B (a ^ 2 * t) ω‖ < 1
  rw [← h2, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 a.coe_nonneg)]
  calc (a : ℝ)⁻¹ * ‖B (φ t) ω‖ < (a : ℝ)⁻¹ * a :=
        mul_lt_mul_of_pos_left h1 (inv_pos.2 ha')
    _ = 1 := inv_mul_cancel₀ ha'.ne'

end LatticeProb
