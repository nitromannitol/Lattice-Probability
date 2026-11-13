import LatticeProb.LQG.LQGDyadicScaling

/-! # Ratios of concentric ball masses under dyadic scaling

Let `μ` be the γ-LQG measure of the circle-average field `hcirc`, `z ∈ ℂ`, `j ∈ ℕ`, `r = 2^{-j}`, and let `μ'` be the
γ-LQG measure of the recentred and dilated field `recentredField hcirc j z`. The exact scaling relation
`μ(B(z, r ρ)) = r^{γ Q} e^{γ h_r(z)} μ'(B(0, ρ))` (Duplantier-Sheffield 2011, Proposition 2.1;
`LQGDyadicScaling.ae_measure_ball_eq`) has a factor that does not depend on `ρ`, so it cancels in a ratio of two
concentric balls: almost surely

  `μ(B(z, r ρ')) / μ(B(z, r ρ)) = μ'(B(0, ρ')) / μ'(B(0, ρ))`  for all `ρ, ρ' > 0`

(`ae_measure_ball_div_eq`), and the event `t μ(B(z, r ρ)) < μ(B(z, r ρ'))` has the same probability as the event
`t μ'(B(0, ρ)) < μ'(B(0, ρ'))` (`measure_mul_ball_lt_ball_eq`). Since the recentred field is again a whole-plane GFF,
moment bounds for the LQG measure of a whole-plane GFF that are uniform over the probability space apply to `μ'`.
This is the invariance of the ratios of ball masses under translation and scaling used in the proof of
Berestycki-Gwynne, arXiv:2003.10320, Lemma A.2.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace LQGDyadicScaling

/-- **Ratios of concentric ball masses are invariant under dyadic recentring.** Almost surely, for all radii
`ρ, ρ' > 0`, `μ(B(z, 2^{-j} ρ')) / μ(B(z, 2^{-j} ρ)) = μ'(B(0, ρ')) / μ'(B(0, ρ))`, where `μ'` is the LQG measure of
the recentred field. -/
theorem ae_measure_ball_div_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') :
    ∀ᵐ ω ∂P, ∀ ρ ρ' : ℝ, 0 < ρ → 0 < ρ' →
      μ ω (ball z (dyadicScale j * ρ')) / μ ω (ball z (dyadicScale j * ρ)) =
        μ' ω (ball 0 ρ') / μ' ω (ball 0 ρ) := by
  filter_upwards [ae_measure_ball_eq hγ hμ j z hμ'] with ω hω ρ ρ' hρ hρ'
  rw [hω ρ' hρ', hω ρ hρ,
    ENNReal.mul_div_mul_left _ _ (dyadicFactor_ne_zero _ _ _) (dyadicFactor_ne_top _ _ _)]

/-- **The ratio event of two concentric balls has a scale- and centre-free probability.** For `t ∈ [0, ∞]` and
`ρ, ρ' > 0`, `P(t μ(B(z, 2^{-j} ρ)) < μ(B(z, 2^{-j} ρ'))) = P(t μ'(B(0, ρ)) < μ'(B(0, ρ')))`, where `μ'` is the
LQG measure of the recentred field. -/
theorem measure_mul_ball_lt_ball_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) (j : ℕ) (z : ℂ)
    (hμ' : IsLQGMeasure P γ (recentredField hcirc j z) μ') (t : ℝ≥0∞) {ρ ρ' : ℝ} (hρ : 0 < ρ)
    (hρ' : 0 < ρ') :
    P {ω | t * μ ω (ball z (dyadicScale j * ρ)) < μ ω (ball z (dyadicScale j * ρ'))} =
      P {ω | t * μ' ω (ball 0 ρ) < μ' ω (ball 0 ρ')} := by
  apply measure_congr
  filter_upwards [ae_measure_ball_eq hγ hμ j z hμ'] with ω hω
  have h0 := dyadicFactor_ne_zero γ j (hcirc ω (dyadicScale j) z)
  have htop := dyadicFactor_ne_top γ j (hcirc ω (dyadicScale j) z)
  change (t * μ ω (ball z (dyadicScale j * ρ)) < μ ω (ball z (dyadicScale j * ρ'))) =
    (t * μ' ω (ball 0 ρ) < μ' ω (ball 0 ρ'))
  rw [hω ρ hρ, hω ρ' hρ', mul_left_comm]
  exact propext (ENNReal.mul_lt_mul_iff_right h0 htop)

end LQGDyadicScaling

end LatticeProb.LQG
