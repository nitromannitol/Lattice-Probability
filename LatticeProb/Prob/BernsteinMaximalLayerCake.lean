/-
# The weak-type / truncation step toward the `L^p` Doob maximal inequality

`LatticeProb.integral_rpow_eq_integral_meas_le` (`Prob/BernsteinLayerCake.lean`) is the Bochner
layer-cake identity `∫ M^p dμ = ∫_0^∞ p t^{p-1} μ{M ≥ t} dt`.  Feeding the
weak-type (Doob) bound
`μ{M ≥ t} ≤ t⁻¹ ∫_{M ≥ t} f` into the integrand turns it into the
double-integral form

  `∫ M^p dμ ≤ ∫_0^∞ p t^{p-2} (∫_{M ≥ t} f) dt`.

This is the truncation/Fubini reduction: the remaining steps to the `L^p` Doob maximal inequality
are the exchange of the two integrals (Tonelli, giving `(p/(p-1)) ∫ f M^{p-1}`) and Hölder.  The
reduction below is unconditional apart from the finiteness hypotheses, so no integral collapses
to the junk `0`; it contains no new external input and is not imported by the root.
-/
import LatticeProb.Prob.BernsteinLayerCake

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The truncation step of the `L^p` Doob maximal inequality.**  For `p > 1`, a non-negative
a.e.-measurable `M` with `M^p` integrable, and `f` satisfying the weak-type (Doob) bound
`μ{M ≥ t} ≤ t⁻¹ ∫_{M ≥ t} f`,

  `∫ M^p dμ ≤ ∫_0^∞ p t^{p-2} (∫_{M ≥ t} f) dt`.

Substituting the layer-cake identity reduces it to a pointwise bound on `(0, ∞)`. -/
theorem integral_rpow_le_integral_weak_type [IsProbabilityMeasure μ] {M f : Ω → ℝ} {p : ℝ}
    (hp : 1 < p) (hMnn : 0 ≤ᵐ[μ] M) (hMint : Integrable (fun ω => M ω ^ p) μ)
    (hweak : ∀ t : ℝ, 0 < t →
      (μ {ω | t ≤ M ω}).toReal ≤ t⁻¹ * ∫ ω in {ω | t ≤ M ω}, f ω ∂μ)
    (hint : Integrable (fun t : ℝ => p * t ^ (p - 1) * (μ {ω | t ≤ M ω}).toReal)
      (volume.restrict (Set.Ioi 0)))
    (hbound : Integrable (fun t : ℝ => p * t ^ (p - 2) *
      (∫ ω in {ω | t ≤ M ω}, f ω ∂μ)) (volume.restrict (Set.Ioi 0))) :
    ∫ ω, M ω ^ p ∂μ
      ≤ ∫ t in Set.Ioi 0, p * t ^ (p - 2) * (∫ ω in {ω | t ≤ M ω}, f ω ∂μ) := by
  rw [integral_rpow_eq_integral_meas_le (by linarith : 0 < p) hMnn hMint]
  refine integral_mono_ae hint hbound ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  have hcoef : (0 : ℝ) ≤ p * t ^ (p - 1) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le _)
  have hle := mul_le_mul_of_nonneg_left (hweak t ht0) hcoef
  have hpow : t ^ (p - 1) * t⁻¹ = t ^ (p - 2) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht0 (p - 1) (-1)]
    congr 1
    ring
  calc p * t ^ (p - 1) * (μ {ω | t ≤ M ω}).toReal
      ≤ p * t ^ (p - 1) * (t⁻¹ * ∫ ω in {ω | t ≤ M ω}, f ω ∂μ) := hle
    _ = p * t ^ (p - 2) * (∫ ω in {ω | t ≤ M ω}, f ω ∂μ) := by
        rw [← hpow]
        ring

end LatticeProb
