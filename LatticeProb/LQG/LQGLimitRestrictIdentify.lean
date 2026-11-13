import LatticeProb.LQG.LQGMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn

/-!
# Local identification of an LQG measure

Let `m` be the `γ`-LQG measure of a field, given as the vague limit on `ℂ` of the circle-average
approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales `ε = 2^{-k}`. On an open set
`U`, the restriction `m|_U` is determined by any vague limit on `U` of the same approximations:
the densities may be changed on Lebesgue-null sets, and vague limits on an open set of measures
finite on its compact subsets are unique.

This is the step that identifies the LQG measure of a field with a measure built from a local
decomposition of the field (for instance a Gaussian free field with zero boundary data plus a
continuous function, by the domain Markov property).

## Main results

* `LatticeProb.LQG.IsLQGLimit.restrict_eq_of_isVagueLimitOn`
* `LatticeProb.LQG.lqgApprox_dyadicScale_eq_withDensity`
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb.LQG

/-- The dyadic circle-average approximation `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz` depends on the
circle averages `h_{2^{-k}}` only up to Lebesgue-null sets. -/
theorem lqgApprox_dyadicScale_eq_withDensity {γ : ℝ} {hε : ℝ → ℂ → ℝ} {b : ℕ → ℂ → ℝ}
    {k : ℕ} (hb : hε (dyadicScale k) =ᵐ[volume] b k) :
    lqgApprox γ hε (dyadicScale k) = volume.withDensity fun z =>
      ENNReal.ofReal (QuantumZipper.radius k ^ (γ ^ 2 / 2) * Real.exp (γ * b k z)) := by
  unfold lqgApprox
  refine withDensity_congr_ae ?_
  filter_upwards [hb] with z hz
  exact congrArg (fun t => ENNReal.ofReal (QuantumZipper.radius k ^ (γ ^ 2 / 2) *
    Real.exp (γ * t))) hz

/-- **Local identification of an LQG measure.** Let `m` be the dyadic vague limit on `ℂ` of the
approximations `ε^{γ²/2} e^{γ h_ε(z)} dz`. If on an open set `U` the Lebesgue measures with
densities `2^{-kγ²/2} e^{γ b_k(z)}`, where `b_k = h_{2^{-k}}` Lebesgue-almost everywhere, converge
vaguely on `U` to `ν`, then `m` restricted to `U` equals `ν`. -/
theorem IsLQGLimit.restrict_eq_of_isVagueLimitOn {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (h : IsLQGLimit γ hε m) {U : Set ℂ} (hU : IsOpen U) {b : ℕ → ℂ → ℝ}
    (hb : ∀ k, hε (dyadicScale k) =ᵐ[volume] b k) {ν : Measure ℂ}
    (hν : QuantumZipper.IsVagueLimitOn U (fun k => volume.withDensity fun z =>
      ENNReal.ofReal (QuantumZipper.radius k ^ (γ ^ 2 / 2) * Real.exp (γ * b k z))) ν) :
    m.restrict U = ν := by
  have := h.isLocallyFiniteMeasure
  have h1 : QuantumZipper.IsVagueLimitOn U (fun k => lqgApprox γ hε (dyadicScale k))
      (m.restrict U) :=
    MatedCRTHarmonic.GMCFacts.isVagueLimitOn_restrict hU (fun _ hK => hK.measure_lt_top)
      h.tendsto_integral
  have h2 : (fun k => lqgApprox γ hε (dyadicScale k)) = fun k => volume.withDensity fun z =>
      ENNReal.ofReal (QuantumZipper.radius k ^ (γ ^ 2 / 2) * Real.exp (γ * b k z)) :=
    funext fun k => lqgApprox_dyadicScale_eq_withDensity (hb k)
  rw [h2] at h1
  exact QuantumZipper.isVagueLimitOn_unique hU h1 hν

end LatticeProb.LQG
