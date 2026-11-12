import Mathlib
import LatticeProb.LQG.GMCAffineCovariance
import LatticeProb.LQG.LQGWeylScaling

/-!
# Weyl scaling of the Liouville quantum gravity measure along arbitrary scales

If the approximations `ε^{γ²/2} e^{γ h_ε(z)} dz` of a field converge vaguely to `μ` along a sequence of scales
`s k → 0` (not necessarily dyadic), and `f : ℂ → ℝ` is continuous, then the approximations of the field with
circle averages `h_ε + f_ε` converge vaguely, along the same scales, to `e^{γ f} μ`
(`isLQGLimitAlong_addCircleAverage`). This is the argument of the dyadic statement
`LQGWeylScalingDerived.isLQGLimit_addCircleAverage`: the density `e^{γ f_ε}` converges uniformly on compact sets
as `ε → 0`, and the approximations have locally bounded mass since they converge vaguely.
-/

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG
open LatticeProb.LQG.LQGWeylScalingDerived
open LatticeProb.LQG.ProfileDerived (isLocallyFiniteMeasure_lqgApprox)
open LatticeProb.Gauss.Section6 (continuous_circleAverage_radius_center)

namespace LatticeProb.LQG.LQGWeylScalingAlong

/-- Multiplication by a continuous test preserves uniform convergence on compact sets of the exponential
circle-average weights `e^{γ f_{s n}}` along any sequence of radii `s n → 0`. -/
theorem tendstoUniformlyOn_test_exp_circleAverage_along (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) {s : ℕ → ℝ}
    (hs0 : Tendsto s atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n z => φ z * Real.exp (γ * Real.circleAverage f z (s n)))
      (fun z => φ z * Real.exp (γ * f z)) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) :=
    (hφ.comp continuous_snd).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_circleAverage_radius_center hf)))
  have hu : UniformContinuousOn
      (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * Real.exp (γ * Real.circleAverage f z r)) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * Real.exp (γ * Real.circleAverage f z r))
      (fun z => φ z * Real.exp (γ * f z)) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  exact hs0.eventually (ht' ε hε)

/-- **Weyl scaling along arbitrary scales.** If the approximations of `hε` converge vaguely to `μ` along scales
`s n ≥ 0` with `s n → 0`, and the regularized field is continuous at these scales, then for every continuous `f`
the approximations of the field with circle averages `hε + f_ε` converge vaguely along `s` to `e^{γ f} μ`. -/
theorem isLQGLimitAlong_addCircleAverage {γ : ℝ} {hε : ℝ → ℂ → ℝ} {s : ℕ → ℝ} {μ : Measure ℂ}
    (hμ : IsLQGLimitAlong γ hε s μ) (hs : ∀ n, 0 ≤ s n) (hs0 : Tendsto s atTop (𝓝 0))
    (hh : ∀ n, Continuous (hε (s n))) (f : ℂ → ℝ) (hf : Continuous f) :
    IsLQGLimitAlong γ (addCircleAverage hε f) s
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))) := by
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ hε (s n)
  let : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n => isLocallyFiniteMeasure_lqgApprox γ (hh n)
  have hfexp : Continuous (fun z => Real.exp (γ * f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf)
  constructor
  · exact IsLocallyFiniteMeasure.withDensity_ofReal hfexp
  · intro φ hφ hφc
    let K := tsupport φ
    have hK : IsCompact K := hφc
    let g : ℕ → ℂ → ℝ := fun n z => φ z * Real.exp (γ * Real.circleAverage f z (s n))
    let g₀ : ℂ → ℝ := fun z => φ z * Real.exp (γ * f z)
    have hg : ∀ n, Integrable (g n) (ν n) := by
      intro n
      have hav : Continuous (fun z => Real.circleAverage f z (s n)) :=
        (continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id)
      have hgc : Continuous (g n) := hφ.mul (Real.continuous_exp.comp (continuous_const.mul hav))
      exact hgc.integrable_of_hasCompactSupport hφc.mul_right
    have huni : TendstoUniformlyOn g g₀ atTop K :=
      tendstoUniformlyOn_test_exp_circleAverage_along γ f φ hf hφ hK hs0
    have hoff : ∀ n z, z ∉ K → g n z = g₀ z := by
      intro n z hz
      have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [g, g₀, hz']
    have hlim := tendsto_integral_of_uniformOn_compact ν μ hμ.tendsto_integral hK
      (hφ.mul hfexp) hφc.mul_right hg huni hoff
    have heq (n : ℕ) : (∫ z, φ z ∂(lqgApprox γ (addCircleAverage hε f) (s n))) =
        ∫ z, g n z ∂(ν n) := by
      rw [lqgApprox_addCircleAverage γ (s n) (hs n) hε (hh n) f hf]
      exact integral_withDensity_exp (ν n) γ (fun z => Real.circleAverage f z (s n)) φ
        ((continuous_circleAverage_radius_center hf).comp (continuous_const.prodMk continuous_id))
    simp_rw [heq, integral_withDensity_exp μ γ f φ hf]
    exact hlim

end LatticeProb.LQG.LQGWeylScalingAlong
