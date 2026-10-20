/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: QuantumZipper/Proofs/Probability/BMMoments.lean.
-/

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Prob.BrownianAbsMoments
import LatticeProb.Prob.BrownianContAll

/-!
# Time-integrated absolute moments of Brownian motion

For a pre-Brownian motion `B : ℝ≥0 → Ω → ℝ` under a probability measure `P` whose paths are
continuous, this file proves that the expectation of the time-integral of `|B r| ^ n` over
`[0, s]` is at most `gaussianAbsMoment n * s ^ (1 + n / 2)`. The proof uses Tonelli's theorem
after checking that `(r, ω) ↦ |B r ω| ^ n` is jointly measurable, which follows from continuity of
the paths by a dyadic approximation in the time variable.

The one-time moment bounds it relies on are `brownian_integrable_abs_pow` and
`brownian_integral_abs_pow_le` from `LatticeProb.Prob.BrownianAbsMoments`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- A dyadic rounding down of `r` at scale `2 ^ (-k)` converges to `r` as `k → ∞`. -/
private lemma tendsto_dyadicRound (r : ℝ) :
    Tendsto (fun k : ℕ => (⌊r * 2 ^ k⌋ : ℝ) / 2 ^ k) atTop (𝓝 r) := by
  have hpos : ∀ k : ℕ, (0 : ℝ) < 2 ^ k := fun k => by positivity
  have hlow : ∀ k : ℕ, (⌊r * 2 ^ k⌋ : ℝ) / 2 ^ k ≤ r := fun k =>
    (div_le_iff₀ (hpos k)).2 (Int.floor_le (r * 2 ^ k))
  have hhigh : ∀ k : ℕ, r ≤ (⌊r * 2 ^ k⌋ : ℝ) / 2 ^ k + (2 ^ k)⁻¹ := by
    intro k
    have h1 : r < ((⌊r * 2 ^ k⌋ : ℝ) + 1) / 2 ^ k :=
      (lt_div_iff₀ (hpos k)).2 (Int.lt_floor_add_one _)
    rw [add_div, one_div] at h1
    exact h1.le
  have hzero : Tendsto (fun k : ℕ => r - (⌊r * 2 ^ k⌋ : ℝ) / 2 ^ k) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
      have h2' : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [inv_pow] using h2'
    exact squeeze_zero (f := fun k : ℕ => r - (⌊r * 2 ^ k⌋ : ℝ) / 2 ^ k)
      (g := fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) (fun k => by linarith [hlow k])
      (fun k => by linarith [hhigh k]) h2
  have := (tendsto_const_nhds (x := r) (f := (atTop : Filter ℕ))).sub hzero
  simpa using this

/-- If `F` is measurable in its first argument for every fixed second argument, and continuous
in its second argument for every fixed first argument, then `F` is jointly measurable. Proved by
approximating the first argument along a dyadic grid (countably many values) and passing to the
limit using continuity. -/
private lemma measurable_uncurry_of_continuous {F : ℝ → Ω → ℝ}
    (hFm : ∀ r, Measurable (F r)) (hFc : ∀ ω, Continuous fun r => F r ω) :
    Measurable (Function.uncurry F) := by
  have hstep : ∀ k : ℕ, Measurable (fun p : ℝ × Ω => F ((⌊p.1 * 2 ^ k⌋ : ℝ) / 2 ^ k) p.2) := by
    intro k
    have hG : Measurable (fun q : ℤ × Ω => F ((q.1 : ℝ) / 2 ^ k) q.2) :=
      measurable_from_prod_countable_right (fun j => hFm ((j : ℝ) / 2 ^ k))
    have hφ : Measurable (fun p : ℝ × Ω => ((⌊p.1 * 2 ^ k⌋ : ℤ), p.2)) :=
      (Int.measurable_floor.comp (measurable_fst.mul_const _)).prodMk measurable_snd
    exact hG.comp hφ
  apply measurable_of_tendsto_metrizable hstep
  rw [tendsto_pi_nhds]
  rintro ⟨r, ω⟩
  exact ((hFc ω).tendsto r).comp (tendsto_dyadicRound r)

/-- For a Brownian motion with continuous paths, the expectation of the time-integral of
`|B r| ^ n` over `[0, s]` is at most `gaussianAbsMoment n * s ^ (1 + n / 2)`. -/
theorem brownian_integral_integral_abs_pow_le (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t : ℝ≥0, Measurable (B t)) (hcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∫ ω, (∫ r in (0 : ℝ)..s, |B (Real.toNNReal r) ω| ^ n) ∂P ≤
      gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set g : ℝ → Ω → ℝ := fun r ω => |B (Real.toNNReal r) ω| ^ n with hgdef
  have hgnn : ∀ r ω, 0 ≤ g r ω := fun r ω => pow_nonneg (abs_nonneg _) n
  have hgmeas : ∀ r, Measurable (g r) :=
    fun r => (continuous_abs.pow n).measurable.comp (hmeas r.toNNReal)
  have hgcont : ∀ ω, Continuous fun r => g r ω :=
    fun ω => ((hcont ω).comp continuous_real_toNNReal).abs.pow n
  have hjoint : Measurable (Function.uncurry g) := measurable_uncurry_of_continuous hgmeas hgcont
  have hHeq : ∀ ω, (∫ r in (0 : ℝ)..s, g r ω) = ∫ r in Set.Ioc (0 : ℝ) s, g r ω ∂volume :=
    fun ω => intervalIntegral.integral_of_le hs
  have hHnn : ∀ ω, 0 ≤ ∫ r in (0 : ℝ)..s, g r ω :=
    fun ω => intervalIntegral.integral_nonneg hs fun r _ => hgnn r ω
  have hHmeas : StronglyMeasurable (fun ω => ∫ r in (0 : ℝ)..s, g r ω) := by
    have hsm : StronglyMeasurable (fun p : Ω × ℝ => g p.2 p.1) :=
      (hjoint.comp measurable_swap).stronglyMeasurable
    simp_rw [hHeq]
    exact hsm.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) s))
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hHnn)
    hHmeas.aestronglyMeasurable]
  have key : ∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..s, g r ω) ∂P ≤
      ENNReal.ofReal (gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2)) := by
    have hstep1 : ∀ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..s, g r ω) ≤
        ∫⁻ r in Set.Ioc (0 : ℝ) s, ENNReal.ofReal (g r ω) ∂volume := by
      intro ω
      rw [hHeq ω, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun r => hgnn r ω)
        (hgcont ω).measurable.aestronglyMeasurable]
      exact ENNReal.ofReal_toReal_le
    have hmeasENN : Measurable (Function.uncurry fun (ω : Ω) (r : ℝ) => ENNReal.ofReal (g r ω)) :=
      ENNReal.measurable_ofReal.comp (hjoint.comp measurable_swap)
    have hswap : ∫⁻ ω, ∫⁻ r in Set.Ioc (0 : ℝ) s, ENNReal.ofReal (g r ω) ∂volume ∂P =
        ∫⁻ r in Set.Ioc (0 : ℝ) s, ∫⁻ ω, ENNReal.ofReal (g r ω) ∂P ∂volume :=
      lintegral_lintegral_swap hmeasENN.aemeasurable
    have hperslice : ∀ r ∈ Set.Ioc (0 : ℝ) s,
        (∫⁻ ω, ENNReal.ofReal (g r ω) ∂P) ≤
          ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2)) := by
      intro r hr
      have hrint : Integrable (g r) P := brownian_integrable_abs_pow hB r.toNNReal n
      have hrbound : ∫ ω, g r ω ∂P ≤ gaussianAbsMoment n * r ^ ((n : ℝ) / 2) := by
        have h := brownian_integral_abs_pow_le hB r.toNNReal n
        rwa [Real.coe_toNNReal r hr.1.le] at h
      have hrbound' : ∫ ω, g r ω ∂P ≤ gaussianAbsMoment n * s ^ ((n : ℝ) / 2) := by
        refine hrbound.trans ?_
        gcongr
        exacts [gaussianAbsMoment_nonneg n, hr.1.le, hr.2]
      calc ∫⁻ ω, ENNReal.ofReal (g r ω) ∂P
          = ENNReal.ofReal (∫ ω, g r ω ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal hrint
              (Filter.Eventually.of_forall fun ω => hgnn r ω)).symm
        _ ≤ ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2)) :=
            ENNReal.ofReal_le_ofReal hrbound'
    calc ∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..s, g r ω) ∂P
        ≤ ∫⁻ ω, ∫⁻ r in Set.Ioc (0 : ℝ) s, ENNReal.ofReal (g r ω) ∂volume ∂P :=
          lintegral_mono_ae (Filter.Eventually.of_forall hstep1)
      _ = ∫⁻ r in Set.Ioc (0 : ℝ) s, ∫⁻ ω, ENNReal.ofReal (g r ω) ∂P ∂volume := hswap
      _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) s, ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2))
            ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hperslice r hr
      _ = ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2)) * volume (Set.Ioc (0 : ℝ) s) :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2)) * ENNReal.ofReal s := by
          rw [Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (gaussianAbsMoment n * s ^ ((n : ℝ) / 2) * s) := by
          rw [← ENNReal.ofReal_mul
            (mul_nonneg (gaussianAbsMoment_nonneg n) (Real.rpow_nonneg hs _))]
      _ = ENNReal.ofReal (gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2)) := by
          rcases hs.eq_or_lt with hs0 | hs0
          · simp [← hs0, Real.zero_rpow (show (1 + (n : ℝ) / 2) ≠ 0 by positivity)]
          · have hexp : s ^ ((n : ℝ) / 2) * s = s ^ (1 + (n : ℝ) / 2) := by
              rw [Real.rpow_add hs0, Real.rpow_one]; ring
            rw [mul_assoc, hexp]
  calc (∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..s, g r ω) ∂P).toReal
      ≤ (ENNReal.ofReal (gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top key
    _ = gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2) :=
        ENNReal.toReal_ofReal (mul_nonneg (gaussianAbsMoment_nonneg n) (Real.rpow_nonneg hs _))

/-! ### Nonvacuity -/

namespace BrownianAbsMomentsFubiniExample

/-- The hypotheses of `brownian_integral_integral_abs_pow_le` are satisfied by a pre-Brownian
motion with everywhere continuous paths, so that theorem is not vacuous. -/
theorem hypotheses_satisfiable :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
      IsPreBrownianReal B P ∧ (∀ t : ℝ≥0, Measurable (B t)) ∧
        ∀ ω, Continuous fun t : ℝ≥0 => B t ω := by
  obtain ⟨Ω, mΩ, P, B, hmeas, hB, hcont⟩ := exists_isBrownianReal_cont
  exact ⟨Ω, mΩ, P, B, hB.toIsPreBrownianReal, hmeas, hcont⟩

/-- The time-integral bound holds for the Brownian motion produced by
`hypotheses_satisfiable`. -/
theorem bound_on_model (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
      ∫ ω, (∫ r in (0 : ℝ)..s, |B (Real.toNNReal r) ω| ^ n) ∂P ≤
        gaussianAbsMoment n * s ^ (1 + (n : ℝ) / 2) := by
  obtain ⟨Ω, mΩ, P, B, hB, hmeas, hcont⟩ := hypotheses_satisfiable
  exact ⟨Ω, mΩ, P, B, brownian_integral_integral_abs_pow_le hB hmeas hcont n s hs⟩

end BrownianAbsMomentsFubiniExample

end LatticeProb
