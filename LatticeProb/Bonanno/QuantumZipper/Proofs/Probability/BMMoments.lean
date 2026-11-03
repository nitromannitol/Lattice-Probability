/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.BMMoments at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Moments of Brownian motion

For a (pre-)Brownian motion `B : ℝ≥0 → Ω → ℝ` under a probability measure `P`, this file
records:

* `hasLaw_gaussianReal` : the law of `B t` is `gaussianReal 0 t`.
* `integral_eq_zero`, `integral_sq`, `integral_pow_three`, `integral_pow_four` : the first four
  raw moments of `B t`.
* `integrable_pow`, `integral_abs_pow_le` : for every `n`, `|B t|^n` is integrable with an
  explicit bound `gaussianAbsMoment n * t^(n/2)`, where `gaussianAbsMoment n` is the `n`-th
  absolute moment of the standard Gaussian.
* `integral_integral_abs_pow_le` : a Tonelli/Fubini bound on the time-integral of the same
  quantity, for continuous paths.
* `shift_indepFun_isPreBrownianReal` : a bundled restatement of the weak Markov property.

Reference: `Mathlib.Probability.BrownianMotion.Basic`,
`Mathlib.Probability.Distributions.Gaussian.Real`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-! ### 1. The law of `B t` -/

/-- The law of `B t` is the centered Gaussian of variance `t`. This is a direct restatement of
`IsPreBrownianReal.hasLaw_eval`. -/
theorem hasLaw_gaussianReal (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    HasLaw (B t) (gaussianReal 0 t) P :=
  hB.hasLaw_eval t

/-! ### 2. Calculus: derivatives of `t ↦ exp (v * t ^ 2 / 2)`

These are auxiliary real-analysis facts used to compute the third and fourth moments of
`gaussianReal 0 v` through its moment-generating function
(`mgf_fun_id_gaussianReal`, `iteratedDeriv_mgf_zero`). All of them are elementary chain/product
rule computations; only the value of the relevant derivative at `0` is eventually needed, but we
record the derivative as a function of `s` since that is what lets us differentiate again. -/

private lemma hasDerivAt_gaussianExp (v s : ℝ) :
    HasDerivAt (fun x => Real.exp (v * x ^ 2 / 2)) (v * s * Real.exp (v * s ^ 2 / 2)) s := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
  have h3 : HasDerivAt (fun x : ℝ => v * x ^ 2 / 2) (v * (2 * s) / 2) s :=
    (h1.const_mul v).div_const 2
  have h4 := h3.exp
  convert h4 using 1
  ring

/-- Differentiating `P * exp(v * x ^ 2 / 2)` once more, given the derivative `P'` of `P` at `s`. -/
private lemma hasDerivAt_mul_gaussianExp {v : ℝ} {Poly : ℝ → ℝ} {Poly' s : ℝ}
    (hP : HasDerivAt Poly Poly' s) :
    HasDerivAt (fun x => Poly x * Real.exp (v * x ^ 2 / 2))
      ((Poly' + Poly s * (v * s)) * Real.exp (v * s ^ 2 / 2)) s := by
  have h := hP.mul (hasDerivAt_gaussianExp v s)
  have hval : Poly' * Real.exp (v * s ^ 2 / 2) + Poly s * (v * s * Real.exp (v * s ^ 2 / 2)) =
      (Poly' + Poly s * (v * s)) * Real.exp (v * s ^ 2 / 2) := by ring
  rwa [hval] at h

private lemma iteratedDeriv_one_gaussianExp (v : ℝ) :
    iteratedDeriv 1 (fun x => Real.exp (v * x ^ 2 / 2)) =
      fun s => v * s * Real.exp (v * s ^ 2 / 2) := by
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_zero]
  exact (hasDerivAt_gaussianExp v s).deriv

private lemma iteratedDeriv_two_gaussianExp (v : ℝ) :
    iteratedDeriv 2 (fun x => Real.exp (v * x ^ 2 / 2)) =
      fun s => (v + v ^ 2 * s ^ 2) * Real.exp (v * s ^ 2 / 2) := by
  funext s
  rw [iteratedDeriv_succ, iteratedDeriv_one_gaussianExp]
  have hP : HasDerivAt (fun x : ℝ => v * x) v s := by
    simpa using (hasDerivAt_id s).const_mul v
  have h := hasDerivAt_mul_gaussianExp (v := v) hP
  rw [h.deriv]
  ring

/-! ### 3. The first four raw moments of `gaussianReal 0 v` -/

private lemma mgf_gaussianReal_eq (v : ℝ≥0) :
    mgf (fun x : ℝ => x) (gaussianReal 0 v) = fun s => Real.exp ((v : ℝ) * s ^ 2 / 2) := by
  funext s
  rw [mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]

private lemma mem_interior_integrableExpSet_gaussianReal (v : ℝ≥0) :
    (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 v)) := by
  rw [integrableExpSet_fun_id_gaussianReal]
  simp

private lemma integral_pow_two_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂ (gaussianReal 0 v) = (v : ℝ) := by
  have h2 := iteratedDeriv_mgf_zero (mem_interior_integrableExpSet_gaussianReal v) 2
  rw [mgf_gaussianReal_eq, iteratedDeriv_two_gaussianExp] at h2
  simp only [Pi.pow_apply] at h2
  simpa using h2.symm

theorem integral_eq_zero (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∫ ω, B t ω ∂P = 0 :=
  hB.integral_eval t

theorem integral_sq (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∫ ω, B t ω ^ 2 ∂P = (t : ℝ) := by
  have h := (hasLaw_gaussianReal hB t).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [Function.comp_def] at h
  rw [h, integral_pow_two_gaussianReal]

/-! ### 4. Absolute moments and an explicit power-law bound -/

/-- The `n`-th absolute moment of the standard Gaussian `gaussianReal 0 1`. This is the explicit
constant `C n` used in `integral_abs_pow_le` and `integral_integral_abs_pow_le`. -/
def gaussianAbsMoment (n : ℕ) : ℝ := ∫ x, |x| ^ n ∂ (gaussianReal 0 1)

theorem gaussianAbsMoment_nonneg (n : ℕ) : 0 ≤ gaussianAbsMoment n :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) n

private lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v) := by
  have hmem : MemLp (fun x : ℝ => x) (n : ℝ≥0) (gaussianReal 0 v) := memLp_id_gaussianReal n
  have hint : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal 0 v) := hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

/-- Scaling identity: the `n`-th absolute moment of `gaussianReal 0 v` is `v ^ (n/2)` times the
`n`-th absolute moment of the standard Gaussian. Obtained from `gaussianReal 0 v` being the
pushforward of `gaussianReal 0 1` under `x ↦ √v * x`. -/
private lemma integral_abs_pow_gaussianReal_eq (v : ℝ≥0) (n : ℕ) :
    ∫ x, |x| ^ n ∂ (gaussianReal 0 v) = (v : ℝ) ^ ((n : ℝ) / 2) * gaussianAbsMoment n := by
  have hv0 : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hsqrt : (0 : ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hcsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt hv0
  have hmap : gaussianReal (0 : ℝ) v =
      (gaussianReal (0 : ℝ) 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq
      push_cast
      rw [hcsq]
      ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, |Real.sqrt v * x| ^ n = (v : ℝ) ^ ((n : ℝ) / 2) * |x| ^ n := by
    intro x
    rw [abs_mul, abs_of_nonneg hsqrt, mul_pow]
    congr 1
    rw [← Real.rpow_natCast (Real.sqrt v) n, Real.sqrt_eq_rpow, ← Real.rpow_mul hv0]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  rfl

theorem integrable_pow (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => |B t ω| ^ n) P := by
  have h := (hasLaw_gaussianReal hB t).integrable_comp
    (f := fun x : ℝ => |x| ^ n) (integrable_abs_pow_gaussianReal t n)
  simpa [Function.comp_def] using h

theorem integral_abs_pow_le (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    ∫ ω, |B t ω| ^ n ∂P ≤ gaussianAbsMoment n * (t : ℝ) ^ ((n : ℝ) / 2) := by
  have heq : ∫ ω, |B t ω| ^ n ∂P = ∫ x, |x| ^ n ∂ (gaussianReal 0 t) := by
    have h := (hasLaw_gaussianReal hB t).integral_comp (f := fun x : ℝ => |x| ^ n) (by fun_prop)
    rwa [Function.comp_def] at h
  rw [heq, integral_abs_pow_gaussianReal_eq]
  exact le_of_eq (mul_comm _ _)

/-! ### 5. Joint measurability of a path-continuous process -/

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

/-! ### 6. A Tonelli/Fubini bound on the pathwise time-integral -/

theorem integral_integral_abs_pow_le (hB : IsPreBrownianReal B P)
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
      have hrint : Integrable (g r) P := integrable_pow hB r.toNNReal n
      have hrbound : ∫ ω, g r ω ∂P ≤ gaussianAbsMoment n * r ^ ((n : ℝ) / 2) := by
        have h := integral_abs_pow_le hB r.toNNReal n
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

/-! ### 7. The weak Markov property, restated -/

/-- Convenient bundling of `IsPreBrownianReal.shift` and `IsPreBrownianReal.indepFun_shift`: the
shifted process `s ↦ B (t + s) - B t` is again pre-Brownian, and is independent of the family
`(B r)_{r ≤ t}`. -/
theorem shift_indepFun_isPreBrownianReal (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsPreBrownianReal (fun s ω => B (t + s) ω - B t ω) P ∧
      IndepFun (fun ω s => B (t + s) ω - B t ω) (fun ω (r : Set.Iic t) => B r ω) P :=
  ⟨hB.shift t, hB.indepFun_shift t⟩

end QuantumZipper
