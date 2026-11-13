/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LemmaA4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LemmaA4Analytic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import LatticeProb.Bonanno.LQGMetric.Field.MarkovFinal
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.BilipLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.GaussianSq

/-!
# [18] Lemma A.4: exponential moments of the oscillation of the harmonic part

[18] = Gwynne–Miller–Sheffield, arXiv 1807.07511v3, Lemma A.4 :
"Let `h` be a whole-plane GFF normalized (with any choice of additive constant) and let `𝔥` be the harmonic part of
`h|_𝔻` as defined just after Lemma 2.1. There is a universal constant `a₀ > 0` such that for `δ ∈ (0, 1/4)`,
`E[sup_{z ∈ B_δ(0)} exp((a₀/δ²)(𝔥(z) − 𝔥(0))²)] ≲ 1` with universal implicit constant."

**Formalization.** `h` is any whole-plane GFF (`IsWholePlaneGFF`, any — possibly random — additive constant) and
`h = G + h̊` a Markov decomposition on `𝔻`: `G` measurable, `h̊|_𝔻` a zero-boundary GFF on `𝔻`, `G` independent of
`h̊` (the output of LQGMetric's `markov_normAt`, `MarkovFinal.lmLem2_1`; see `lemmaA4_of_normAt`). The harmonic part
`𝔥` is any harmonic function on `𝔻` representing `G|_𝔻`; the supremum is over all such representatives (they
coincide on `𝔻`).

**Proof.** We follow the paper's mean value + Jensen argument, with a rescaled radial profile so that
`sup_{B_δ}|𝔥 − 𝔥(0)| ≤ C δ^{-2} ∫_{B_{2δ}} |𝔥 − 𝔥(0)|`. For the pointwise exponential moment we do not use the cited
variance formula (`[MS16d, Lemma 6.4]`, which concerns a different field): instead
`𝔥(y) − 𝔥(0) = G(ψ_y − ψ_0)/∫ψ` for a fixed radial bump `ψ` of radius `1/4` (mean value property), the pairing
`G(ψ_y − ψ_0)` is dominated in the convex order by `h(ψ_y − ψ_0) ∼ N(0, logCov(ψ_y − ψ_0))`
(`lintegral_convex_le_add_of_indepFun`), and `logCov(ψ_y − ψ_0) ≤ C|y|²` (`exists_logCov_radDiff_le_sq`).

* `GMSAppA.harm_sub_eq_pairing` — `𝔥(y) − 𝔥(0) = G(ψ_y − ψ_0)/∫ψ`.
* `GMSAppA.exp_le_setAverage_of_harmonic` — the mean value + Jensen step.
* `GMSAppA.lintegral_exp_sq_pairing_le` — the pointwise exponential moment.
* **`GMSAppA.lemmaA4`** — Lemma A.4 for any Markov decomposition on `𝔻`.
* `GMSAppA.lemmaA4_normAt` — Lemma A.4 for the Markov decomposition of LQGMetric (`DFGPS.markov_normAt` with
  `MarkovFinal.lmLem2_1`) of a whole-plane GFF normalized on any circle `∂B_r(w)` disjoint from `𝔻` (e.g. `h_1(0) = 0`,
  or `h_R(w) = 0` with `𝔻 ⊂ B_R(w)` as in Lemma A.5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric InnerProductSpace
open LQGMetric LQGMetric.GM LQGMetric.Blueprint
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSAppA

/-- `∫ radProf (1/4)`, the mass of the fixed bump -/
def massQ : ℝ := ∫ y, radProf (1 / 4) y

lemma massQ_pos : 0 < massQ := integral_radProf_pos quarter_pos

/-- The mean-zero test function `ψ_y − ψ_0` is supported in `𝔻` when `|y| < 3/4`. -/
lemma tsupport_radDiff_subset {y : ℂ} (hy : ‖y‖ < 3 / 4) :
    tsupport ((radDiff quarter_pos.le y 0).1 : ℂ → ℝ) ⊆ (ballO 0 1 : Set ℂ) := by
  have hsub : tsupport ((radDiff quarter_pos.le y 0).1 : ℂ → ℝ) ⊆ closedBall 0 (‖y‖ + 1 / 4) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra hx'
    rw [mem_closedBall, dist_zero_right, not_le] at hx'
    apply hx
    show radProf (1 / 4) (x - y) - radProf (1 / 4) (x - 0) = 0
    have h1 : 1 / 4 ≤ ‖x - y‖ := by have := norm_sub_norm_le x y; linarith
    have h2 : 1 / 4 ≤ ‖x - 0‖ := by rw [sub_zero]; linarith [norm_nonneg y]
    rw [radProf_eq_zero quarter_pos.le h1, radProf_eq_zero quarter_pos.le h2, sub_zero]
  refine hsub.trans fun x hx => ?_
  rw [mem_closedBall, dist_zero_right] at hx
  show x ∈ ball (0 : ℂ) 1
  rw [mem_ball, dist_zero_right]
  linarith

/-- **Point values of the harmonic part as pairings**: if `G = g` on `𝔻` with `g` harmonic, then for `|y| < 3/4`,
`g(y) − g(0) = G(ψ_y − ψ_0) / ∫ψ`. -/
lemma harm_sub_eq_pairing {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1)) {T : DistC}
    (hT : ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) T φ = ∫ x, g x * φ x) {y : ℂ}
    (hy : ‖y‖ < 3 / 4) :
    g y - g 0 = T (radDiff quarter_pos.le y 0).1 / massQ := by
  have hB : ∀ w : ℂ, ‖w‖ < 3 / 4 → closedBall w (1 / 4) ⊆ (ballO 0 1 : Set ℂ) := by
    intro w hw x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    show x ∈ ball (0 : ℂ) 1
    rw [mem_ball, dist_zero_right]
    calc ‖x‖ = ‖(x - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
      _ < 1 := by linarith
  have h1 := pair_radBump_of_harmonic (V := ballO 0 1) hg hT quarter_pos (hB y hy)
  have h2 := pair_radBump_of_harmonic (V := ballO 0 1) hg hT quarter_pos
    (hB 0 (by rw [norm_zero]; norm_num))
  have e : (radDiff quarter_pos.le y 0).1 = radBump (1 / 4) quarter_pos.le y -
      radBump (1 / 4) quarter_pos.le 0 := rfl
  have hm : (∫ y, radProf (1 / 4) y) = massQ := rfl
  rw [e, map_sub, h1, h2, ← sub_mul, hm, mul_div_assoc, div_self massQ_pos.ne', mul_one]

/-- the constant of the scaled mean value bound -/
def mvConst : ℝ := expNegInvGlue 1 / ∫ y, radProf 1 y

lemma mvConst_pos : 0 < mvConst :=
  div_pos (expNegInvGlue.pos_of_pos one_pos) (integral_radProf_pos one_pos)

/-- **The mean value + Jensen step** ([18] ): for `g` harmonic on `𝔻`, `δ ∈ (0, 1/4)`, `z ∈ B_δ(0)`
and `a ≥ 0`, `exp(a/δ² (g(z) − g(0))²) ≤ ⨍_{B̄_{2δ}(0)} exp(16π² c² a/δ² (g(y) − g(0))²)` with `c = mvConst`. -/
theorem exp_le_setAverage_of_harmonic {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball (0 : ℂ) 1))
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ < 1 / 4) {z : ℂ} (hz : z ∈ ball (0 : ℂ) δ) {a : ℝ}
    (ha : 0 ≤ a) :
    Real.exp (a / δ ^ 2 * (g z - g 0) ^ 2) ≤
      ⨍ y in closedBall (0 : ℂ) (2 * δ),
        Real.exp (16 * Real.pi ^ 2 * mvConst ^ 2 * a / δ ^ 2 * (g y - g 0) ^ 2) := by
  set K := closedBall (0 : ℂ) (2 * δ) with hK
  set f : ℂ → ℝ := fun y => g y - g 0 with hf
  have hzn : ‖z‖ < δ := by rwa [mem_ball, dist_zero_right] at hz
  have hKsub : K ⊆ ball (0 : ℂ) 1 := fun x hx => by
    rw [hK, mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]; linarith
  have hfc : ContinuousOn f K := fun y hy =>
    ((hg y (hKsub hy)).1.continuousAt.sub continuousAt_const).continuousWithinAt
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hvol : volume.real K = Real.pi * (2 * δ) ^ 2 := by
    rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by linarith)]
    simp [mul_comm]
  have hvol0 : volume K ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.2 (by linarith)).ne')
      (by simpa using NNReal.pi_pos.ne')
  have hvolt : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hvolr : 0 < volume.real K := by rw [hvol]; positivity
  -- (1) the mean value bound
  have hB : closedBall z δ ⊆ ball (0 : ℂ) 1 := fun x hx => by
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_ball, dist_zero_right]
    have := norm_sub_norm_le x z
    linarith
  have h1 := abs_sub_le_setIntegral_of_harmonic_scaled isOpen_ball hg hδ hB (g 0)
  have hBK : closedBall z δ ⊆ K := fun x hx => by
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [hK, mem_closedBall, dist_zero_right]
    have := norm_sub_norm_le x z
    linarith
  have hint_abs : IntegrableOn (fun y => |f y|) K := (hfc.abs).integrableOn_compact hKc
  have h2 : ∫ y in closedBall z δ, |g y - g 0| ≤ ∫ y in K, |f y| :=
    setIntegral_mono_set hint_abs (ae_of_all _ fun y => abs_nonneg _)
      (HasSubset.Subset.eventuallyLE hBK)
  have h3 : ∫ y in K, |f y| = volume.real K * ⨍ y in K, |f y| := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hvolr.ne', one_mul]
  -- (2) Jensen for the square
  have hsq : (⨍ y in K, |f y|) ^ 2 ≤ ⨍ y in K, (f y) ^ 2 := by
    have hconv : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => x ^ 2) := convexOn_pow 2
    have := hconv.map_set_average_le (continuous_pow 2).continuousOn isClosed_Ici hvol0 hvolt
      (ae_of_all _ fun y => abs_nonneg (f y)) hint_abs
      ((hfc.abs.pow 2).integrableOn_compact hKc)
    simpa only [Function.comp_def, sq_abs] using this
  have hmain : (g z - g 0) ^ 2 ≤ 16 * Real.pi ^ 2 * mvConst ^ 2 * ⨍ y in K, (f y) ^ 2 := by
    have hI1 := integral_radProf_pos (one_pos : (0 : ℝ) < 1)
    have hle : |g z - g 0| ≤ expNegInvGlue 1 / (δ ^ 2 * ∫ y, radProf 1 y) * ∫ y in K, |f y| :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (div_nonneg (expNegInvGlue.nonneg _) (by positivity)))
    have hle' : |g z - g 0| ≤ 4 * Real.pi * mvConst * ⨍ y in K, |f y| := by
      refine hle.trans (le_of_eq ?_)
      rw [h3, hvol, mvConst]
      field_simp
      ring
    have hnn : 0 ≤ ⨍ y in K, |f y| := by
      rw [setAverage_eq, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hvolr.le)
        (setIntegral_nonneg measurableSet_closedBall fun y _ => abs_nonneg _)
    calc (g z - g 0) ^ 2 = |g z - g 0| ^ 2 := (sq_abs _).symm
      _ ≤ (4 * Real.pi * mvConst * ⨍ y in K, |f y|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hle' 2
      _ = 16 * Real.pi ^ 2 * mvConst ^ 2 * (⨍ y in K, |f y|) ^ 2 := by ring
      _ ≤ 16 * Real.pi ^ 2 * mvConst ^ 2 * ⨍ y in K, (f y) ^ 2 := by
          gcongr
  -- (3) Jensen for the exponential
  set κ := 16 * Real.pi ^ 2 * mvConst ^ 2 * a / δ ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hint_sq : IntegrableOn (fun y => κ * (f y) ^ 2) K :=
    ((continuousOn_const.mul (hfc.pow 2))).integrableOn_compact hKc
  have hJ := convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn isClosed_univ hvol0
    hvolt (ae_of_all _ fun _ => mem_univ _) hint_sq
    ((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hfc.pow 2))).integrableOn_compact
      hKc)
  have havg : ⨍ y in K, κ * (f y) ^ 2 = κ * ⨍ y in K, (f y) ^ 2 := by
    rw [setAverage_eq, setAverage_eq, integral_const_mul, smul_eq_mul, smul_eq_mul]; ring
  calc Real.exp (a / δ ^ 2 * (g z - g 0) ^ 2)
      ≤ Real.exp (κ * ⨍ y in K, (f y) ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        calc a / δ ^ 2 * (g z - g 0) ^ 2 ≤ a / δ ^ 2 *
              (16 * Real.pi ^ 2 * mvConst ^ 2 * ⨍ y in K, (f y) ^ 2) :=
              mul_le_mul_of_nonneg_left hmain (by positivity)
          _ = κ * ⨍ y in K, (f y) ^ 2 := by rw [hκ]; ring
    _ = Real.exp (⨍ y in K, κ * (f y) ^ 2) := by rw [havg]
    _ ≤ ⨍ y in K, Real.exp (κ * (f y) ^ 2) := hJ

/-- `x ↦ exp(μx²)` is convex for `μ ≥ 0`. -/
lemma convexOn_exp_mul_sq {μ : ℝ} (hμ : 0 ≤ μ) : ConvexOn ℝ univ fun x : ℝ => Real.exp (μ * x ^ 2) := by
  have hq : ConvexOn ℝ univ fun x : ℝ => μ * x ^ 2 := by
    have := (Even.convexOn_pow (𝕜 := ℝ) even_two).smul hμ
    simpa only [smul_eq_mul] using this
  have himg : Convex ℝ ((fun x : ℝ => μ * x ^ 2) '' univ) :=
    ((isPreconnected_univ.image _ (by fun_prop : Continuous fun x : ℝ => μ * x ^ 2).continuousOn)
      ).ordConnected.convex
  exact (convexOn_exp.subset (subset_univ _) himg).comp hq (Real.exp_monotone.monotoneOn _)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- **Pointwise exponential moment of a harmonic-part pairing.** For a Markov decomposition `h = G + h̊` on `𝔻` and
`|y| < 3/4`, if `4μ · logCov(ψ_y − ψ_0) ≤ 1` then `E[exp(μ G(ψ_y − ψ_0)²)] ≤ √2`. -/
theorem lintegral_exp_sq_pairing_le {h G hz : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hG : Measurable G) (hdec : ∀ᵐ ω ∂P, h ω = G ω + hz ω) (hind : IndepFun G hz P)
    (hzb : IsZeroBoundaryGFF (ballO 0 1) (fun ω => restrictTo (ballO 0 1) (hz ω)) P) {y : ℂ}
    (hy : ‖y‖ < 3 / 4) {μ : ℝ} (hμ : 0 ≤ μ)
    (hvar : 4 * μ * logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1 ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * (G ω (radDiff quarter_pos.le y 0).1) ^ 2)) ∂P ≤
      ENNReal.ofReal (√2) := by
  set φ := radDiff quarter_pos.le y 0
  set X : Ω → ℝ := fun ω => G ω φ.1
  set Z : Ω → ℝ := fun ω => hz ω φ.1
  set Y : Ω → ℝ := fun ω => h ω φ.1
  have hXm : Measurable X := (measurable_distOn_apply φ.1).comp hG
  let φV : TestOn (ballO 0 1) := ⟨φ.1, φ.1.contDiff, φ.1.hasCompactSupport, tsupport_radDiff_subset hy⟩
  have hZeq : Z = fun ω => restrictTo (ballO 0 1) (hz ω) φV := by
    funext ω
    show hz ω φ.1 = hz ω (TestFunction.monoCLM ℝ φV)
    congr 1
    ext x
    simp [TestFunction.monoCLM_apply, φV]
  have hZm : Measurable Z := by rw [hZeq]; exact hzb.process.measurable φV
  have hZi : Integrable Z P := by
    rw [hZeq]; exact (hzb.process.gaussian.hasGaussianLaw_eval φV).memLp_two.integrable one_le_two
  have hZ0 : ∫ ω, Z ω ∂P = 0 := by rw [hZeq]; exact hzb.process.centered φV
  have hXZ : IndepFun X Z P := hind.comp (measurable_distOn_apply φ.1) (measurable_distOn_apply φ.1)
  have hdom := lintegral_convex_le_add_of_indepFun hXm hZm hXZ hZi hZ0 (convexOn_exp_mul_sq hμ)
    (by fun_prop) (fun x => (Real.exp_pos _).le)
  -- the law of `Y = X + Z`
  have hYeq : (fun ω => ENNReal.ofReal (Real.exp (μ * (X ω + Z ω) ^ 2))) =ᵐ[P]
      fun ω => ENNReal.ofReal (Real.exp (μ * (Y ω) ^ 2)) := by
    filter_upwards [hdec] with ω hω
    show ENNReal.ofReal (Real.exp (μ * (G ω φ.1 + hz ω φ.1) ^ 2)) =
      ENNReal.ofReal (Real.exp (μ * (h ω φ.1) ^ 2))
    rw [hω, ContinuousLinearMap.add_apply]
  have hYG : HasGaussianLaw Y P := hh.gaussian.hasGaussianLaw_eval φ
  have hYm : Measurable Y := (measurable_distOn_apply φ.1).comp hh.measurable
  have hmean : P[Y] = 0 := hh.centered φ
  have hvarY : Var[Y; P] = logCov φ.1 φ.1 := by
    rw [← covariance_self hYm.aemeasurable]; exact hh.covariance_eq φ φ
  have hmap : P.map Y = gaussianReal 0 (logCov φ.1 φ.1).toNNReal := by
    rw [hYG.map_eq_gaussianReal, hmean, hvarY]
  set v := (logCov φ.1 φ.1).toNNReal
  have hv : 4 * μ * (v : ℝ) ≤ 1 := by
    rw [Real.coe_toNNReal']
    rcases le_total (logCov φ.1 φ.1) 0 with hneg | hpos
    · rw [max_eq_right hneg]; simp
    · rw [max_eq_left hpos]; exact hvar
  have hfm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (μ * x ^ 2)) := by fun_prop
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * (X ω) ^ 2)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * (X ω + Z ω) ^ 2)) ∂P := hdom
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (μ * (Y ω) ^ 2)) ∂P := lintegral_congr_ae hYeq
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (μ * x ^ 2)) ∂(P.map Y) := (lintegral_map hfm hYm).symm
    _ = ENNReal.ofReal (∫ x, Real.exp (μ * x ^ 2) ∂(gaussianReal 0 v)) := by
        rw [hmap, ofReal_integral_eq_lintegral_ofReal
          (integrable_exp_mul_sq_gaussianReal (by nlinarith [v.2]))
          (ae_of_all _ fun x => (Real.exp_pos _).le)]
    _ ≤ ENNReal.ofReal (√2) :=
        ENNReal.ofReal_le_ofReal (integral_exp_mul_sq_gaussianReal_le (by linarith))

/-- the set of harmonic representatives of `G|_𝔻` -/
def HarmRep (T : DistC) (g : ℂ → ℝ) : Prop :=
  HarmonicOnNhd g (ball (0 : ℂ) 1) ∧
    ∀ φ : TestOn (ballO 0 1), restrictTo (ballO 0 1) T φ = ∫ x, g x * φ x

/-- **[18] Lemma A.4.** There are universal constants `a₀ > 0`, `C` such that for every whole-plane GFF `h` (any
additive constant), every Markov decomposition `h = G + h̊` on `𝔻` (`G` measurable and independent of `h̊`, `h̊|_𝔻` a
zero-boundary GFF on `𝔻`) and every `δ ∈ (0, 1/4)`,
`E[sup_{z ∈ B_δ(0)} exp((a₀/δ²)(𝔥(z) − 𝔥(0))²)] ≤ C`, where `𝔥` is (any) harmonic representative of `G|_𝔻`. -/
theorem lemmaA4 : ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h G hz : Ω → DistC), IsWholePlaneGFF h P → Measurable G →
      (∀ᵐ ω ∂P, h ω = G ω + hz ω) → IndepFun G hz P →
      IsZeroBoundaryGFF (ballO 0 1) (fun ω => restrictTo (ballO 0 1) (hz ω)) P →
      ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
        ∫⁻ ω, ⨆ (g : ℂ → ℝ) (_ : HarmRep (G ω) g), ⨆ z ∈ ball (0 : ℂ) δ,
          ENNReal.ofReal (Real.exp (a₀ / δ ^ 2 * (g z - g 0) ^ 2)) ∂P ≤ ENNReal.ofReal C := by
  obtain ⟨CL, hCL0, hCL⟩ := exists_logCov_radDiff_le_sq
  set κ := massQ ^ 2 / (16 * (CL + 1)) with hκ
  have hκ0 : 0 < κ := div_pos (pow_pos massQ_pos 2) (by positivity)
  set a₀ := κ / (16 * Real.pi ^ 2 * mvConst ^ 2) with ha₀
  have ha₀0 : 0 < a₀ := div_pos hκ0 (by have := mvConst_pos; positivity)
  refine ⟨a₀, √2, ha₀0, by positivity, ?_⟩
  intro Ω _ P _ h G hz hh hG hdec hind hzb δ hδ hδ4
  set K := closedBall (0 : ℂ) (2 * δ) with hK
  have hKn : ∀ y ∈ K, ‖y‖ ≤ 2 * δ := fun y hy => by rwa [hK, mem_closedBall, dist_zero_right] at hy
  set X : Ω → ℂ → ℝ := fun ω y => G ω (radDiff quarter_pos.le y 0).1 with hX
  set μ := κ / (δ ^ 2 * massQ ^ 2) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg hκ0.le (by positivity)
  set F : Ω → ℂ → ℝ := fun ω y => Real.exp (μ * (X ω y) ^ 2) with hF
  -- measurability and continuity of the pairing field
  have hXeq : ∀ ω y, X ω y = G ω (radBump (1 / 4) quarter_pos.le y) -
      G ω (radBump (1 / 4) quarter_pos.le 0) := fun ω y => by
    show G ω (radBump (1 / 4) quarter_pos.le y - radBump (1 / 4) quarter_pos.le 0) = _
    rw [map_sub]
  have hXm : Measurable (Function.uncurry X) := by
    have h1 : Measurable fun p : Ω × ℂ => G p.1 (radBump (1 / 4) quarter_pos.le p.2) :=
      (measurable_apply_radBump (1 / 4) quarter_pos.le).comp
        ((hG.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun p : Ω × ℂ => G p.1 (radBump (1 / 4) quarter_pos.le 0) :=
      ((measurable_distOn_apply _).comp hG).comp measurable_fst
    have e : Function.uncurry X = fun p : Ω × ℂ => G p.1 (radBump (1 / 4) quarter_pos.le p.2) -
        G p.1 (radBump (1 / 4) quarter_pos.le 0) := by
      funext p; exact hXeq p.1 p.2
    rw [e]; exact h1.sub h2
  have hXc : ∀ ω, Continuous (X ω) := fun ω => by
    have e : X ω = fun y => G ω (radBump (1 / 4) quarter_pos.le y) -
        G ω (radBump (1 / 4) quarter_pos.le 0) := funext (hXeq ω)
    rw [e]
    exact ((map_continuous (G ω)).comp (continuous_radBump (1 / 4) quarter_pos.le)).sub
      continuous_const
  have hFm : Measurable (Function.uncurry fun ω y => ENNReal.ofReal (F ω y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (hXm.pow_const 2)))
  have hFc : ∀ ω, Continuous (F ω) := fun ω =>
    Real.continuous_exp.comp (continuous_const.mul ((hXc ω).pow 2))
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hvolt : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hvol0 : volume K ≠ 0 := by
    rw [Complex.volume_closedBall]
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.2 (by linarith)).ne')
      (by simpa using NNReal.pi_pos.ne')
  have hvolr : 0 < volume.real K := ENNReal.toReal_pos hvol0 hvolt
  -- (1) the supremum is bounded by the average `Φ(ω)` of `F(ω, ·)` over `K`
  have hsup : ∀ ω, (⨆ (g : ℂ → ℝ) (_ : HarmRep (G ω) g), ⨆ z ∈ ball (0 : ℂ) δ,
      ENNReal.ofReal (Real.exp (a₀ / δ ^ 2 * (g z - g 0) ^ 2))) ≤
      ENNReal.ofReal (⨍ y in K, F ω y) := by
    intro ω
    refine iSup₂_le fun g hg => iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_
    have h1 := exp_le_setAverage_of_harmonic hg.1 hδ hδ4 hz ha₀0.le
    refine h1.trans (le_of_eq ?_)
    rw [setAverage_eq, setAverage_eq]
    congr 1
    refine setIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    have hy' : ‖y‖ < 3 / 4 := by have := hKn y hy; linarith
    simp only [F, X]
    rw [harm_sub_eq_pairing hg.1 hg.2 hy']
    congr 1
    rw [hμ, ha₀]
    have := mvConst_pos
    have := massQ_pos
    field_simp
  -- (2) Tonelli and the pointwise moment
  have hpt : ∀ y ∈ K, ∫⁻ ω, ENNReal.ofReal (F ω y) ∂P ≤ ENNReal.ofReal (√2) := by
    intro y hy
    have hyn := hKn y hy
    have hy34 : ‖y‖ < 3 / 4 := by linarith
    refine lintegral_exp_sq_pairing_le hh hG hdec hind hzb hy34 hμ0 ?_
    have hL := hCL y (by linarith)
    calc 4 * μ * logCov (radDiff quarter_pos.le y 0).1 (radDiff quarter_pos.le y 0).1
        ≤ 4 * μ * (CL * ‖y‖ ^ 2) := mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ 4 * μ * (CL * (2 * δ) ^ 2) := by gcongr
      _ = 16 * κ * CL / massQ ^ 2 := by rw [hμ]; field_simp; ring
      _ ≤ 1 := by
          rw [hκ, div_le_one (pow_pos massQ_pos 2)]
          field_simp
          nlinarith [pow_pos massQ_pos 2]
  calc ∫⁻ ω, ⨆ (g : ℂ → ℝ) (_ : HarmRep (G ω) g), ⨆ z ∈ ball (0 : ℂ) δ,
        ENNReal.ofReal (Real.exp (a₀ / δ ^ 2 * (g z - g 0) ^ 2)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (⨍ y in K, F ω y) ∂P := lintegral_mono hsup
    _ = ∫⁻ ω, ENNReal.ofReal (volume.real K)⁻¹ * (∫⁻ y in K, ENNReal.ofReal (F ω y)) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [setAverage_eq, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.2 hvolr.le),
          ofReal_integral_eq_lintegral_ofReal ((hFc ω).continuousOn.integrableOn_compact hKc)
            (ae_of_all _ fun y => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal (volume.real K)⁻¹ * ∫⁻ y in K, ∫⁻ ω, ENNReal.ofReal (F ω y) ∂P := by
        have hmi : Measurable fun ω => ∫⁻ y in K, ENNReal.ofReal (F ω y) :=
          hFm.lintegral_prod_right' (ν := volume.restrict K)
        rw [lintegral_const_mul _ hmi]
        congr 1
        exact lintegral_lintegral_swap (μ := P) (ν := volume.restrict K)
          (f := fun ω y => ENNReal.ofReal (F ω y)) hFm.aemeasurable
    _ ≤ ENNReal.ofReal (volume.real K)⁻¹ * ∫⁻ _ in K, ENNReal.ofReal (√2) := by
        gcongr ENNReal.ofReal (volume.real K)⁻¹ * ?_
        exact setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal (√2) := by
        rw [setLIntegral_const, ← mul_assoc, mul_comm _ (ENNReal.ofReal (√2)), mul_assoc]
        rw [← ENNReal.ofReal_toReal hvolt, ← ENNReal.ofReal_mul (inv_nonneg.2 hvolr.le)]
        rw [show (volume.real K)⁻¹ * (volume K).toReal = 1 from inv_mul_cancel₀ hvolr.ne']
        simp

/-- **[18] Lemma A.4 for LQGMetric's Markov decomposition.** For a whole-plane GFF `h` normalized so that its circle
average over a circle `∂B_r(w)` disjoint from `𝔻` vanishes, the decomposition `h = 𝔥 + h̊` on `𝔻` given by
`DFGPS.markov_normAt` satisfies the bound of Lemma A.4 with universal constants. -/
theorem lemmaA4_normAt : ∃ a₀ C : ℝ, 0 < a₀ ∧ 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (r : ℝ) (w : ℂ), 0 < r → (∀ᵐ ω ∂P, circleAvg (h ω) r w = 0) →
      Disjoint (ball (0 : ℂ) 1) (sphere w r) →
      ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧ (∀ᵐ ω ∂P, ∃ g, HarmRep (hh ω) g) ∧
        IndepFun hh hz P ∧
        IsZeroBoundaryGFF (ballO 0 1) (fun ω => restrictTo (ballO 0 1) (hz ω)) P ∧
        ∀ δ : ℝ, 0 < δ → δ < 1 / 4 →
          ∫⁻ ω, ⨆ (g : ℂ → ℝ) (_ : HarmRep (hh ω) g), ⨆ z ∈ ball (0 : ℂ) δ,
            ENNReal.ofReal (Real.exp (a₀ / δ ^ 2 * (g z - g 0) ^ 2)) ∂P ≤ ENNReal.ofReal C := by
  obtain ⟨a₀, C, ha₀, hC, hA4⟩ := lemmaA4
  refine ⟨a₀, C, ha₀, hC, ?_⟩
  intro Ω _ P _ h hh r w hr hn hV
  obtain ⟨hh', hz, hsum, hharm, ⟨G', hG'm, hG'⟩, hind, hzb, -, -⟩ :=
    DFGPS.markov_normAt MarkovFinal.lmLem2_1 P h hh hr w hn (ballO 0 1) hV
  refine ⟨hh', hz, hsum, hharm, hind, hzb, fun δ hδ hδ4 => ?_⟩
  have hG'meas : Measurable G' := hG'm.mono (GM.Bilip.fieldSigmaClosed_le hh.measurable _) le_rfl
  have hdec : ∀ᵐ ω ∂P, h ω = G' ω + hz ω := by
    filter_upwards [hG'] with ω hω
    rw [hsum ω, hω]
  have hind' : IndepFun G' hz P := hind.congr hG' (ae_of_all _ fun _ => rfl)
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hA4 P h G' hz hh hG'meas hdec hind' hzb δ hδ hδ4)
  filter_upwards [hG'] with ω hω
  rw [hω]

end MatedCRTHarmonic.GMSAppA
