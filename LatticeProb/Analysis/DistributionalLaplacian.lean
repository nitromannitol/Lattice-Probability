import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact

import LatticeProb.Analysis.SuperharmonicMinimumPrinciple

/-!
# The distributional Laplacian of a function on the plane

For an open set `U ⊆ ℂ`, `IsTestFunction U φ` says that `φ : ℂ → ℝ` is a smooth function with compact support
contained in `U`. `DistribLaplacianLE f μ U` says that `Δf ≤ μ` on `U` in the sense of distributions, that is,
`f` is locally integrable on `U` and `∫ f Δφ ≤ ∫ φ dμ` for every nonnegative test function `φ` on `U`
(cf. Armitage and Gardiner, *Classical Potential Theory*, Springer 2001, Chapter 3, on superharmonic functions).
For `μ = 0` this says that `f` is distributionally superharmonic on `U`.
-/

open MeasureTheory Laplacian
open scoped ContDiff

open MeasureTheory Set Metric Filter Topology Complex Laplacian
open scoped ContDiff Real

namespace LatticeProb

/-- `φ : ℂ → ℝ` is a *test function on `U`*: it is smooth, has compact support, and its support is contained
in `U`. -/
def IsTestFunction (U : Set ℂ) (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- `Δf ≤ μ` *on `U`* in the sense of distributions: `f` is locally integrable on `U` and
`∫ f Δφ ≤ ∫ φ dμ` for every nonnegative test function `φ` on `U` that is `μ`-integrable.
For `μ = 0` this says that `f` is distributionally superharmonic on `U`
(cf. Armitage and Gardiner, *Classical Potential Theory*, Chapter 3). -/
def DistribLaplacianLE (f : ℂ → ℝ) (μ : Measure ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn f U ∧
    ∀ φ : ℂ → ℝ, IsTestFunction U φ → 0 ≤ φ → Integrable φ μ →
      ∫ x, f x * Δ φ x ≤ ∫ x, φ x ∂μ

noncomputable abbrev innerCLM : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
/-- The derivative of `w ↦ ‖w - c‖²` at `z`, as a real linear form. -/
noncomputable abbrev normSqGradCLM (z : ℂ) : ℂ →L[ℝ] ℝ := (2 : ℕ) • innerCLM z
/-- The derivative of `z ↦ normSqGradCLM z`. -/
noncomputable abbrev normSqHessCLM : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (2 : ℕ) • innerCLM

theorem hasFDerivAt_normSq_sub' (c z : ℂ) :
    HasFDerivAt (fun w : ℂ => ‖w - c‖ ^ 2) (normSqGradCLM (z - c)) z := by
  have h := (hasStrictFDerivAt_norm_sq (z - c)).hasFDerivAt
  have h2 := h.comp z ((hasFDerivAt_id z).sub_const c)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem hasFDerivAt_affine_dq (c z : ℂ) :
    HasFDerivAt (fun w : ℂ => normSqGradCLM (w - c)) normSqHessCLM z := by
  have h := (innerCLM.hasFDerivAt).comp z ((hasFDerivAt_id z).sub_const c)
  have h2 := h.const_smul (2 : ℕ)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem laplacian_comp_normSq_sub' (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (c y : ℂ) :
    Δ (fun z : ℂ => K (‖z - c‖ ^ 2)) y = 4 * deriv (fun t : ℝ => t * deriv K t) (‖y - c‖ ^ 2) := by
  have hK' : ContDiff ℝ ∞ (deriv K) := (contDiff_infty_iff_deriv.mp hK).2
  have hKd : Differentiable ℝ K := hK.differentiable (by simp)
  have hK'd : Differentiable ℝ (deriv K) := hK'.differentiable (by simp)
  have hf : ∀ w : ℂ, HasFDerivAt (fun z : ℂ => K (‖z - c‖ ^ 2))
      (deriv K (‖w - c‖ ^ 2) • normSqGradCLM (w - c)) w := by
    intro w
    have h1 : HasDerivAt K (deriv K (‖w - c‖ ^ 2)) (‖w - c‖ ^ 2) := (hKd _).hasDerivAt
    exact h1.comp_hasFDerivAt w (hasFDerivAt_normSq_sub' c w)
  have hfd : fderiv ℝ (fun z : ℂ => K (‖z - c‖ ^ 2)) =
      fun w => deriv K (‖w - c‖ ^ 2) • normSqGradCLM (w - c) := funext fun w => (hf w).fderiv
  have hc : HasFDerivAt (fun w : ℂ => deriv K (‖w - c‖ ^ 2))
      (deriv (deriv K) (‖y - c‖ ^ 2) • normSqGradCLM (y - c)) y := by
    have h1 : HasDerivAt (deriv K) (deriv (deriv K) (‖y - c‖ ^ 2)) (‖y - c‖ ^ 2) := (hK'd _).hasDerivAt
    exact h1.comp_hasFDerivAt y (hasFDerivAt_normSq_sub' c y)
  have hg : HasFDerivAt (fun w : ℂ => deriv K (‖w - c‖ ^ 2) • normSqGradCLM (w - c))
      (deriv K (‖y - c‖ ^ 2) • normSqHessCLM +
        (deriv (deriv K) (‖y - c‖ ^ 2) • normSqGradCLM (y - c)).smulRight (normSqGradCLM (y - c))) y :=
    hc.smul (hasFDerivAt_affine_dq c y)
  have hsec : fderiv ℝ (fderiv ℝ (fun z : ℂ => K (‖z - c‖ ^ 2))) y =
      deriv K (‖y - c‖ ^ 2) • normSqHessCLM +
        (deriv (deriv K) (‖y - c‖ ^ 2) • normSqGradCLM (y - c)).smulRight (normSqGradCLM (y - c)) := by
    rw [hfd]
    exact hg.fderiv
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply, hsec]
  have hder : deriv (fun t : ℝ => t * deriv K t) (‖y - c‖ ^ 2) =
      deriv K (‖y - c‖ ^ 2) + ‖y - c‖ ^ 2 * deriv (deriv K) (‖y - c‖ ^ 2) := by
    have h1 : HasDerivAt (fun t : ℝ => t) 1 (‖y - c‖ ^ 2) := hasDerivAt_id _
    have h2 : HasDerivAt (deriv K) (deriv (deriv K) (‖y - c‖ ^ 2)) (‖y - c‖ ^ 2) :=
      (hK'd _).hasDerivAt
    have h3 : HasDerivAt (fun t : ℝ => t * deriv K t)
        (1 * deriv K (‖y - c‖ ^ 2) + ‖y - c‖ ^ 2 * deriv (deriv K) (‖y - c‖ ^ 2)) (‖y - c‖ ^ 2) :=
      HasDerivAt.mul h1 h2
    rw [h3.deriv]
    ring
  have hnorm : ‖y - c‖ ^ 2 = (y - c).re ^ 2 + (y - c).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hder, hnorm]
  have hin : ∀ v w : ℂ, innerCLM v w = (inner ℝ v w : ℝ) := fun v w => rfl
  simp [normSqGradCLM, normSqHessCLM, hin, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  ring_nf

/-- Radial integration on the plane: an integral of `f(y) G(|y - c|²)` in polar coordinates centred at `c`. -/
theorem integral_mul_radial_sq_eq_polar (f : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ContinuousOn f (closedBall c R)) (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ q, R ^ 2 ≤ q → G q = 0) :
    ∫ y, f y * G (‖y - c‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ q in Ioi (0 : ℝ),
        (∫ θ in (-π)..π, f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))) * G q := by
  -- Step 1: translate by `c`
  have h1 : ∫ y, f y * G (‖y - c‖ ^ 2) = ∫ z, f (z + c) * G (‖z‖ ^ 2) := by
    rw [← integral_add_right_eq_self (fun y => f y * G (‖y - c‖ ^ 2)) c]
    simp
  -- Step 2: polar coordinates on `ℂ`
  have h2 : ∫ z, f (z + c) * G (‖z‖ ^ 2) =
      ∫ p in Complex.polarCoord.target, p.1 • (f (Complex.polarCoord.symm p + c) *
        G (‖Complex.polarCoord.symm p‖ ^ 2)) :=
    (Complex.integral_comp_polarCoord_symm (fun z => f (z + c) * G (‖z‖ ^ 2))).symm
  rw [h1, h2, Complex.polarCoord_target]
  have hnorm : ∀ p : ℝ × ℝ, ‖Complex.polarCoord.symm p‖ ^ 2 = p.1 ^ 2 := fun p => by
    rw [Complex.norm_polarCoord_symm, sq_abs]
  simp only [hnorm, smul_eq_mul]
  -- the target is `Ioi 0 ×ˢ Ioo (-π) π`; the integrand vanishes off `K := Icc 0 R ×ˢ Icc (-π) π`
  set K : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc (-π) π with hK
  set Ψ : ℝ × ℝ → ℝ := fun p => p.1 * (f (Complex.polarCoord.symm p + c) * G (p.1 ^ 2)) with hΨ
  have hsymm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hKc : ContinuousOn Ψ K := by
    refine ContinuousOn.mul continuousOn_fst (ContinuousOn.mul ?_ (hG.comp (continuous_fst.pow 2)).continuousOn)
    have hmaps : MapsTo (fun p : ℝ × ℝ => Complex.polarCoord.symm p + c) K (closedBall c R) := by
      intro p hp
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, Complex.norm_polarCoord_symm]
      rw [hK, mem_prod] at hp
      exact abs_le.mpr ⟨by linarith [hp.1.1], hp.1.2⟩
    exact (hf.comp ((hsymm.add continuous_const).continuousOn) hmaps)
  -- integrability on the target: `Ψ` vanishes off `K`
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hIntK : IntegrableOn Ψ K := hKc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hIntT : IntegrableOn Ψ (Ioi 0 ×ˢ Ioo (-π) π) := by
    have hind : Integrable (K.indicator Ψ) := hIntK.integrable_indicator hKmeas
    refine (hind.integrableOn (s := Ioi 0 ×ˢ Ioo (-π) π)).congr_fun ?_
      (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    by_cases hpK : p ∈ K
    · rw [indicator_of_mem hpK]
    · rw [indicator_of_notMem hpK]
      have hp1 : R < p.1 := by
        by_contra hle
        have hle' : p.1 ≤ R := not_lt.mp hle
        apply hpK
        rw [hK, mem_prod]
        exact ⟨⟨hp.1.le, hle'⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
      have hp0 : (0 : ℝ) < p.1 := hp.1
      have hsq : R ^ 2 ≤ p.1 ^ 2 := by nlinarith
      simp only [hΨ]
      rw [hG0 _ hsq]
      simp
  -- polar form of the parametrisation
  have hpolar : ∀ (s θ : ℝ), Complex.polarCoord.symm (s, θ) = (s : ℂ) * Complex.exp (θ * Complex.I) := by
    intro s θ
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hinner : ∀ s : ℝ, 0 < s → ∫ θ in Ioo (-π) π, Ψ (s, θ) =
      s * G (s ^ 2) * ∫ θ in (-π)..π, f (c + (Real.sqrt (s ^ 2) : ℂ) * Complex.exp (θ * Complex.I)) := by
    intro s hs
    have e1 : ∀ θ : ℝ, Ψ (s, θ) = s * G (s ^ 2) * f (c + (s : ℂ) * Complex.exp (θ * Complex.I)) := by
      intro θ
      simp only [hΨ]
      rw [hpolar]
      ring_nf
    simp_rw [e1]
    rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo, Real.sqrt_sq hs.le]
  -- Fubini on the product target
  have hIntT' : IntegrableOn Ψ (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hIntT
  rw [Measure.volume_eq_prod, setIntegral_prod Ψ hIntT']
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hinner s hs)]
  -- the substitution `q = s²`
  have subst : ∀ h : ℝ → ℝ, ∫ s in Ioi (0 : ℝ), s * h (s ^ 2) = (1 / 2 : ℝ) * ∫ q in Ioi (0 : ℝ), h q := by
    intro h
    have himg : (fun s : ℝ => s ^ 2) '' Ioi 0 = Ioi 0 := by
      ext q
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨s, hs, rfl⟩
        positivity
      · intro hq
        exact ⟨Real.sqrt q, Real.sqrt_pos.mpr hq, Real.sq_sqrt hq.le⟩
    have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ => s ^ 2) (2 * x) (Ioi 0) x := by
      intro x _
      simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
    have hinj : InjOn (fun s : ℝ => s ^ 2) (Ioi 0) := by
      intro a ha b hb hab
      simp only [mem_Ioi] at ha hb hab
      nlinarith
    have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj h
    rw [himg] at key
    have h2 : ∫ x in Ioi (0 : ℝ), |2 * x| • h (x ^ 2) = 2 * ∫ x in Ioi (0 : ℝ), x * h (x ^ 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [mem_Ioi] at hx
      simp only [smul_eq_mul]
      rw [abs_of_pos (by linarith)]
      ring
    rw [h2] at key
    linarith
  rw [← subst (fun q => (∫ θ in (-π)..π, f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))) * G q)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only
  ring

/-- A smooth step rising from `0` on `(-∞, x - δ]` to `1` on `[x + δ, ∞)`. -/
noncomputable def smoothStep (x δ : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((t - (x - δ)) / (2 * δ))

theorem smoothStep_contDiff (x δ : ℝ) : ContDiff ℝ ∞ (smoothStep x δ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem smoothStep_monotone (x : ℝ) {δ : ℝ} (hδ : 0 < δ) : Monotone (smoothStep x δ) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

theorem smoothStep_eq_zero_of_le (x : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ≤ x - δ) :
    smoothStep x δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
  linarith

theorem smoothStep_eq_one_of_le (x : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : x + δ ≤ t) :
    smoothStep x δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The derivative of the smooth step: a nonnegative smooth bump of total mass one on `[x - δ, x + δ]`. -/
noncomputable def stepBump (x δ : ℝ) : ℝ → ℝ := deriv (smoothStep x δ)

theorem stepBump_contDiff (x δ : ℝ) : ContDiff ℝ ∞ (stepBump x δ) :=
  (contDiff_infty_iff_deriv.mp (smoothStep_contDiff x δ)).2

theorem stepBump_nonneg (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ stepBump x δ t :=
  (smoothStep_monotone x hδ).deriv_nonneg

theorem stepBump_eq_zero_of_lt (x : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t < x - δ) :
    stepBump x δ t = 0 := by
  unfold stepBump
  have hev : smoothStep x δ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact smoothStep_eq_zero_of_le x hδ (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

theorem stepBump_eq_zero_of_gt (x : ℝ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : x + δ < t) :
    stepBump x δ t = 0 := by
  unfold stepBump
  have hev : smoothStep x δ =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact smoothStep_eq_one_of_le x hδ (le_of_lt hs)
  rw [hev.deriv_eq]
  simp

theorem integral_stepBump (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in (x - δ)..(x + δ), stepBump x δ t = 1 := by
  have hderiv : ∀ t ∈ uIcc (x - δ) (x + δ), HasDerivAt (smoothStep x δ) (stepBump x δ t) t := by
    intro t _
    exact ((smoothStep_contDiff x δ).differentiable (by simp) t).hasDerivAt
  have hint : IntervalIntegrable (stepBump x δ) volume (x - δ) (x + δ) :=
    (stepBump_contDiff x δ).continuous.intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [smoothStep_eq_one_of_le x hδ (t := x + δ) (by linarith),
    smoothStep_eq_zero_of_le x hδ (t := x - δ) (by linarith)]
  norm_num

/-- Approximate identity: the normalized smooth bumps centred at a point `x` of an open set on which `B` is
continuous average `B` to `B x`. -/
theorem tendsto_integral_mul_stepBump {B : ℝ → ℝ} {U0 : Set ℝ} (hU0 : IsOpen U0) (hBc : ContinuousOn B U0)
    {x : ℝ} (hx : x ∈ U0) :
    Tendsto (fun δ : ℝ => ∫ t in (x - δ)..(x + δ), B t * stepBump x δ t) (𝓝[>] 0) (𝓝 (B x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : ContinuousAt B x := hBc.continuousAt (hU0.mem_nhds hx)
  obtain ⟨η, hη, hBη⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (by linarith)
  obtain ⟨η0, hη0, hball⟩ := Metric.isOpen_iff.mp hU0 x hx
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη hη0)] with δ hδ
  have hδpos : 0 < δ := hδ.1
  have hδη : δ < η := lt_of_lt_of_le hδ.2 (min_le_left _ _)
  have hδη0 : δ < η0 := lt_of_lt_of_le hδ.2 (min_le_right _ _)
  have hle : x - δ ≤ x + δ := by linarith
  have hsub : uIcc (x - δ) (x + δ) ⊆ U0 := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hcontI : ContinuousOn (fun t => B t * stepBump x δ t) (uIcc (x - δ) (x + δ)) :=
    (hBc.mono hsub).mul (stepBump_contDiff x δ).continuous.continuousOn
  have hint_B : IntervalIntegrable (fun t => B t * stepBump x δ t) volume (x - δ) (x + δ) :=
    hcontI.intervalIntegrable
  have hint_g : IntervalIntegrable (stepBump x δ) volume (x - δ) (x + δ) :=
    (stepBump_contDiff x δ).continuous.intervalIntegrable _ _
  have hconst : ∫ t in (x - δ)..(x + δ), B x * stepBump x δ t = B x := by
    rw [intervalIntegral.integral_const_mul, integral_stepBump x hδpos, mul_one]
  have h2 : IntervalIntegrable (fun t => B x * stepBump x δ t) volume (x - δ) (x + δ) :=
    hint_g.const_mul (B x)
  have hdiff : ∫ t in (x - δ)..(x + δ), (B t - B x) * stepBump x δ t =
      (∫ t in (x - δ)..(x + δ), B t * stepBump x δ t) - ∫ t in (x - δ)..(x + δ), B x * stepBump x δ t := by
    simp only [sub_mul]
    exact intervalIntegral.integral_sub hint_B h2
  have hpt : ∀ t ∈ uIoc (x - δ) (x + δ),
      ‖(B t - B x) * stepBump x δ t‖ ≤ ε / 2 * stepBump x δ t := by
    intro t ht
    rw [uIoc_of_le hle] at ht
    have hdist : dist t x < η := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have hB' : |B t - B x| < ε / 2 := by
      have := hBη hdist
      rwa [Real.dist_eq] at this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stepBump_nonneg x hδpos t)]
    exact mul_le_mul_of_nonneg_right hB'.le (stepBump_nonneg x hδpos t)
  have hpt' : ∀ t ∈ Ioc (x - δ) (x + δ), ‖(B t - B x) * stepBump x δ t‖ ≤ ε / 2 * stepBump x δ t :=
    fun t ht => hpt t (by rw [uIoc_of_le hle]; exact ht)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hle (ae_of_all _ hpt')
    (hint_g.const_mul (ε / 2))
  have hval : ∫ t in (x - δ)..(x + δ), ε / 2 * stepBump x δ t = ε / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_stepBump x hδpos, mul_one]
  have h3 : ‖∫ t in (x - δ)..(x + δ), (B t - B x) * stepBump x δ t‖ ≤ ε / 2 := le_trans hbound hval.le
  rw [Real.norm_eq_abs, hdiff] at h3
  rw [Real.dist_eq]
  have h4 : (∫ t in (x - δ)..(x + δ), B t * stepBump x δ t) - ∫ t in (x - δ)..(x + δ), B x * stepBump x δ t = (∫ t in (x - δ)..(x + δ), B t * stepBump x δ t) - B x := by
    rw [hconst]
  rw [h4] at h3
  linarith


theorem smoothStep_anti {x y : ℝ} {δ : ℝ} (hδ : 0 < δ) (hxy : x ≤ y) (t : ℝ) :
    smoothStep y δ t ≤ smoothStep x δ t := by
  unfold smoothStep
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith

/-- The radial profile `M = S_b - S_a` of the radial test function: nonpositive, zero off `(a - δ, b + δ)`. -/
noncomputable def radialProfile (a b δ : ℝ) : ℝ → ℝ := fun t => smoothStep b δ t - smoothStep a δ t

theorem radialProfile_contDiff (a b δ : ℝ) : ContDiff ℝ ∞ (radialProfile a b δ) :=
  (smoothStep_contDiff b δ).sub (smoothStep_contDiff a δ)

theorem radialProfile_nonpos {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (t : ℝ) :
    radialProfile a b δ t ≤ 0 := by
  unfold radialProfile
  linarith [smoothStep_anti (x := a) (y := b) hδ hab t]

theorem radialProfile_eq_zero_of_le {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {t : ℝ} (ht : t ≤ a - δ) :
    radialProfile a b δ t = 0 := by
  unfold radialProfile
  rw [smoothStep_eq_zero_of_le a hδ ht, smoothStep_eq_zero_of_le b hδ (by linarith)]
  ring

theorem radialProfile_eq_zero_of_ge {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {t : ℝ} (ht : b + δ ≤ t) :
    radialProfile a b δ t = 0 := by
  unfold radialProfile
  rw [smoothStep_eq_one_of_le b hδ ht, smoothStep_eq_one_of_le a hδ (by linarith)]
  ring

theorem radialProfile_deriv (a b δ : ℝ) :
    deriv (radialProfile a b δ) = fun t => stepBump b δ t - stepBump a δ t := by
  funext t
  unfold radialProfile
  have h1 := (smoothStep_contDiff b δ).differentiable (by simp) t
  have h2 := (smoothStep_contDiff a δ).differentiable (by simp) t
  exact deriv_sub h1 h2

/-- `N(t) = -M(t)/t`: smooth on `ℝ` because `M` vanishes on `(-∞, a - δ]` and `a - δ > 0`. -/
noncomputable def radialKernel (a b δ : ℝ) : ℝ → ℝ := fun t => -(radialProfile a b δ t) / t

theorem radialKernel_contDiff {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (ha : δ < a) :
    ContDiff ℝ ∞ (radialKernel a b δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t0
  by_cases ht0 : t0 < a - δ
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds ht0] with t ht
    show -(radialProfile a b δ t) / t = 0
    rw [radialProfile_eq_zero_of_le hδ hab (le_of_lt ht)]
    simp
  · have hpos : 0 < t0 := by linarith [not_lt.mp ht0]
    exact ((radialProfile_contDiff a b δ).neg.contDiffAt).div contDiffAt_id hpos.ne'

theorem radialKernel_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ radialKernel a b δ t := by
  unfold radialKernel
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, div_zero]
  · exact div_nonneg (by linarith [radialProfile_nonpos hδ hab t]) h.le

theorem radialKernel_eq_zero_of_ge {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {t : ℝ} (ht : b + δ ≤ t) :
    radialKernel a b δ t = 0 := by
  unfold radialKernel
  rw [radialProfile_eq_zero_of_ge hδ hab ht]
  simp

/-- The radial primitive `K(q) = ∫_q^{b+δ} N(t) dt` of the test function. -/
noncomputable def radialTest (a b δ : ℝ) : ℝ → ℝ := fun q => ∫ t in q..(b + δ), radialKernel a b δ t

theorem radialTest_hasDerivAt {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (ha : δ < a) (q : ℝ) :
    HasDerivAt (radialTest a b δ) (-(radialKernel a b δ q)) q := by
  have hc := (radialKernel_contDiff hδ hab ha).continuous
  exact intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem radialTest_contDiff {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (ha : δ < a) :
    ContDiff ℝ ∞ (radialTest a b δ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun q => (radialTest_hasDerivAt hδ hab ha q).differentiableAt, ?_⟩
  have hd : deriv (radialTest a b δ) = fun q => -(radialKernel a b δ q) :=
    funext fun q => (radialTest_hasDerivAt hδ hab ha q).deriv
  rw [hd]
  exact (radialKernel_contDiff hδ hab ha).neg

theorem radialTest_eq_zero_of_ge {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {q : ℝ} (hq : b + δ ≤ q) :
    radialTest a b δ q = 0 := by
  unfold radialTest
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => by
    have htb : b + δ ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2]
    exact radialKernel_eq_zero_of_ge hδ hab htb)]
  simp

theorem radialTest_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ radialTest a b δ q := by
  by_cases hq' : q ≤ b + δ
  · apply intervalIntegral.integral_nonneg hq'
    intro t ht
    exact radialKernel_nonneg hδ hab (le_trans hq ht.1)
  · rw [radialTest_eq_zero_of_ge hδ hab (le_of_lt (not_le.mp hq'))]

theorem radialTest_mul_deriv {a b δ : ℝ} (hδ : 0 < δ) (hab : a ≤ b) (ha : δ < a) (t : ℝ) :
    t * deriv (radialTest a b δ) t = radialProfile a b δ t := by
  rw [(radialTest_hasDerivAt hδ hab ha t).deriv]
  unfold radialKernel
  by_cases ht : t = 0
  · subst ht
    simp [radialProfile_eq_zero_of_le hδ hab (by linarith : (0 : ℝ) ≤ a - δ)]
  · field_simp

/-- The mean of `f` over the circle of radius `√q` about `c`, as a function of the squared radius `q`
(the interval integral over one period of the angle). -/
noncomputable def sqMeanB (f : ℂ → ℝ) (c : ℂ) (q : ℝ) : ℝ :=
  ∫ θ in (-π)..π, f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))

theorem sqMeanB_continuousWithinAt {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hf : ContinuousOn f (closedBall c ρ))
    (hρ : 0 ≤ ρ) {q0 : ℝ} (hq0 : q0 < ρ ^ 2) :
    ContinuousWithinAt (sqMeanB f c) (Iio (ρ ^ 2)) q0 := by
  have hmaps : ∀ q ∈ Iio (ρ ^ 2), ∀ θ : ℝ, c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I) ∈
      closedBall c ρ := by
    intro q hq θ
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg q)]
    have hq' : q < ρ ^ 2 := hq
    calc Real.sqrt q ≤ Real.sqrt (ρ ^ 2) := Real.sqrt_le_sqrt hq'.le
      _ = ρ := Real.sqrt_sq hρ
  obtain ⟨M, hM⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn hf
  have hcontθ : ∀ q ∈ Iio (ρ ^ 2), Continuous (fun θ' : ℝ =>
      f (c + (Real.sqrt q : ℂ) * Complex.exp (θ' * Complex.I))) := by
    intro q hq
    have hc : Continuous (fun θ' : ℝ => c + (Real.sqrt q : ℂ) * Complex.exp (θ' * Complex.I)) := by
      fun_prop
    exact hf.comp_continuous hc (fun θ' => hmaps q hq θ')
  have hcontq : ∀ θ : ℝ, ContinuousWithinAt (fun q : ℝ =>
      f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))) (Iio (ρ ^ 2)) q0 := by
    intro θ
    have hc : Continuous (fun q : ℝ => c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I)) := by
      fun_prop
    have hmem : c + (Real.sqrt q0 : ℂ) * Complex.exp (θ * Complex.I) ∈ closedBall c ρ :=
      hmaps q0 hq0 θ
    exact ContinuousWithinAt.comp (g := f)
      (f := fun q : ℝ => c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I)) (hf _ hmem)
      hc.continuousWithinAt (fun (q : ℝ) (hq : q ∈ Iio (ρ ^ 2)) => hmaps q hq θ)
  unfold sqMeanB
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hcontθ q hq).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with q hq
    refine ae_of_all _ fun θ _ => ?_
    exact hM _ (hmaps q hq θ)
  · exact ae_of_all _ fun θ _ => hcontq θ

/-- Integral over `(0, ∞)` of a function vanishing off `[α, β]` (with `0 < α`) is the interval integral. -/
theorem setIntegral_Ioi_eq_intervalIntegral {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hF : ∀ q, q ∉ Icc α β → F q = 0) :
    ∫ q in Ioi (0 : ℝ), F q = ∫ q in α..β, F q := by
  have hsub : Icc α β ⊆ Ioi 0 := fun q hq => lt_of_lt_of_le hα hq.1
  have h't : ∀ q ∈ Ioi (0 : ℝ) \ Icc α β, F q = 0 := fun q hq => hF q hq.2
  rw [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub h't

/-- Integrability on `(0, ∞)` of a continuous function on `[α, β]` vanishing off it. -/
theorem integrableOn_Ioi_of_continuousOn_Icc {F : ℝ → ℝ} {α β : ℝ} (hF : ContinuousOn F (Icc α β))
    (hz : ∀ q, q ∉ Icc α β → F q = 0) :
    IntegrableOn F (Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn F (Icc α β) := hF.integrableOn_compact isCompact_Icc
  refine IntegrableOn.of_forall_sdiff_eq_zero h1 measurableSet_Ioi (fun q hq => hz q hq.2)

/-- The radial inequality, in the form needed for the mean value property: if `f` is distributionally
superharmonic along the radial test functions `K(‖· - c‖²)` (the hypothesis `hrad`), then the circle means
`sqMeanB f c` satisfy `∫_{a-δ}^{a+δ} B g_a ≥ ∫_{b-δ}^{b+δ} B g_b` for the bumps `g_x = stepBump x δ`. -/
theorem sqMeanB_bump_le {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hf : ContinuousOn f (closedBall c ρ))
    {a b δ : ℝ} (hδ : 0 < δ) (hab : a < b) (ha : δ < a) (hbδ : b + 2 * δ ≤ ρ ^ 2)
    (hrad : ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K → (∀ q, 0 ≤ q → 0 ≤ K q) → (∀ q, b + δ ≤ q → K q = 0) →
      ∫ y, f y * Δ (fun z => K (‖z - c‖ ^ 2)) y ≤ 0) :
    (∫ q in (b - δ)..(b + δ), sqMeanB f c q * stepBump b δ q) -
      ∫ q in (a - δ)..(a + δ), sqMeanB f c q * stepBump a δ q ≤ 0 := by
  have hBc : ContinuousOn (sqMeanB f c) (Iio (ρ ^ 2)) := fun q hq => sqMeanB_continuousWithinAt hf hρ hq
  set K := radialTest a b δ with hKdef
  have hKc := radialTest_contDiff hδ hab.le ha
  have hKnn : ∀ q, 0 ≤ q → 0 ≤ K q := fun q hq => radialTest_nonneg hδ hab.le hq
  have hKz : ∀ q, b + δ ≤ q → K q = 0 := fun q hq => radialTest_eq_zero_of_ge hδ hab.le hq
  have hmain := hrad K hKc hKnn hKz
  -- the Laplacian of the test function
  have hlap : ∀ y : ℂ, Δ (fun z => K (‖z - c‖ ^ 2)) y =
      4 * (stepBump b δ (‖y - c‖ ^ 2) - stepBump a δ (‖y - c‖ ^ 2)) := by
    intro y
    rw [laplacian_comp_normSq_sub' K hKc c y]
    have hfun : (fun t : ℝ => t * deriv K t) = radialProfile a b δ :=
      funext fun t => radialTest_mul_deriv hδ hab.le ha t
    rw [hfun, radialProfile_deriv]
  set G : ℝ → ℝ := fun q => stepBump b δ q - stepBump a δ q with hGdef
  have hGc : Continuous G := (stepBump_contDiff b δ).continuous.sub (stepBump_contDiff a δ).continuous
  set ρ' : ℝ := Real.sqrt (b + 2 * δ) with hρ'def
  have hρ'0 : 0 ≤ ρ' := Real.sqrt_nonneg _
  have hρ'sq : ρ' ^ 2 = b + 2 * δ := Real.sq_sqrt (by linarith)
  have hρ'le : ρ' ≤ ρ := by
    calc ρ' = Real.sqrt (b + 2 * δ) := rfl
      _ ≤ Real.sqrt (ρ ^ 2) := Real.sqrt_le_sqrt hbδ
      _ = ρ := Real.sqrt_sq hρ
  have hfρ' : ContinuousOn f (closedBall c ρ') := hf.mono (closedBall_subset_closedBall hρ'le)
  have hG0 : ∀ q, ρ' ^ 2 ≤ q → G q = 0 := by
    intro q hq
    have hq1 : b + δ < q := by linarith
    simp only [hGdef]
    rw [stepBump_eq_zero_of_gt b hδ hq1, stepBump_eq_zero_of_gt a hδ (by linarith)]
    ring
  have hpolar := integral_mul_radial_sq_eq_polar f c ρ' hρ'0 hfρ' G hGc hG0
  -- the test-function integral is `4 ∫ f G(‖·‖²)`
  have hint : ∫ y, f y * Δ (fun z => K (‖z - c‖ ^ 2)) y = 4 * ∫ y, f y * G (‖y - c‖ ^ 2) := by
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [hlap y]
    simp only [hGdef]
    ring
  rw [hint, hpolar] at hmain
  have hJ : ∫ q in Ioi (0 : ℝ), (∫ θ in (-π)..π, f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))) * G q ≤ 0 := by
    linarith
  have hFb : ∀ x : ℝ, x + δ < ρ ^ 2 → ∀ q, q ∉ Icc (x - δ) (x + δ) → sqMeanB f c q * stepBump x δ q = 0 := by
    intro x _ q hq
    have hor : q < x - δ ∨ x + δ < q := by
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact hq ⟨h.1, h.2⟩
    rcases hor with h1 | h1
    · simp [stepBump_eq_zero_of_lt x hδ h1]
    · simp [stepBump_eq_zero_of_gt x hδ h1]
  have hCb : ∀ x : ℝ, x + δ < ρ ^ 2 → ContinuousOn (fun q => sqMeanB f c q * stepBump x δ q) (Icc (x - δ) (x + δ)) := by
    intro x hx
    have hsub : Icc (x - δ) (x + δ) ⊆ Iio (ρ ^ 2) := fun q hq => lt_of_le_of_lt hq.2 hx
    exact (hBc.mono hsub).mul (stepBump_contDiff x δ).continuous.continuousOn
  have hIb : IntegrableOn (fun q => sqMeanB f c q * stepBump b δ q) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_of_continuousOn_Icc (hCb b (by linarith)) (fun q hq => hFb b (by linarith) q hq)
  have hIa : IntegrableOn (fun q => sqMeanB f c q * stepBump a δ q) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_of_continuousOn_Icc (hCb a (by linarith)) (fun q hq => hFb a (by linarith) q hq)
  have hsplit : ∫ q in Ioi (0 : ℝ), (∫ θ in (-π)..π, f (c + (Real.sqrt q : ℂ) * Complex.exp (θ * Complex.I))) * G q =
      (∫ q in Ioi (0 : ℝ), sqMeanB f c q * stepBump b δ q) - ∫ q in Ioi (0 : ℝ), sqMeanB f c q * stepBump a δ q := by
    rw [← integral_sub hIb hIa]
    congr 1
    funext q
    simp only [hGdef, sqMeanB, mul_sub]
  have hbI : ∫ q in Ioi (0 : ℝ), sqMeanB f c q * stepBump b δ q = ∫ q in (b - δ)..(b + δ), sqMeanB f c q * stepBump b δ q :=
    setIntegral_Ioi_eq_intervalIntegral (by linarith) (by linarith) (fun q hq => hFb b (by linarith) q hq)
  have haI : ∫ q in Ioi (0 : ℝ), sqMeanB f c q * stepBump a δ q = ∫ q in (a - δ)..(a + δ), sqMeanB f c q * stepBump a δ q :=
    setIntegral_Ioi_eq_intervalIntegral (by linarith) (by linarith) (fun q hq => hFb a (by linarith) q hq)
  linarith


/-- Monotonicity of the circle means along squared radii, from the radial inequality. -/
theorem sqMeanB_anti_of {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : ContinuousOn f (closedBall c ρ))
    (hrad : ∀ b δ : ℝ, 0 < δ → b + 2 * δ ≤ ρ ^ 2 → ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K →
      (∀ q, 0 ≤ q → 0 ≤ K q) → (∀ q, b + δ ≤ q → K q = 0) →
      ∫ y, f y * Δ (fun z => K (‖z - c‖ ^ 2)) y ≤ 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < ρ ^ 2) :
    sqMeanB f c b ≤ sqMeanB f c a := by
  have hBc : ContinuousOn (sqMeanB f c) (Iio (ρ ^ 2)) := fun q hq => sqMeanB_continuousWithinAt hf hρ.le hq
  have hta := tendsto_integral_mul_stepBump isOpen_Iio hBc (x := a) (show a ∈ Iio (ρ ^ 2) by simp; linarith)
  have htb := tendsto_integral_mul_stepBump isOpen_Iio hBc (x := b) (show b ∈ Iio (ρ ^ 2) from hb)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (∫ q in (b - δ)..(b + δ), sqMeanB f c q * stepBump b δ q) -
      ∫ q in (a - δ)..(a + δ), sqMeanB f c q * stepBump a δ q ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min a ((ρ ^ 2 - b) / 2) from
      lt_min ha (by linarith))] with δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hδa : δ < a := lt_of_lt_of_le hδ.2 (min_le_left _ _)
    have hδb : δ < (ρ ^ 2 - b) / 2 := lt_of_lt_of_le hδ.2 (min_le_right _ _)
    exact sqMeanB_bump_le hρ.le hf hδ0 hab hδa (by linarith) (hrad b δ hδ0 (by linarith))
  have hlim := htb.sub hta
  have := le_of_tendsto hlim hev
  linarith

/-- The circle mean at radius `0` is the value at the centre. -/
theorem sqMeanB_zero (f : ℂ → ℝ) (c : ℂ) : sqMeanB f c 0 = 2 * π * f c := by
  unfold sqMeanB
  simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_mul, add_zero, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

/-- Circle means at the centre limit: `sqMeanB b ≤ 2π f c` for `0 < b < ρ²`. -/
theorem sqMeanB_le_centre {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hf : ContinuousOn f (closedBall c ρ))
    (hrad : ∀ b δ : ℝ, 0 < δ → b + 2 * δ ≤ ρ ^ 2 → ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K →
      (∀ q, 0 ≤ q → 0 ≤ K q) → (∀ q, b + δ ≤ q → K q = 0) →
      ∫ y, f y * Δ (fun z => K (‖z - c‖ ^ 2)) y ≤ 0)
    {b : ℝ} (hb0 : 0 < b) (hb : b < ρ ^ 2) :
    sqMeanB f c b ≤ 2 * π * f c := by
  have hBc : ContinuousOn (sqMeanB f c) (Iio (ρ ^ 2)) := fun q hq => sqMeanB_continuousWithinAt hf hρ.le hq
  have h0 : (0 : ℝ) < ρ ^ 2 := by positivity
  have hcont0 : ContinuousWithinAt (sqMeanB f c) (Ioi 0) 0 :=
    (sqMeanB_continuousWithinAt hf hρ.le h0).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds h0))
  rw [← sqMeanB_zero]
  refine ge_of_tendsto hcont0.tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT hb0] with a ha
  exact sqMeanB_anti_of hρ hf hrad ha.1 ha.2 hb

/-- Circle means in the normalized form of `Real.circleAverage`. -/
theorem circleAverage_eq_sqMeanB (f : ℂ → ℝ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage f c r = (2 * π)⁻¹ * sqMeanB f c (r ^ 2) := by
  rw [Real.circleAverage_def]
  unfold sqMeanB
  rw [Real.sqrt_sq hr, smul_eq_mul]
  congr 1
  have hper : Function.Periodic (fun θ : ℝ => f (c + (r : ℂ) * Complex.exp (θ * Complex.I))) (2 * π) := by
    intro θ
    have h2 : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    have h3 : (((θ + 2 * π : ℝ)) : ℂ) * Complex.I = (θ : ℂ) * Complex.I + ((2 * π : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    simp only [h3, Complex.exp_add, h2, mul_one]
  have h1 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, show (0 : ℝ) + 2 * π = 2 * π by ring] at h1
  exact h1.symm

/-- Distributional superharmonicity along the radial test functions `K(‖· - c‖²)`, `K` smooth and nonnegative on
`[0, ∞)` and vanishing from `T` on, gives the super-mean-value inequality of the circle averages. -/
theorem superMeanValueOn_of_distribLaplacianLE {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (h : DistribLaplacianLE f 0 U) : SuperMeanValueOn f U := by
  intro c r hr hball
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall c r).exists_thickening_subset_open hU hball
  set R : ℝ := r + δ / 2 with hR
  have hRpos : 0 < R := by linarith
  have hsubR : closedBall c R ⊆ U := by
    intro y hy
    apply hthick
    rw [thickening_closedBall hδ hr.le]
    exact closedBall_subset_ball (by linarith) hy
  have hfR : ContinuousOn f (closedBall c R) := hf.mono hsubR
  have hrad : ∀ b δ' : ℝ, 0 < δ' → b + 2 * δ' ≤ R ^ 2 → ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K →
      (∀ q, 0 ≤ q → 0 ≤ K q) → (∀ q, b + δ' ≤ q → K q = 0) →
      ∫ y, f y * Δ (fun z => K (‖z - c‖ ^ 2)) y ≤ 0 := by
    intro b δ' _ hbδ K hK hKnn hKz
    set φ : ℂ → ℝ := fun z => K (‖z - c‖ ^ 2) with hφ
    have hφc : ContDiff ℝ ∞ φ := hK.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
    have hsupp : Function.support φ ⊆ closedBall c R := by
      intro z hz
      rw [Function.mem_support] at hz
      rw [mem_closedBall, dist_eq_norm]
      by_contra hcon
      have hlt : R < ‖z - c‖ := lt_of_not_ge hcon
      have hge : b + δ' ≤ ‖z - c‖ ^ 2 := by nlinarith [norm_nonneg (z - c)]
      exact hz (hKz _ hge)
    have hφsupp : HasCompactSupport φ := by
      refine HasCompactSupport.intro (isCompact_closedBall c R) (fun z hz => ?_)
      by_contra hne
      exact hz (hsupp (Function.mem_support.mpr hne))
    have htsupp : tsupport φ ⊆ U := (closure_minimal hsupp isClosed_closedBall).trans hsubR
    have hφtest : LatticeProb.IsTestFunction U φ := ⟨hφc, hφsupp, htsupp⟩
    have hφnn : 0 ≤ φ := fun z => hKnn _ (by positivity)
    have hint : Integrable φ (0 : Measure ℂ) := integrable_zero_measure
    have := h.2 φ hφtest hφnn hint
    simpa using this
  have hcentre := sqMeanB_le_centre hRpos hfR hrad (b := r ^ 2) (by positivity)
    (by nlinarith)
  rw [circleAverage_eq_sqMeanB f c hr.le]
  have hpi : 0 < 2 * π := by positivity
  calc (2 * π)⁻¹ * sqMeanB f c (r ^ 2) ≤ (2 * π)⁻¹ * (2 * π * f c) :=
        mul_le_mul_of_nonneg_left hcentre (by positivity)
    _ = f c := by field_simp

end LatticeProb
