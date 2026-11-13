/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RescaledFddCharFunReduction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GaussianWeakLimitClosure
import LatticeProb.Bonanno.ReflectedGMS.Limit.UnstoppedContinuousLindeberg
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
import LatticeProb.Bonanno.ReflectedGMS.Limit.MultiTimeCharFunFromIncrements
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# `RescaledFddCharFunLimits` reduced to one-increment limits on the walk's sample space

`GaussianWeakLimitClosure.RescaledFddCharFunLimits μ target` asks, along every sequence of
scales `ε k → 0⁺` and for every finite family of times and directions, that the
finite-dimensional characteristic functions of the diffusively rescaled path laws converge
to the Gaussian ones.  It is a statement about laws on `C(ℝ≥0, Euc 2)`.  This file moves it
to the **sample space of the walk**, where the filtration and the adapted martingale live,
and reduces it to three inputs:

* `hinc` (`RescaledIncrementCharFunLimit`) — the **one-increment conditional
  characteristic-function limit**: for the diffusively rescaled adapted process
  `Xᵏ(t) = εₖ • M(t/εₖ²)` and the rescaled filtration `𝔽ᵏ(s) = 𝔽(s/εₖ²)`,

    `∫ ‖ P[exp(i⟪η, Xᵏ(t) − Xᵏ(s)⟫) | 𝔽ᵏ(s)] − exp(−(ηᵀ Σ η)(t−s)/2) ‖ dP ⟶ 0`.

  This is exactly the shape the project's Lindeberg / characteristic-function chain
  produces (`ConditionalGaussianIdentification`, `GaussianIdentificationUnlocalization`,
  `UnstoppedContinuousLindeberg`), and it is the multi-time martingale CLT's only
  probabilistic content.
* `hinterp` (`RescaledInterpolationErrorVanishes`) — at every fixed rescaled time the
  continuous interpolation `Iw` and the adapted process `M` differ by a quantity tending to
  `0` in probability.  (The interpolation is not adapted — it looks one holding interval
  ahead — so the conditional statement must be about `M`, and the interpolation is
  compared afterwards.)
* the deterministic start `M 0 = p` a.s. (the same `h0` the consumer already carries for
  `Iw`).

## Route

1. `fddCharFun_diffusivelyRescaled_map` — transport: the finite-dimensional
   characteristic function of `diffusivelyRescaledPathLaw (P.map Iw) ε` is the integral
   over the walk's sample space of `exp (i ∑ⱼ ⟪θⱼ, ε • Iw(uⱼ/ε²)⟫)`.  (No positivity of `ε`
   is needed: at `ε = 0` both sides are the constant path.)
2. `MultiTimeCharFun.tendsto_integral_cexp_sub_of_tendstoInMeasure` — replace the
   interpolation by the adapted process at the finitely many rescaled times, using `hinterp`.
3. `MultiTimeCharFun.tendsto_integral_cexp_finSum` — the multi-time limit for the adapted
   process from `hinc`, peeling one increment at a time.

## Anti-vacuity

`FddClusterReduction.lean:80` records that the identification input follows from the
convergence it helps to produce; so a discharge must never use anything conclusion-shaped.
**Nothing here assumes a weak limit, a tightness statement, a finite-dimensional
convergence of laws or a scaling limit.**  Both new inputs are statements on the walk's
own sample space: an `L¹` limit of conditional characteristic functions given the walk's
past, and an in-probability comparison at fixed times.

Satisfiability, machine-checked and non-circular:

* `rescaledIncrementCharFunLimit_of_projectionSquareMartingale` — **every** process whose
  scalar projections are continuous square-integrable martingales with the deterministic
  bracket `(θᵀ Σ θ) u` (`BrownianFdd.ProjectionSquareMartingale`) satisfies `hinc`, with
  error exactly `0` at every positive scale, via
  `UnstoppedContinuousLindeberg.condExp_cexp_increment_eq_exp_of_continuous_square_martingale`
  (diffusive rescaling preserves the exact bracket).  This is the "feed from
  `UnstoppedContinuousLindeberg`" step: the exact-bracket case is the base case of the
  martingale CLT, and it is discharged.
* `rescaledInterpolationErrorVanishes_of_eq` — `hinterp` holds when the interpolation is
  the process itself.

Honest accounting: this is a **REDUCTION**, not a discharge, of `RescaledFddCharFunLimits`.
What is gained is that the atom is now a *one-increment* statement *with a filtration*, on
the walk's sample space, in exactly the output shape of the project's Lindeberg machinery;
what remains is the approximate-bracket version of that machinery (the bracket of the
walk is random and only converges to `tΣ` in probability), which is genuinely new.

CONDITIONAL on `hinc`, `hinterp`; nothing about the reflected walk is proved here.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace ReflectedGMS.RescaledFddCharFun

open ReflectedGMS.StatementIngredients ReflectedGMS.GaussianWeakLimit
open ReflectedGMS.GaussianLimitIdentification ReflectedGMS.MultiTimeCharFun
open ReflectedGMS.BrownianFdd ReflectedGMS.FddClusterReduction
open ReflectedGMS.TwoClockScalingLimitReduction ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Diffusive rescaling on the sample space -/

/-- The diffusively rescaled process `t ↦ ε • M (t / ε²)`. -/
noncomputable def rescaleProcess (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (ε : ℝ≥0) (t : ℝ≥0)
    (ω : Ω) : BouRabeeGwynne.Euc 2 :=
  (ε : ℝ) • M (ε⁻¹ ^ 2 * t) ω

/-- The diffusively rescaled filtration `t ↦ 𝔽 (t / ε²)`. -/
noncomputable def rescaleFiltration (𝔽 : Filtration ℝ≥0 mΩ) (ε : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := 𝔽 (ε⁻¹ ^ 2 * t)
  mono' _ _ hab := 𝔽.mono (mul_le_mul_of_nonneg_left hab zero_le)
  le' _ := 𝔽.le _

theorem stronglyMeasurable_rescaleProcess {𝔽 : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2} (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (ε t : ℝ≥0) : StronglyMeasurable[rescaleFiltration 𝔽 ε t] (rescaleProcess M ε t) := by
  show StronglyMeasurable[rescaleFiltration 𝔽 ε t] ((ε : ℝ) • M (ε⁻¹ ^ 2 * t))
  exact (hadapt _).const_smul _

/-- The scalar projection `⟪η, ε • M (u / ε²)⟫` of the rescaled process. -/
noncomputable def rescaledProjection (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (ε : ℝ≥0)
    (η : BouRabeeGwynne.Euc 2) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ⟪η, rescaleProcess M ε u ω⟫_ℝ

theorem rescaledProjection_eq (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (ε : ℝ≥0)
    (η : BouRabeeGwynne.Euc 2) (u : ℝ≥0) (ω : Ω) :
    rescaledProjection M ε η u ω = (ε : ℝ) * ⟪η, M (ε⁻¹ ^ 2 * u) ω⟫_ℝ := by
  rw [rescaledProjection, rescaleProcess, real_inner_smul_right]

/-! ## Transport of the finite-dimensional characteristic function -/

/-- The rescaling map, without any positivity assumption on the scale. -/
theorem scaledBrownianPath_inv_apply' (ε : ℝ≥0) (ω : BouRabeeGwynne.BrownianPath 2)
    (t : ℝ≥0) :
    BouRabeeGwynne.scaledBrownianPath ε⁻¹ ω t = (ε : ℝ) • ω (ε⁻¹ ^ 2 * t) := by
  rw [BouRabeeGwynne.scaledBrownianPath_apply]
  simp

/-- **Transport.**  The finite-dimensional characteristic function of the diffusively
rescaled interpolation law is an oscillatory integral over the walk's sample space. -/
theorem fddCharFun_diffusivelyRescaled_map [IsProbabilityMeasure P]
    (Iw : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable Iw) (ε : ℝ≥0)
    {ι : Type*} [Fintype ι] (u : ι → ℝ≥0) (θ : ι → BouRabeeGwynne.Euc 2) :
    fddCharFun (diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map Iw) ε :
        Measure (BouRabeeGwynne.BrownianPath 2)) u θ
      = ∫ ω, Complex.exp
          (((∑ i, ⟪θ i, (ε : ℝ) • Iw ω (ε⁻¹ ^ 2 * u i)⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂P := by
  have hcoe : ((diffusivelyRescaledPathLaw (P.toProbabilityMeasure.map Iw) ε :
      ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
      Measure (BouRabeeGwynne.BrownianPath 2))
      = (P.map Iw).map (BouRabeeGwynne.scaledBrownianPath ε⁻¹) := rfl
  have hc : Continuous fun f : BouRabeeGwynne.BrownianPath 2 =>
      Complex.exp ((pathCombination u θ f : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_pathCombination u θ)).mul continuous_const)
  rw [fddCharFun, hcoe,
    Measure.map_map (BouRabeeGwynne.measurable_scaledBrownianPath (d := 2) ε⁻¹) hI,
    integral_map ((BouRabeeGwynne.measurable_scaledBrownianPath (d := 2) ε⁻¹).comp hI).aemeasurable
      hc.measurable.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply, pathCombination, scaledBrownianPath_inv_apply']

/-! ## The two named inputs on the walk's sample space -/

/-- **The one-increment conditional characteristic-function limit of the diffusively
rescaled adapted process.**  Along every sequence of scales `ε k → 0⁺`, for every
direction `η` and every pair of times `s ≤ t`, the conditional characteristic function of
the rescaled increment given the rescaled past converges in `L¹` to the Gaussian factor
`exp (-(ηᵀ Σ η)(t - s)/2)`.  This is the multi-time martingale CLT's only probabilistic
content, in the exact output shape of the project's Lindeberg chain. -/
def RescaledIncrementCharFunLimit (P : Measure Ω) (𝔽 : Filtration ℝ≥0 mΩ)
    (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) (target : AnisotropicBrownianTarget) : Prop :=
  ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) →
    ∀ (η : BouRabeeGwynne.Euc 2) (s t : ℝ≥0), s ≤ t →
      Tendsto (fun k => ∫ ω, ‖(P[fun ω => Complex.exp
          ((⟪η, rescaleProcess M (ε k) t ω - rescaleProcess M (ε k) s ω⟫_ℝ : ℂ) * Complex.I)
            | rescaleFiltration 𝔽 (ε k) s]) ω
          - gaussFactor (bilinForm target.covariance) η s t‖ ∂P) atTop (𝓝 0)

/-- **The interpolation error at fixed rescaled times vanishes in probability.**  Along
every sequence of scales `ε k → 0⁺` and at every time `u`, the rescaled interpolation
`ε • Iw (u / ε²)` and the rescaled adapted process `ε • M (u / ε²)` differ by a quantity
tending to `0` in probability. -/
def RescaledInterpolationErrorVanishes (P : Measure Ω) (Iw : Ω → BouRabeeGwynne.BrownianPath 2)
    (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2) : Prop :=
  ∀ ε : ℕ → ℝ≥0, Tendsto ε atTop (nhdsWithin (0 : ℝ≥0) (Set.Ioi 0)) → ∀ u : ℝ≥0,
    TendstoInMeasure P
      (fun k ω => (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u) - rescaleProcess M (ε k) u ω) atTop 0

/-! ## The target's bilinear form -/

theorem bilinForm_add_left (target : AnisotropicBrownianTarget) (a b c : BouRabeeGwynne.Euc 2) :
    bilinForm target.covariance (a + b) c
      = bilinForm target.covariance a c + bilinForm target.covariance b c := by
  simp only [bilinForm, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem bilinForm_symm (target : AnisotropicBrownianTarget) (a b : BouRabeeGwynne.Euc 2) :
    bilinForm target.covariance a b = bilinForm target.covariance b a := by
  rw [GaussianLimitInputAtTarget.bilinForm_covariance_eq,
    GaussianLimitInputAtTarget.bilinForm_covariance_eq, real_inner_comm]

theorem bilinForm_self_nonneg (target : AnisotropicBrownianTarget) (a : BouRabeeGwynne.Euc 2) :
    0 ≤ bilinForm target.covariance a a := by
  rw [GaussianLimitInputAtTarget.bilinForm_covariance_eq]
  exact real_inner_self_nonneg

/-! ## The reduction -/

/-- **`RescaledFddCharFunLimits` from the one-increment limits.**  The rescaled
interpolation law's finite-dimensional characteristic functions converge to the Gaussian
ones, given: adaptedness of `M`, the deterministic start `M 0 = p`, the one-increment
conditional characteristic-function limit `hinc`, and the vanishing interpolation error
`hinterp`.  No weak limit, tightness, or fdd convergence of laws is assumed. -/
theorem rescaledFddCharFunLimits_of_increment_limits [IsProbabilityMeasure P]
    (Iw : Ω → BouRabeeGwynne.BrownianPath 2) (hI : Measurable Iw)
    (𝔽 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → BouRabeeGwynne.Euc 2)
    (hadapt : ∀ t, StronglyMeasurable[𝔽 t] (M t))
    (p : BouRabeeGwynne.Euc 2) (h0 : ∀ᵐ ω ∂P, M 0 ω = p)
    (target : AnisotropicBrownianTarget)
    (hinc : RescaledIncrementCharFunLimit P 𝔽 M target)
    (hinterp : RescaledInterpolationErrorVanishes P Iw M) :
    RescaledFddCharFunLimits (P.toProbabilityMeasure.map Iw) target := by
  intro ε hε n u θ
  have hεR : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) :=
    NNReal.tendsto_coe.2 (tendsto_nhds_of_tendsto_nhdsWithin hε)
  have hMmeas : ∀ t, Measurable (M t) := fun t => ((hadapt t).mono (𝔽.le t)).measurable
  have hXmeas : ∀ k t, Measurable (rescaleProcess M (ε k) t) := by
    intro k t
    show Measurable ((ε k : ℝ) • M ((ε k)⁻¹ ^ 2 * t))
    exact (hMmeas _).const_smul _
  have hImeas : ∀ t, Measurable (fun ω => Iw ω t) :=
    fun t => (ContinuousMap.measurable_eval t).comp hI
  have hIsm : ∀ (k : ℕ) (t : ℝ≥0), Measurable (fun ω => (ε k : ℝ) • Iw ω t) := by
    intro k t
    show Measurable ((ε k : ℝ) • fun ω => Iw ω t)
    exact (hImeas t).const_smul _
  -- the start
  have hzero : ∀ ϑ : BouRabeeGwynne.Euc 2, Tendsto
      (fun k => ∫ ω, Complex.exp ((⟪ϑ, rescaleProcess M (ε k) 0 ω⟫_ℝ : ℂ) * Complex.I) ∂P)
      atTop (𝓝 1) := by
    intro ϑ
    have hmeas : TendstoInMeasure P
        (fun k ω => ⟪ϑ, rescaleProcess M (ε k) 0 ω⟫_ℝ - (0 : ℝ)) atTop 0 := by
      refine tendstoInMeasure_zero_of_ae_norm_le (c := fun k => (ε k : ℝ) * (‖ϑ‖ * ‖p‖))
        ?_ ?_
      · simpa using hεR.mul_const (‖ϑ‖ * ‖p‖)
      · intro k
        filter_upwards [h0] with ω hω
        simp only [sub_zero, rescaleProcess, mul_zero, hω]
        calc ‖⟪ϑ, (ε k : ℝ) • p⟫_ℝ‖ ≤ ‖ϑ‖ * ‖(ε k : ℝ) • p‖ := norm_inner_le_norm _ _
          _ = (ε k : ℝ) * (‖ϑ‖ * ‖p‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ε k).coe_nonneg]
            ring
    have hdiff := tendsto_integral_cexp_sub_of_tendstoInMeasure
      (a := fun k ω => ⟪ϑ, rescaleProcess M (ε k) 0 ω⟫_ℝ) (b := fun _ _ => (0 : ℝ))
      (fun k => measurable_const.inner (hXmeas k 0)) (fun _ => measurable_const) hmeas
    have h1 : Tendsto (fun _ : ℕ => ∫ _ω, Complex.exp (((0 : ℝ) : ℂ) * Complex.I) ∂P) atTop
        (𝓝 1) := by
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, integral_const, probReal_univ,
        one_smul]
      exact tendsto_const_nhds
    have := hdiff.add h1
    simpa using this
  -- the comparison between the interpolation and the adapted process
  have hcmp := tendsto_integral_cexp_sub_of_tendstoInMeasure (P := P)
    (a := fun k ω => ∑ i, ⟪θ i, (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u i)⟫_ℝ)
    (b := fun k ω => ∑ i, ⟪θ i, rescaleProcess M (ε k) (u i) ω⟫_ℝ)
    (fun k => Finset.measurable_sum _ fun i _ =>
      measurable_const.inner (hIsm k ((ε k)⁻¹ ^ 2 * u i)))
    (fun k => Finset.measurable_sum _ fun i _ => measurable_const.inner (hXmeas k (u i))) ?_
  swap
  · have heq : (fun k ω => (∑ i, ⟪θ i, (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u i)⟫_ℝ)
          - ∑ i, ⟪θ i, rescaleProcess M (ε k) (u i) ω⟫_ℝ)
        = fun k ω => ∑ i, ⟪θ i, (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u i)
            - rescaleProcess M (ε k) (u i) ω⟫_ℝ := by
      funext k ω
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (inner_sub_right _ _ _).symm
    rw [heq]
    refine tendstoInMeasure_zero_finset_sum Finset.univ fun i _ => ?_
    exact tendstoInMeasure_zero_of_norm_le (norm_nonneg (θ i))
      (fun k ω => norm_inner_le_norm _ _) (hinterp ε hε (u i))
  -- the multi-time limit for the adapted process
  have hmain := tendsto_integral_cexp_finSum (fun k => rescaleFiltration 𝔽 (ε k))
    (fun k => rescaleProcess M (ε k)) (fun k t => stronglyMeasurable_rescaleProcess hadapt _ _)
    (bilinForm target.covariance) (bilinForm_add_left target) (bilinForm_symm target)
    (bilinForm_self_nonneg target) hzero (hinc ε hε) n u θ
  -- combine
  have hfinal : Tendsto (fun k => ∫ ω, Complex.exp
      (((∑ i, ⟪θ i, (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u i)⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂P) atTop
      (𝓝 (((Real.exp (-(∑ i, ∑ j, bilinForm target.covariance (θ i) (θ j)
        * ((min (u i) (u j) : ℝ≥0) : ℝ)) / 2)) : ℝ) : ℂ)) := by
    have := hcmp.add hmain
    simpa using this
  have hL : (((Real.exp (-(∑ i, ∑ j, bilinForm target.covariance (θ i) (θ j)
        * ((min (u i) (u j) : ℝ≥0) : ℝ)) / 2)) : ℝ) : ℂ)
      = Complex.exp (-(gaussQuad target u θ : ℂ) / 2) := by
    show (((Real.exp (-(gaussQuad target u θ) / 2)) : ℝ) : ℂ)
      = Complex.exp (-(gaussQuad target u θ : ℂ) / 2)
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hfun : (fun k => fddCharFun (diffusivelyRescaledPathLaw
        (P.toProbabilityMeasure.map Iw) (ε k) : Measure (BouRabeeGwynne.BrownianPath 2)) u θ)
      = fun k => ∫ ω, Complex.exp
          (((∑ i, ⟪θ i, (ε k : ℝ) • Iw ω ((ε k)⁻¹ ^ 2 * u i)⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂P :=
    funext fun k => fddCharFun_diffusivelyRescaled_map Iw hI (ε k) u θ
  rw [hfun, ← hL]
  exact hfinal

/-! ## Satisfiability: the exact-bracket case is discharged -/

/-! ## Machine-checked welds -/

end ReflectedGMS.RescaledFddCharFun
