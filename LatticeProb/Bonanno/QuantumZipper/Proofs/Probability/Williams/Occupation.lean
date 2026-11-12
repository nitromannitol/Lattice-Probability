/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.Occupation at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: set_option autoImplicit true after the imports, the default of the source repository (this library disables it).
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W0
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit true

/-!
Node W3 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), a step of the proof of L14
(`WilliamsDriftDecomposition`). For `Y = dpath σ μ b` (a Brownian motion with diffusion `σ` and
drift `μ`, started at `0`), the occupation measure `occ σ μ`
(`Proofs/Probability/Williams/Defs.lean`) is the mixture `∫_0^∞ law(Y_m) dm` of the
one-dimensional marginals. W3 states that it has a density `occDens σ μ`, that this density is
continuous (for `σ, μ > 0`), and that `occ σ μ A` is the expected total time `Y` spends in `A`.

* `occDens`: `y ↦ ∫_0^∞ gaussianPDFReal (μ m) (σ² m) y dm`;
* `occ_eq` (with `0 < σ` and `0 < μ`, see below): `occ σ μ = volume.withDensity (occDens σ μ)`;
* `continuous_occDens`: `Continuous (occDens σ μ)` for `σ, μ > 0`;
* `occ_eq_lintegral`: `occ σ μ A = ∫⁻ ω, ∫⁻_0^∞ 1_A (Y_m ω) dm ∂P`.

The two remaining items of W3 in the blueprint (`occDens_nonneg_const`, `prob_hit_neg`) use the
strong Markov property at a hitting time and are proved elsewhere.

Routes. `occ_eq` is Tonelli: `occ_apply` (W0) writes `occ σ μ A` as `∫⁻ m, gaussianReal … A`, the
density of `gaussianReal` turns each inner term into an integral of `gaussianPDFReal`, and Tonelli
swaps the two integrals; `ofReal_integral_eq_lintegral_ofReal` moves between the Bochner integral
defining `occDens` and its `ℝ≥0∞`-valued counterpart (this is where integrability, hence `0 < σ`
and `0 < μ`, is used). `occ_eq_lintegral` is the same swap against `P`, plus the law of the
one-dimensional marginal `dpath σ μ b · m`, which is `gaussianReal (μ m) (σ² m)`
(`IsPreBrownianReal.hasLaw_eval`, `gaussianReal_map_const_mul`, `gaussianReal_map_add_const`).
Continuity is dominated convergence (`tendsto_integral_filter_of_dominated_convergence`) with the
bound `gaussianPDFReal (μ m) (σ² m) y ≤ occConst σ μ K * occWeight σ μ m` for `m > 0`, `|y| ≤ K`:
the exponent is `-y²/(2σ²m) + μy/σ² - μ²m/(2σ²)`, whose first term is `≤ 0` and second is
`≤ μ|y|/σ²`, so the dominating function is a constant times `m^{-1/2} e^{-μ²m/(2σ²)}`, which is
integrable on `(0, ∞)` by the Gamma integral `integrableOn_rpow_mul_exp_neg_mul_rpow`.

Hypotheses (deviations from the blueprint sketch; see the report). `occ_eq` needs `0 < σ`
(otherwise `gaussianReal _ 0` is a Dirac mass, whose `gaussianPDFReal _ 0` density vanishes) **and**
`0 < μ` (for `μ = 0` the integral defining `occDens` diverges, so as a Bochner integral it is the
junk value `0` by `integral_undef`, while `occ σ 0` is a nonzero measure). `continuous_occDens`
uses `0 < μ` for the exponential decay of the bound (for `μ < 0` the same proof works with `|μ|`).
`occ_eq_lintegral` needs no hypothesis on `σ`, `μ`. The inner integral of `occ_eq_lintegral` is
taken over `m ∈ (0, ∞) ⊆ ℝ` with `m.toNNReal`, since `ℝ≥0` carries no `volume` (this is the same
convention as in `occ` and `occ_apply`). The variance `σ² m` is written using the abbreviation
`occVar`, whose body is `NNReal.mk (σ^2) _ * m.toNNReal`: this is definitionally the expression
`⟨σ^2, sq_nonneg σ⟩ * m.toNNReal` of `Defs.lean`, written in the canonical constructor form so
that the coercion lemmas apply.

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. VI §1 (occupation
densities) for the object; the convergence argument is an own elementary proof (dominated
convergence with the Gaussian bound above), following the sketch of
`blueprint/EXT_PP_BLUEPRINT.md` §A.1 W3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## The occupation density, and the bound used for its continuity -/

/-- The variance of the `m`-th marginal of `dpath σ μ b`, as a nonnegative real. The body is the
expression `⟨σ^2, sq_nonneg σ⟩ * m.toNNReal` of `occ`, in constructor form. -/
abbrev occVar (σ : ℝ) (m : ℝ) : ℝ≥0 := NNReal.mk (σ ^ 2) (sq_nonneg σ) * m.toNNReal

/-- **W3.** The density of the occupation measure `occ σ μ`: the mixture over `m > 0` of the
Gaussian densities with mean `μ m` and variance `σ² m`. -/
def occDens (σ μ : ℝ) (y : ℝ) : ℝ :=
  ∫ m in Set.Ioi (0 : ℝ), gaussianPDFReal (μ * m) (occVar σ m) y

@[simp]
theorem coe_occVar (σ : ℝ) {m : ℝ} (hm : 0 ≤ m) : ((occVar σ m : ℝ≥0) : ℝ) = σ ^ 2 * m := by
  rw [occVar, NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hm]

/-- If `m > 0` and `σ ≠ 0` then the `m`-th marginal of `dpath σ μ b` is nondegenerate. -/
theorem occVar_ne_zero {σ m : ℝ} (hm : 0 < m) (hσ : σ ≠ 0) : occVar σ m ≠ 0 := by
  rw [occVar]
  refine mul_ne_zero ?_ ?_
  · intro h0
    have h1 : σ ^ 2 = (0 : ℝ) := congrArg (fun x : ℝ≥0 => (x : ℝ)) h0
    exact hσ (mul_self_eq_zero.mp (by rwa [pow_two] at h1))
  · exact (Real.toNNReal_pos.mpr hm).ne'

/-- The weight `m^{-1/2} e^{-(μ²/(2σ²)) m}` of the dominating function. -/
def occWeight (σ μ : ℝ) (m : ℝ) : ℝ := m ^ (-(1 / 2) : ℝ) * Real.exp (-(μ ^ 2 / (2 * σ ^ 2)) * m)

/-- The constant of the dominating function on the band `|y| ≤ K`. -/
def occConst (σ μ K : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (μ * K / σ ^ 2)

/-- Unfolding of the dominating function: it is the product of its `m`-weight and its
`μ|y|`-factor. -/
theorem occConst_mul_occWeight (σ μ K m : ℝ) :
    occConst σ μ K * occWeight σ μ m
      = (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * (m ^ (-(1 / 2) : ℝ))
        * (Real.exp (μ * K / σ ^ 2) * Real.exp (-(μ ^ 2 / (2 * σ ^ 2)) * m)) := by
  rw [occConst, occWeight]; ring

/-- The explicit form of a Gaussian density with variance `σ² m`. -/
theorem gaussianPDFReal_occVar_eq (σ μ : ℝ) {m : ℝ} (hm : 0 ≤ m) (y : ℝ) :
    gaussianPDFReal (μ * m) (occVar σ m) y
      = (Real.sqrt (2 * Real.pi * (σ ^ 2 * m)))⁻¹
        * Real.exp (-(y - μ * m) ^ 2 / (2 * (σ ^ 2 * m))) := by
  rw [gaussianPDFReal_def]
  dsimp only
  rw [coe_occVar σ hm]

/-! ## The Gaussian bound -/

/-- **The Gaussian bound.** For `σ, μ > 0`, `m > 0` and `|y| ≤ K`, the density of the `m`-th
marginal of `dpath σ μ b` at `y` is at most `occConst σ μ K * occWeight σ μ m`. This is the
dominating function of `continuous_occDens` (blueprint §A.1 W3). -/
theorem gaussianPDFReal_le_occBound (hσ : 0 < σ) (hμ : 0 < μ) (K y m : ℝ) (hy : |y| ≤ K)
    (hm : 0 < m) :
    gaussianPDFReal (μ * m) (occVar σ m) y ≤ occConst σ μ K * occWeight σ μ m := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hm0 : (0 : ℝ) ≤ m := hm.le
  -- normalize the exponent
  have hexp : -(y - μ * m) ^ 2 / (2 * (σ ^ 2 * m))
      = -y ^ 2 / (2 * (σ ^ 2 * m)) + μ * y / σ ^ 2 + (-(μ ^ 2 / (2 * σ ^ 2))) * m := by
    field_simp
    ring
  -- the square root of the variance splits as `√(2πσ²) √m`
  have hsqrt : Real.sqrt (2 * Real.pi * (σ ^ 2 * m))
      = Real.sqrt (2 * Real.pi * σ ^ 2) * Real.sqrt m := by
    rw [show 2 * Real.pi * (σ ^ 2 * m) = 2 * Real.pi * σ ^ 2 * m by ring,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * σ ^ 2)]
  have hinv : (Real.sqrt m)⁻¹ = m ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hm0 (1 / 2 : ℝ)]
  rw [gaussianPDFReal_occVar_eq σ μ hm0 y, hsqrt, mul_inv, hinv, hexp,
    Real.exp_add, Real.exp_add, occConst_mul_occWeight]
  -- strip the nonnegative prefactor, then compare the three exponentials
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have he1 : Real.exp (-y ^ 2 / (2 * (σ ^ 2 * m))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnn : (0 : ℝ) ≤ y ^ 2 / (2 * (σ ^ 2 * m)) :=
      div_nonneg (sq_nonneg y) (by positivity)
    have heq : -y ^ 2 / (2 * (σ ^ 2 * m)) = -(y ^ 2 / (2 * (σ ^ 2 * m))) := by ring
    rw [heq]
    linarith
  have he2 : Real.exp (μ * y / σ ^ 2) ≤ Real.exp (μ * K / σ ^ 2) :=
    Real.exp_le_exp.mpr (by
      refine div_le_div_of_nonneg_right ?_ hσ2.le
      nlinarith [abs_le.mp hy, hμ.le])
  have h12 : Real.exp (-y ^ 2 / (2 * (σ ^ 2 * m))) * Real.exp (μ * y / σ ^ 2)
      ≤ Real.exp (μ * K / σ ^ 2) := by
    simpa using mul_le_mul he1 he2 (Real.exp_pos _).le zero_le_one
  exact mul_le_mul h12 le_rfl (Real.exp_pos _).le (Real.exp_pos _).le

/-! ## Measurability of the integrand -/

/-- The integrand of `occDens σ μ` is measurable in `m`. -/
theorem measurable_occDens_integrand (σ μ : ℝ) (y : ℝ) :
    Measurable fun m : ℝ => gaussianPDFReal (μ * m) (occVar σ m) y :=
  measurable_uncurry_gaussianPDFReal.comp
    ((measurable_const.mul measurable_id).prodMk
      ((measurable_const.mul measurable_id.real_toNNReal).prodMk measurable_const))

/-- The integrand of the double integral behind `occ_eq`: joint measurability in `(m, y)`. -/
theorem measurable_uncurry_occIntegrand (σ μ : ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal (μ * p.1) (occVar σ p.1) p.2) :=
  ENNReal.measurable_ofReal.comp
    (measurable_uncurry_gaussianPDFReal.comp
      ((measurable_const.mul measurable_fst).prodMk
        ((measurable_const.mul measurable_fst.real_toNNReal).prodMk measurable_snd)))

/-! ## Integrability of the dominating function -/

/-- The weight `occWeight σ μ` is integrable on `(0, ∞)`: this is the Gamma integral
`∫_0^∞ m^{-1/2} e^{-c m} dm` with `c = μ²/(2σ²) > 0` (`integrableOn_rpow_mul_exp_neg_mul_rpow`). -/
theorem integrableOn_occWeight (hσ : 0 < σ) (hμ : 0 < μ) :
    IntegrableOn (occWeight σ μ) (Ioi 0) := by
  have hc : (0 : ℝ) < μ ^ 2 / (2 * σ ^ 2) := by positivity
  have h : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)
      * Real.exp (-(μ ^ 2 / (2 * σ ^ 2)) * x)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ))
        (b := μ ^ 2 / (2 * σ ^ 2)) (by norm_num) one_pos hc
  exact h

/-- The dominating function of `gaussianPDFReal_le_occBound` is integrable on `(0, ∞)`. -/
theorem integrable_occBound (hσ : 0 < σ) (hμ : 0 < μ) (K : ℝ) :
    Integrable (fun m => occConst σ μ K * occWeight σ μ m) (volume.restrict (Ioi 0)) :=
  (integrableOn_occWeight hσ hμ).const_mul _

/-- For `σ, μ > 0` the integrand of `occDens σ μ` is integrable on `(0, ∞)`: domination by
`integrable_occBound` and the Gaussian bound `gaussianPDFReal_le_occBound`. -/
theorem integrable_occDens_integrand (hσ : 0 < σ) (hμ : 0 < μ) (y : ℝ) :
    Integrable (fun m : ℝ => gaussianPDFReal (μ * m) (occVar σ m) y)
      (volume.restrict (Ioi 0)) := by
  refine (integrable_occBound hσ hμ |y|).mono'
    (measurable_occDens_integrand σ μ y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
  rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact gaussianPDFReal_le_occBound hσ hμ |y| y m le_rfl hm

/-! ## Continuity of the density -/

/-- A single Gaussian density is continuous, for any variance. -/
theorem continuous_gaussianPDFReal_apply (ν : ℝ) (v : ℝ≥0) :
    Continuous fun y : ℝ => gaussianPDFReal ν v y := by
  rw [gaussianPDFReal_def]
  dsimp only
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact (((continuous_id.sub continuous_const).pow 2).neg).div_const _

/-- **W3.** For `σ, μ > 0` the occupation density is continuous. -/
theorem continuous_occDens (hσ : 0 < σ) (hμ : 0 < μ) : Continuous (occDens σ μ) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  refine tendsto_integral_filter_of_dominated_convergence
    (fun m => occConst σ μ (|y₀| + 1) * occWeight σ μ m) ?_ ?_
    (integrable_occBound hσ hμ _) ?_
  · filter_upwards with y
    exact (measurable_occDens_integrand σ μ y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds y₀ zero_lt_one] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    refine gaussianPDFReal_le_occBound hσ hμ _ y m ?_ hm
    rw [Metric.mem_ball, Real.dist_eq] at hy
    calc |y| = |(y - y₀) + y₀| := by rw [sub_add_cancel]
      _ ≤ |y - y₀| + |y₀| := abs_add_le _ _
      _ ≤ 1 + |y₀| := by linarith
      _ = |y₀| + 1 := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with m _
    exact (continuous_gaussianPDFReal_apply _ _).continuousAt

/-! ## The occupation measure is the mixture of the densities -/

/-- **W3.** The occupation measure has density `occDens σ μ` (for `σ, μ > 0`; see the module
docstring for why both hypotheses are needed). -/
theorem occ_eq (hσ : 0 < σ) (hμ : 0 < μ) :
    occ σ μ = volume.withDensity fun y => ENNReal.ofReal (occDens σ μ y) := by
  refine Measure.ext fun A hA => ?_
  have hL : occ σ μ A = ∫⁻ m in Set.Ioi (0 : ℝ),
      ∫⁻ y in A, ENNReal.ofReal (gaussianPDFReal (μ * m) (occVar σ m) y) := by
    rw [occ_apply σ μ hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    -- the variance of `occ_apply` is `occVar σ m` in constructor form
    have hform : gaussianReal (μ * m) (⟨σ ^ 2, sq_nonneg σ⟩ * m.toNNReal) A
        = gaussianReal (μ * m) (occVar σ m) A := rfl
    exact hform.trans (by
      rw [gaussianReal_apply _ (occVar_ne_zero hm hσ.ne') A, gaussianPDF_def])
  have hR : (volume.withDensity fun y => ENNReal.ofReal (occDens σ μ y)) A = ∫⁻ y in A,
      ∫⁻ m in Set.Ioi (0 : ℝ), ENNReal.ofReal (gaussianPDFReal (μ * m) (occVar σ m) y) := by
    rw [withDensity_apply _ hA]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hA] with y _
    rw [occDens, ofReal_integral_eq_lintegral_ofReal (integrable_occDens_integrand hσ hμ y)
      (ae_of_all _ fun m => gaussianPDFReal_nonneg _ _ _)]
  rw [hL, hR]
  exact lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume.restrict A)
    (measurable_uncurry_occIntegrand σ μ).aemeasurable

/-! ## Expectation form of the occupation measure -/

/-- `GoodBM` forces `P` to be a probability measure (`b 0 = 0` a.s.). -/
theorem isProbabilityMeasure_of_goodBM (hb : GoodBM b P) : IsProbabilityMeasure P := by
  have h := hb.pre.hasLaw_eval 0
  rw [gaussianReal_zero_var] at h
  constructor
  have h2 : (P.map (b 0)) univ = P univ := by
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable MeasurableSet.univ, Set.preimage_univ]
  rw [← h2, h.map_eq]
  simp

/-- **Law of the one-dimensional marginal.** `dpath σ μ b · m` has law `gaussianReal (μ m) (σ² m)`:
it is `σ (b_m) + μ m`, and `b_m ~ N(0, m)`. -/
theorem hasLaw_dpath (hb : GoodBM b P) (σ μ : ℝ) {m : ℝ} (hm : 0 < m) :
    HasLaw (fun ω => dpath σ μ b ω m.toNNReal) (gaussianReal (μ * m) (occVar σ m)) P := by
  have h1 : HasLaw (fun ω => σ * b m.toNNReal ω) (gaussianReal (σ * 0) (occVar σ m)) P :=
    gaussianReal_const_mul (hb.pre.hasLaw_eval m.toNNReal) σ
  have h2 := gaussianReal_const_add h1 (μ * m)
  simp only [mul_zero, zero_add] at h2
  refine h2.congr ?_
  filter_upwards with ω
  simp only [dpath]
  rw [Real.coe_toNNReal _ hm.le]
  ring

/-- Joint measurability of the marginal, for the Tonelli step. -/
theorem measurable_uncurry_dpath_toNNReal (hb : GoodBM b P) (σ μ : ℝ) :
    Measurable fun p : ℝ × Ω => dpath σ μ b p.2 p.1.toNNReal := by
  have hb' : Measurable (Function.uncurry b) :=
    measurable_uncurry_of_continuous_of_measurable hb.cont hb.meas
  have h1 : Measurable fun p : ℝ × Ω => b p.1.toNNReal p.2 :=
    hb'.comp ((measurable_id.real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun p : ℝ × Ω => ((p.1.toNNReal : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.measurable.comp (measurable_id.real_toNNReal.comp measurable_fst)
  have h3 : Measurable fun p : ℝ × Ω => σ * b p.1.toNNReal p.2
      + μ * ((p.1.toNNReal : ℝ≥0) : ℝ) :=
    (h1.const_mul σ).add (h2.const_mul μ)
  simpa only [dpath] using h3

/-- **W3.** The defining property of the occupation measure: `occ σ μ A` is the expected total time
spent by `dpath σ μ b` in `A`. No hypothesis on `σ, μ` is needed. -/
theorem occ_eq_lintegral (hb : GoodBM b P) (σ μ : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    occ σ μ A
      = ∫⁻ ω, ∫⁻ m in Set.Ioi (0 : ℝ), A.indicator 1 (dpath σ μ b ω m.toNNReal) ∂volume ∂P := by
  have hprob : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := P)
    (f := fun (m : ℝ) (ω : Ω) => A.indicator 1 (dpath σ μ b ω m.toNNReal))
    ((measurable_const.indicator hA).comp (measurable_uncurry_dpath_toNNReal hb σ μ)).aemeasurable
  rw [← hswap, occ_apply σ μ hA]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
  have hlaw := hasLaw_dpath hb σ μ hm
  have hform : gaussianReal (μ * m) (⟨σ ^ 2, sq_nonneg σ⟩ * m.toNNReal) A
      = gaussianReal (μ * m) (occVar σ m) A := rfl
  exact hform.trans (by
    rw [hlaw.lintegral_comp (f := A.indicator (1 : ℝ → ℝ≥0∞))
      (measurable_const.indicator hA).aemeasurable, lintegral_indicator_one hA])

end QuantumZipper.Williams
