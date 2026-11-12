/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.GaussKernel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Occupation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The classical Gaussian kernel identity behind `occDens_nonneg_const`

Node W3 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). `occDens_nonneg_const` states that the
occupation density `occDens σ μ` of the drift Brownian motion is constant on `[0, ∞)`; unlike the
statement `prob_hit_neg`, it carries no `GoodBM b P`, so the blueprint's strong-Markov proof at
`τ_x` is not available for it and the remaining content is the classical Gaussian identity

`∫_0^∞ m^{-1/2} e^{-a/m - b m} dm = √(π/b) e^{-2√(a b)}`  (`a, b > 0`),

equivalently (the `K_{1/2}` Bessel / heat-kernel formula)

`∫_0^∞ e^{-a (u - 1/u)²} du = √(π/a)/2`  and  `∫_0^∞ e^{-a u²} du = √(π/a)/2`.

This file proves it and evaluates the density. `two_mul_lintegral_exp_neg_mul_sq_sub_inv` is the
identity in the form `2 ∫_0^∞ e^{-a(u-1/u)²} du = √(π/a)`, proved with the one-dimensional Jacobian
substitution `lintegral_image_eq_lintegral_deriv_mul_of_{monotone,antitone}On`
(`Mathlib/MeasureTheory/Function/JacobianOneDim.lean`):

* `u ↦ 1/u` is an antitone self-map of `(0, ∞)` with `|f'| = u⁻²` and `1/u - u = -(u - 1/u)`, so
  `∫ f = ∫ f/u²` (`hsub_inv`);
* `u ↦ u - 1/u` is monotone with image `ℝ` and derivative `1 + 1/u²`, so the full-line Gaussian
  integral is `∫ f (1 + 1/u²)` (`hsub_sub`);
* adding the two copies gives `2 ∫ f = ∫_ℝ e^{-a w²} dw = √(π/a)` (`integral_gaussian`).

Then `m = (y/μ) u²` (`image_mul_sq_Ioi`, `pointwise_mul_sq`) turns the density integral at a
positive level into a constant times `∫_0^∞ e^{-a(u-1/u)²} du` with `a = yμ/(2σ²)`, and the
arithmetic closes: `occDens_eq_inv_mu` gives `occDens σ μ y = 1/μ` for `y > 0`, whence
`occDens_zero_eq_inv_mu` extends it to `y = 0` by continuity (`continuous_occDens`).

Sources: the identity is the classical Bessel `K_{1/2}` / Gaussian integral (it is the analytic
form of the first-passage decomposition used by Revuz–Yor, *Continuous Martingales and Brownian
Motion*, 3rd ed., Ch. VI §1 — local time and occupation densities; the hitting probabilities of
the decomposition are Ch. VII Prop 3.2, printed pp. 301–302); it is not stated in `literature/`,
so the proof here is an
**own elementary proof** (substitution and the standard Gaussian integral, both in mathlib).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantumZipper.Williams

/-- `u ↦ 1/u` maps `(0,∞)` onto itself. -/
theorem inv_image_Ioi : (fun u : ℝ => u⁻¹) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext v
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact inv_pos.mpr hu
  · intro hv
    exact ⟨v⁻¹, inv_pos.mpr hv, inv_inv v⟩

/-- `u ↦ u - 1/u` maps `(0,∞)` onto `ℝ`. -/
theorem sub_inv_image_Ioi : (fun u : ℝ => u - u⁻¹) '' Set.Ioi 0 = Set.univ := by
  refine Set.eq_univ_of_forall fun w => ?_
  set s : ℝ := Real.sqrt (w ^ 2 + 4) with hs
  have h4 : (0 : ℝ) < w ^ 2 + 4 := by positivity
  have hs2 : s ^ 2 = w ^ 2 + 4 := by rw [hs]; exact Real.sq_sqrt h4.le
  have hlt : -w < s := by
    have h1 : |w| < s := by
      rw [hs, Real.lt_sqrt (abs_nonneg w), sq_abs]
      linarith
    linarith [neg_le_abs w]
  have hpos : 0 < (w + s) / 2 := by linarith
  refine ⟨(w + s) / 2, hpos, ?_⟩
  have hne : (w + s) ≠ 0 := by linarith
  have hkey : (2 : ℝ) / (w + s) = (s - w) / 2 := by
    rw [div_eq_div_iff hne (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith [hs2]
  change (w + s) / 2 - ((w + s) / 2)⁻¹ = w
  rw [inv_div, hkey]
  ring

/-- `u ↦ u - 1/u` is monotone on `(0, ∞)`. -/
theorem monotoneOn_sub_inv : MonotoneOn (fun u : ℝ => u - u⁻¹) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h1 : x - y ≤ 0 := by linarith
  have h2 : 0 ≤ x⁻¹ - y⁻¹ := by
    have h := one_div_le_one_div_of_le hx hxy
    rw [one_div, one_div] at h
    linarith
  linarith

/-- The classical identity, in the form used for `occDens_nonneg_const`:
`2 * ∫_0^∞ e^{-a (u - 1/u)²} du = √(π/a)` for `a > 0`. -/
theorem two_mul_lintegral_exp_neg_mul_sq_sub_inv {a : ℝ} (ha : 0 < a) :
    2 * (∫⁻ u in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(a * (u - u⁻¹) ^ 2))))
      = ENNReal.ofReal (Real.sqrt (Real.pi / a)) := by
  set F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(a * (u - u⁻¹) ^ 2))) with hF
  have hFm : Measurable F := by
    rw [hF]
    measurability
  -- (A) the antitone substitution `u ↦ 1/u` on `(0, ∞)`
  have hsub_inv : (∫⁻ u in Set.Ioi (0 : ℝ), F u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal ((u ^ 2)⁻¹) * F u := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun u : ℝ => u⁻¹) (-(x ^ 2)⁻¹) (Set.Ioi 0) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
    have hanti : AntitoneOn (fun u : ℝ => u⁻¹) (Set.Ioi 0) := by
      intro x hx y hy hxy
      have h := one_div_le_one_div_of_le hx hxy
      rw [one_div, one_div] at h
      exact h
    have h := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := Set.Ioi (0 : ℝ)) (f := fun u : ℝ => u⁻¹)
      (f' := fun u : ℝ => -(u ^ 2)⁻¹) measurableSet_Ioi hderiv hanti F
    rw [inv_image_Ioi] at h
    refine h.trans (setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
    have hsq : (x⁻¹ - (x⁻¹)⁻¹) ^ 2 = (x - x⁻¹) ^ 2 := by
      rw [inv_inv]
      ring
    simp only [hF, neg_neg, hsq]
  -- (B) the monotone substitution `u ↦ u - 1/u`, whose image is all of `ℝ`
  have hsub_sub : (∫⁻ w : ℝ, ENNReal.ofReal (Real.exp (-(a * w ^ 2))))
      = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 + (u ^ 2)⁻¹) * F u := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun u : ℝ => u - u⁻¹) (1 + (x ^ 2)⁻¹) (Set.Ioi 0) x := by
      intro x hx
      have h1 : HasDerivAt (fun u : ℝ => u - u⁻¹) (1 - -(x ^ 2)⁻¹) x :=
        (hasDerivAt_id x).sub (hasDerivAt_inv (ne_of_gt hx))
      have h2 : (1 : ℝ) - -(x ^ 2)⁻¹ = 1 + (x ^ 2)⁻¹ := by ring
      rw [h2] at h1
      exact h1.hasDerivWithinAt
    have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (s := Set.Ioi (0 : ℝ)) (f := fun u : ℝ => u - u⁻¹)
      (f' := fun u : ℝ => 1 + (u ^ 2)⁻¹) measurableSet_Ioi hderiv monotoneOn_sub_inv
      (fun w => ENNReal.ofReal (Real.exp (-(a * w ^ 2))))
    rw [sub_inv_image_Ioi, Measure.restrict_univ] at h
    refine h.trans (setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
    simp only [hF]
  -- (C) the Gaussian value
  have hgauss : (∫⁻ w : ℝ, ENNReal.ofReal (Real.exp (-(a * w ^ 2))))
      = ENNReal.ofReal (Real.sqrt (Real.pi / a)) := by
    have hint : Integrable fun w : ℝ => Real.exp (-(a * w ^ 2)) := by
      simpa only [neg_mul] using integrable_exp_neg_mul_sq ha
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun w => (Real.exp_pos _).le)]
    congr 1
    simpa only [neg_mul] using integral_gaussian a
  -- (D) split the weighted integral: `(1 + 1/u²) · F = F + 1/u² · F`
  have hsplit : (∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 + (u ^ 2)⁻¹) * F u)
      = (∫⁻ u in Set.Ioi (0 : ℝ), F u)
        + ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal ((u ^ 2)⁻¹) * F u := by
    rw [← lintegral_add_left (μ := volume.restrict (Set.Ioi (0 : ℝ))) (f := F) hFm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, add_mul, one_mul]
  rw [two_mul]
  nth_rw 2 [hsub_inv]
  rw [← hsplit, ← hsub_sub]
  exact hgauss

/-- The substitution `m = c u²` (`c > 0`) maps `(0, ∞)` onto itself. -/
theorem image_mul_sq_Ioi {c : ℝ} (hc : 0 < c) :
    (fun u : ℝ => c * u ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
  ext v
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact mul_pos hc (pow_pos hu 2)
  · intro hv
    refine ⟨Real.sqrt (v / c), Real.sqrt_pos.2 (div_pos hv hc), ?_⟩
    rw [Real.sq_sqrt (div_pos hv hc).le]
    field_simp

/-- The pointwise form of the substitution `m = c u²` for the drifted Gaussian density. -/
theorem pointwise_mul_sq {σ μ y u : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) (hy : 0 < y) (hu : 0 < u) :
    2 * (y / μ) * u * ((Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ * u ^ 2))))⁻¹
        * Real.exp (-(y - μ * (y / μ * u ^ 2)) ^ 2 / (2 * (σ ^ 2 * (y / μ * u ^ 2)))))
      = (2 * (y / μ) * (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))))⁻¹)
        * Real.exp (-(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2)) := by
  have h1 : 2 * Real.pi * (σ ^ 2 * (y / μ * u ^ 2))
      = (2 * Real.pi * (σ ^ 2 * (y / μ))) * u ^ 2 := by ring
  have hD : 0 < 2 * Real.pi * (σ ^ 2 * (y / μ)) := by positivity
  have hs : Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ * u ^ 2)))
      = Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))) * u := by
    rw [h1, Real.sqrt_mul hD.le, Real.sqrt_sq hu.le]
  have he : -(y - μ * (y / μ * u ^ 2)) ^ 2 / (2 * (σ ^ 2 * (y / μ * u ^ 2)))
      = -(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2) := by
    field_simp
    ring
  have hkey : u * (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))) * u)⁻¹
      = (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))))⁻¹ := by
    rw [mul_inv,
      show u * ((Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))))⁻¹ * u⁻¹)
        = (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))))⁻¹ * (u * u⁻¹) by ring,
      mul_inv_cancel₀ (ne_of_gt hu), mul_one]
  rw [hs, he,
    show 2 * (y / μ) * u * ((Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))) * u)⁻¹
        * Real.exp (-(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2)))
      = (2 * (y / μ)) * (u * (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))) * u)⁻¹)
        * Real.exp (-(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2)) by ring,
    hkey]

/-- The occupation density at a positive level, for positive drift: the density is `1/μ`. This is
the classical Gaussian integral `∫_0^∞ m^{-1/2} e^{-a/m-bm} dm = √(π/b) e^{-2√(ab)}`, reached here
through the substitution `m = (y/μ) u²`, which reduces it to
`two_mul_lintegral_exp_neg_mul_sq_sub_inv`. -/
theorem occDens_eq_inv_mu {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) {y : ℝ} (hy : 0 < y) :
    occDens σ μ y = 1 / μ := by
  have hc : 0 < y / μ := div_pos hy hμ
  have ha : 0 < y * μ / (2 * σ ^ 2) := by positivity
  set ψ : ℝ → ℝ := fun m => (Real.sqrt (2 * Real.pi * (σ ^ 2 * m)))⁻¹
    * Real.exp (-(y - μ * m) ^ 2 / (2 * (σ ^ 2 * m))) with hψ
  have hnn : ∀ m : ℝ, 0 ≤ ψ m := fun m =>
    mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hmeas : Measurable ψ := by
    rw [hψ]
    measurability
  -- the density is the integral of `ψ`
  have h1 : occDens σ μ y = ∫ m in Set.Ioi (0 : ℝ), ψ m := by
    refine integral_congr_ae (μ := volume.restrict (Set.Ioi (0 : ℝ))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
    rw [hψ]
    exact gaussianPDFReal_occVar_eq σ μ hm.le y
  have h2 := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ae_of_all _ hnn) hmeas.aestronglyMeasurable
  rw [h1, h2]
  -- the substitution `m = (y/μ) u²`
  have hsub : (∫⁻ m in Set.Ioi (0 : ℝ), ENNReal.ofReal (ψ m))
      = ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * (y / μ) * u)
        * ENNReal.ofReal (ψ ((y / μ) * u ^ 2)) := by
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun u : ℝ => (y / μ) * u ^ 2) (2 * (y / μ) * x) (Set.Ioi 0) x := by
      intro x hx
      have h : HasDerivAt (fun u : ℝ => (y / μ) * u ^ 2) (2 * (y / μ) * x) x := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (hasDerivAt_pow 2 x).const_mul (y / μ)
      exact h.hasDerivWithinAt
    have hmono : MonotoneOn (fun u : ℝ => (y / μ) * u ^ 2) (Set.Ioi 0) := by
      intro a ha b hb hab
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab 2) hc.le
    have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
      (s := Set.Ioi (0 : ℝ)) (f := fun u : ℝ => (y / μ) * u ^ 2)
      (f' := fun u : ℝ => 2 * (y / μ) * u) measurableSet_Ioi hderiv hmono
      (fun m => ENNReal.ofReal (ψ m))
    rw [image_mul_sq_Ioi hc] at h
    exact h
  rw [hsub]
  -- pull out the constant and apply the core identity
  set K : ℝ := 2 * (y / μ) * (Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ))))⁻¹ with hK
  have hpoint : ∀ u ∈ Set.Ioi (0 : ℝ),
      ENNReal.ofReal (2 * (y / μ) * u) * ENNReal.ofReal (ψ ((y / μ) * u ^ 2))
        = ENNReal.ofReal K * ENNReal.ofReal (Real.exp (-(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2))) := by
    intro u hu
    have hu' : (0 : ℝ) < u := hu
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (y / μ) * u), hψ]
    rw [show 2 * (y / μ) * u * ((Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ * u ^ 2))))⁻¹
          * Real.exp (-(y - μ * (y / μ * u ^ 2)) ^ 2 / (2 * (σ ^ 2 * (y / μ * u ^ 2)))))
        = K * Real.exp (-(y * μ / (2 * σ ^ 2) * (u - u⁻¹) ^ 2)) from by
      rw [hK]
      exact pointwise_mul_sq hσ hμ hy hu']
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K)]
  rw [setLIntegral_congr_fun (μ := volume) measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _ (by finiteness)]
  have hcore := two_mul_lintegral_exp_neg_mul_sq_sub_inv ha
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ K)]
  have hY : (∫⁻ a in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(y * μ / (2 * σ ^ 2) * (a - a⁻¹) ^ 2)))).toReal
      = Real.sqrt (Real.pi / (y * μ / (2 * σ ^ 2))) / 2 := by
    have hc2 := congrArg ENNReal.toReal hcore
    rw [ENNReal.toReal_mul] at hc2
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at hc2
    rw [ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ Real.sqrt (Real.pi / (y * μ / (2 * σ ^ 2))))] at hc2
    linarith
  rw [hY]
  -- arithmetic: `K * (√(π/a)) / 2 = 1/μ`
  have hKval : K * (Real.sqrt (Real.pi / (y * μ / (2 * σ ^ 2))) / 2) = 1 / μ := by
    rw [hK]
    have harg : Real.pi / (y * μ / (2 * σ ^ 2)) = Real.pi * (2 * σ ^ 2) / (y * μ) := by
      field_simp
    rw [harg]
    have hsplit : Real.sqrt (Real.pi * (2 * σ ^ 2) / (y * μ))
        = Real.sqrt (Real.pi * (2 * σ ^ 2)) / Real.sqrt (y * μ) :=
      Real.sqrt_div (by positivity : (0 : ℝ) ≤ Real.pi * (2 * σ ^ 2)) (y * μ)
    rw [hsplit]
    have hD : 0 < 2 * Real.pi * (σ ^ 2 * (y / μ)) := by positivity
    have hD' : 0 < Real.pi * (2 * σ ^ 2) := by positivity
    rw [show Real.sqrt (2 * Real.pi * (σ ^ 2 * (y / μ)))
        = Real.sqrt (Real.pi * (2 * σ ^ 2)) * Real.sqrt (y / μ) by
      rw [show 2 * Real.pi * (σ ^ 2 * (y / μ)) = (Real.pi * (2 * σ ^ 2)) * (y / μ) by ring,
        Real.sqrt_mul hD'.le]]
    rw [mul_inv]
    field_simp
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ y / μ)]
    rw [show y / μ * (y * μ) = y ^ 2 by field_simp, Real.sqrt_sq hy.le]
  rw [hKval]

theorem occDens_zero_eq_inv_mu {σ μ : ℝ} (hσ : 0 < σ) (hμ : 0 < μ) :
    occDens σ μ 0 = 1 / μ := by
  have hcont : Continuous (occDens σ μ) := continuous_occDens hσ hμ
  have h1 : Tendsto (occDens σ μ) (𝓝[>] (0 : ℝ)) (𝓝 (occDens σ μ 0)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (occDens σ μ) (𝓝[>] (0 : ℝ)) (𝓝 (1 / μ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (occDens_eq_inv_mu hσ hμ hy).symm
  exact tendsto_nhds_unique h1 h2

end QuantumZipper.Williams
