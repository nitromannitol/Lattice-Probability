import Mathlib
import LatticeProb.LQG.LQGNegRec
import LatticeProb.LQG.LQGCircleMoments
import LatticeProb.Prob.GaussianLaw
import LatticeProb.Gauss.TruncatedExpMoment

/-!
# The lognormal weights of the two dyadic sub-squares

`subSquareLognormal γ hcirc k a s = e^{γ g - γ²/2} R^{2+γ²/2} e^{γ h_R(z_s)}` (`R = 2^{-k}`,
`a = (field, g)`) is the weight by which the `s`-th dyadic sub-square of the square
`[-1/8, 1/8]²` enters the recursion for the Laplace transform of the mass of the square.  Its
logarithm is `X_s - u₀` with `X_s = γ (g + h_R(z_s))` centred Gaussian of variance
`σ² = γ² (1 + k log 2)` and `u₀ = γ²/2 + (2 + γ²/2) k log 2`.

* `integrable_prod_rpow_neg_subSquareLognormal`: all negative moments of `∏_s W_s` are finite.
* `measureReal_exists_subSquareLognormal_lt_le`: `P(∃ s, W_s < e^{-u}) ≤ 2 exp (-(u-u₀)²/(2σ²))`
  for `u ≥ u₀`.
* `integral_comp_subSquareLognormal_eq`: expectations of measurable functions of
  `(W_0, W_1)` do not depend on the model of the whole-plane GFF.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

open LatticeProb LatticeProb.LQG LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

theorem log_dyadicScale_eq (k : ℕ) : Real.log (dyadicScale k) = -(k * Real.log 2) := by
  unfold dyadicScale
  rw [Real.log_pow, Real.log_inv]
  ring

/-- The variance `σ² = γ² (1 + k log 2)` of `γ (g + h_R(z_s))`, `R = 2^{-k}`. -/
def lognormalVariance (γ : ℝ) (k : ℕ) : ℝ := γ ^ 2 * (1 + k * Real.log 2)

/-- The shift `u₀ = γ²/2 + (2 + γ²/2) k log 2` between `log W_s` and `-γ (g + h_R(z_s))`. -/
def lognormalShift (γ : ℝ) (k : ℕ) : ℝ := γ ^ 2 / 2 + (2 + γ ^ 2 / 2) * (k * Real.log 2)

theorem lognormalVariance_pos {γ : ℝ} (hγ : γ ≠ 0) (k : ℕ) : 0 < lognormalVariance γ k := by
  have h2 : 0 < γ ^ 2 := by positivity
  have h3 := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  unfold lognormalVariance
  positivity

theorem lognormalShift_nonneg (γ : ℝ) (k : ℕ) : 0 ≤ lognormalShift γ k := by
  have h3 := Real.log_pos (one_lt_two : (1 : ℝ) < 2)
  unfold lognormalShift
  positivity

omit [MeasurableSpace Ω] in
theorem log_subSquareLognormal (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (a : Ω × ℝ) (s : Fin 2) :
    Real.log (subSquareLognormal γ hcirc k a s) =
      γ * a.2 + γ * hcirc a.1 (dyadicScale k) (lqgSquareCentre s) - lognormalShift γ k := by
  have hR := dyadicScale_pos' k
  unfold subSquareLognormal lognormalShift
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hR _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hR _).ne', Real.log_exp, Real.log_exp,
    Real.log_rpow hR, log_dyadicScale_eq]
  ring

/-- `γ (g + h_R(z_s))` has the Gaussian exponential moments of a centred Gaussian of variance
`σ²`: `E exp (b γ (g + h_R(z_s))) = exp (b² σ² / 2)`. -/
theorem IsWholePlaneGFF.integral_exp_mul_lognormal (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) (s : Fin 2) (b : ℝ) :
    ∫ a : Ω × ℝ, Real.exp (b * (γ * a.2 + γ * hcirc a.1 (dyadicScale k) (lqgSquareCentre s)))
        ∂(P.prod (gaussianReal 0 1)) = Real.exp (b ^ 2 * lognormalVariance γ k / 2) := by
  have hP := hh.isProbabilityMeasure
  have hR := dyadicScale_pos' k
  have hz := norm_lqgSquareCentre_add_dyadicScale_le_one hk s
  have hfun : ∀ a : Ω × ℝ, Real.exp (b * (γ * a.2 + γ *
      hcirc a.1 (dyadicScale k) (lqgSquareCentre s))) =
      Real.exp ((b * γ) * hcirc a.1 (dyadicScale k) (lqgSquareCentre s)) *
        Real.exp ((b * γ) * a.2) := fun a => by
    rw [← Real.exp_add]; congr 1; ring
  have hfield : ∫ ω, Real.exp ((b * γ) * hcirc ω (dyadicScale k) (lqgSquareCentre s)) ∂P =
      Real.exp ((b * γ) ^ 2 * (-Real.log (dyadicScale k)) / 2) := by
    have h := hh.integral_exp_sum_circle hR (fun _ : Fin 1 => lqgSquareCentre s) (fun _ => b * γ)
    have hcov : cov[fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre s),
        fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre s); P] = -Real.log (dyadicScale k) := by
      rw [hh.covariance_circle_inside hR hR hz hz, circlePairPotential_self_center hR.le, max_self]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, hcov] at h
    rw [h]
    congr 1
    ring
  have hgauss : ∫ x : ℝ, Real.exp ((b * γ) * x) ∂(gaussianReal 0 1) = Real.exp ((b * γ) ^ 2 / 2) := by
    have := LatticeProb.GaussTail.integral_exp_mul_gaussianReal_zero 1 (b * γ)
    simpa using this
  calc _ = ∫ a : Ω × ℝ, Real.exp ((b * γ) * hcirc a.1 (dyadicScale k) (lqgSquareCentre s)) *
        Real.exp ((b * γ) * a.2) ∂(P.prod (gaussianReal 0 1)) :=
        integral_congr_ae (Filter.Eventually.of_forall hfun)
    _ = _ := by
      rw [integral_prod_mul (fun ω => Real.exp ((b * γ) * hcirc ω (dyadicScale k)
        (lqgSquareCentre s))) (fun x : ℝ => Real.exp ((b * γ) * x)), hfield, hgauss,
        ← Real.exp_add, log_dyadicScale_eq]
      congr 1
      unfold lognormalVariance
      ring

theorem IsWholePlaneGFF.integrable_exp_mul_lognormal (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (k : ℕ) (s : Fin 2) (b : ℝ) :
    Integrable (fun a : Ω × ℝ => Real.exp (b * (γ * a.2 +
      γ * hcirc a.1 (dyadicScale k) (lqgSquareCentre s)))) (P.prod (gaussianReal 0 1)) := by
  have hP := hh.isProbabilityMeasure
  have hR := dyadicScale_pos' k
  have hf : Integrable (fun ω => Real.exp ((b * γ) * hcirc ω (dyadicScale k)
      (lqgSquareCentre s))) P := by
    have := hh.integrable_exp_sum_circle hR (fun _ : Fin 1 => lqgSquareCentre s) (fun _ => b * γ)
    simpa using this
  have hg : Integrable (fun x : ℝ => Real.exp ((b * γ) * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal (b * γ)
  refine (hf.mul_prod hg).congr (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Chernoff bound for one sub-square.** For `u ≥ u₀`, `P(W_s < e^{-u}) ≤ exp (-(u-u₀)²/(2σ²))`. -/
theorem IsWholePlaneGFF.measureReal_subSquareLognormal_lt_le (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) {k : ℕ} (hk : 4 ≤ k) (s : Fin 2) {u : ℝ} (hu : lognormalShift γ k ≤ u) :
    (P.prod (gaussianReal 0 1)).real {a | subSquareLognormal γ hcirc k a s < Real.exp (-u)} ≤
      Real.exp (-((1 / (2 * lognormalVariance γ k)) * (u - lognormalShift γ k) ^ 2)) := by
  have hP := hh.isProbabilityMeasure
  have hσ := lognormalVariance_pos hγ k
  set σ2 := lognormalVariance γ k with hσ2
  set u0 := lognormalShift γ k with hu0
  set τ := u - u0 with hτ
  have hτ0 : 0 ≤ τ := sub_nonneg.2 hu
  set X : Ω × ℝ → ℝ := fun a => γ * a.2 + γ * hcirc a.1 (dyadicScale k) (lqgSquareCentre s) with hX
  have hsub : {a : Ω × ℝ | subSquareLognormal γ hcirc k a s < Real.exp (-u)} ⊆
      {a | X a ≤ -τ} := by
    intro a ha
    have h1 := (Real.log_lt_iff_lt_exp (subSquareLognormal_pos γ hcirc k a s)).2 ha
    rw [log_subSquareLognormal] at h1
    show X a ≤ -τ
    simp only [hX, hτ]
    linarith
  have ht : -(τ / σ2) ≤ 0 := by
    have : 0 ≤ τ / σ2 := div_nonneg hτ0 hσ.le
    linarith
  have hint := hh.integrable_exp_mul_lognormal γ k s (-(τ / σ2))
  have hch := measure_le_le_exp_mul_mgf (μ := P.prod (gaussianReal 0 1)) (X := X) (-τ) ht hint
  have hmgf : mgf X (P.prod (gaussianReal 0 1)) (-(τ / σ2)) =
      Real.exp (τ ^ 2 / σ2 ^ 2 * σ2 / 2) := by
    have := hh.integral_exp_mul_lognormal γ hk s (-(τ / σ2))
    rw [← hσ2] at this
    have e : (-(τ / σ2)) ^ 2 * σ2 / 2 = τ ^ 2 / σ2 ^ 2 * σ2 / 2 := by ring
    rw [e] at this
    exact this
  refine le_trans (measureReal_mono hsub) (le_trans hch ?_)
  rw [hmgf, ← Real.exp_add]
  refine Real.exp_le_exp.2 (le_of_eq ?_)
  field_simp
  ring

/-- **Tail of the minimum of the weights.** For `u ≥ u₀`,
`P(∃ s, W_s < e^{-u}) ≤ 2 exp (-(u-u₀)²/(2σ²))`. -/
theorem IsWholePlaneGFF.measureReal_exists_subSquareLognormal_lt_le
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : γ ≠ 0) {k : ℕ} (hk : 4 ≤ k) {u : ℝ}
    (hu : lognormalShift γ k ≤ u) :
    (P.prod (gaussianReal 0 1)).real {a | ∃ s : Fin 2, subSquareLognormal γ hcirc k a s <
        Real.exp (-u)} ≤
      2 * Real.exp (-((1 / (2 * lognormalVariance γ k)) * (u - lognormalShift γ k) ^ 2)) := by
  have hP := hh.isProbabilityMeasure
  have hset : {a : Ω × ℝ | ∃ s : Fin 2, subSquareLognormal γ hcirc k a s < Real.exp (-u)} =
      {a | subSquareLognormal γ hcirc k a 0 < Real.exp (-u)} ∪
        {a | subSquareLognormal γ hcirc k a 1 < Real.exp (-u)} := by
    ext a
    simp [Fin.exists_fin_two]
  rw [hset]
  refine le_trans (measureReal_union_le _ _) ?_
  have h0 := hh.measureReal_subSquareLognormal_lt_le hγ hk 0 hu
  have h1 := hh.measureReal_subSquareLognormal_lt_le hγ hk 1 hu
  linarith

/-- **Negative moments of the product of the weights.** For every `a`, `∏_s W_s^{-a}` is
integrable. -/
theorem IsWholePlaneGFF.integrable_prod_rpow_neg_subSquareLognormal
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) (k : ℕ) (a : ℝ) :
    Integrable (fun x : Ω × ℝ => ∏ s : Fin 2, subSquareLognormal γ hcirc k x s ^ (-a))
      (P.prod (gaussianReal 0 1)) := by
  have hP := hh.isProbabilityMeasure
  have hR := dyadicScale_pos' k
  have hf : Integrable (fun ω => Real.exp (∑ s : Fin 2, (-(a * γ)) *
      hcirc ω (dyadicScale k) (lqgSquareCentre s))) P :=
    hh.integrable_exp_sum_circle hR (fun s : Fin 2 => lqgSquareCentre s) (fun _ => -(a * γ))
  have hg : Integrable (fun x : ℝ => Real.exp ((-(2 * a * γ)) * x)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal (-(2 * a * γ))
  refine ((hf.mul_prod hg).const_mul (Real.exp (2 * a * lognormalShift γ k))).congr
    (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  have h1 : ∀ s : Fin 2, subSquareLognormal γ hcirc k x s ^ (-a) = Real.exp ((γ * x.2 +
      γ * hcirc x.1 (dyadicScale k) (lqgSquareCentre s) - lognormalShift γ k) * (-a)) := fun s => by
    rw [Real.rpow_def_of_pos (subSquareLognormal_pos γ hcirc k x s), log_subSquareLognormal]
  simp only [h1, Fin.prod_univ_two, Fin.sum_univ_two, ← Real.exp_add]
  congr 1
  ring

/-! ### The law of the weights does not depend on the model -/

section Models

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {hC' : Ω' → (ℂ → ℝ) → ℝ}
  {hcirc' : Ω' → ℝ → ℂ → ℝ}

theorem IsWholePlaneGFF.integral_circle_mul (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∫ ω, hcirc ω r z * hcirc ω s w ∂P = wholePlaneGFFCov (.circle r z) (.circle s w) := by
  have hP := hh.isProbabilityMeasure
  have h1 := hh.covariance_circle_circle hr hs z w
  rw [covariance_eq_sub (hh.memLp_two_circle hr z) (hh.memLp_two_circle hs w)] at h1
  have e1 := hh.integral_eq_zero (.circle r z) hr
  have e2 := hh.integral_eq_zero (.circle s w) hs
  simp only [GFFObservable.eval] at e1 e2
  simpa [e1, e2, Pi.mul_apply] using h1

/-- **The law of circle averages is the same in every model.** For two whole-plane GFFs (on
possibly different probability spaces), the joint laws of any finite family of circle averages
coincide. -/
theorem IsWholePlaneGFF.map_circleVector_eq (hh : IsWholePlaneGFF P hC hcirc)
    (hh' : IsWholePlaneGFF P' hC' hcirc') {ι : Type*} (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) :
    P.map (fun ω i => hcirc ω (r i) (z i)) = P'.map (fun ω i => hcirc' ω (r i) (z i)) := by
  have hP := hh.isProbabilityMeasure
  have hP' := hh'.isProbabilityMeasure
  let f : ι → GFFObservable.Admissible := fun i => ⟨.circle (r i) (z i), hr i⟩
  exact gaussian_law_eq_of_covariance Ω Ω' P P' (fun i ω => hcirc ω (r i) (z i))
    (fun i ω => hcirc' ω (r i) (z i)) (hh.isGaussianProcess.comp_right f)
    (hh'.isGaussianProcess.comp_right f) (fun i => hh.measurable_circle _ _ (hr i))
    (fun i => hh'.measurable_circle _ _ (hr i))
    (fun i => hh.integral_eq_zero (.circle (r i) (z i)) (hr i))
    (fun i => hh'.integral_eq_zero (.circle (r i) (z i)) (hr i))
    (fun i j => by
      rw [hh.integral_circle_mul (hr i) (hr j), hh'.integral_circle_mul (hr i) (hr j)])

/-- **Expectations of functions of the circle averages and a Gaussian.** -/
theorem IsWholePlaneGFF.integral_comp_circle_prod_eq (hh : IsWholePlaneGFF P hC hcirc)
    (hh' : IsWholePlaneGFF P' hC' hcirc') {R : ℝ} (hR : 0 < R) (z : Fin 2 → ℂ)
    (F : (Fin 2 → ℝ) × ℝ → ℝ) (hF : Measurable F) :
    ∫ a : Ω × ℝ, F (fun s => hcirc a.1 R (z s), a.2) ∂(P.prod (gaussianReal 0 1)) =
      ∫ a : Ω' × ℝ, F (fun s => hcirc' a.1 R (z s), a.2) ∂(P'.prod (gaussianReal 0 1)) := by
  have hP := hh.isProbabilityMeasure
  have hP' := hh'.isProbabilityMeasure
  have hv : Measurable fun ω => fun s : Fin 2 => hcirc ω R (z s) :=
    Measurable.of_eval fun s => hh.measurable_circle _ _ hR
  have hv' : Measurable fun ω => fun s : Fin 2 => hcirc' ω R (z s) :=
    Measurable.of_eval fun s => hh'.measurable_circle _ _ hR
  have hmap := hh.map_circleVector_eq hh' (fun _ : Fin 2 => R) z (fun _ => hR)
  have e1 : ∫ a : Ω × ℝ, F (fun s => hcirc a.1 R (z s), a.2) ∂(P.prod (gaussianReal 0 1)) =
      ∫ p, F p ∂((P.map fun ω => fun s : Fin 2 => hcirc ω R (z s)).prod (gaussianReal 0 1)) := by
    have := Measure.map_prod_map (μa := P) (μc := gaussianReal 0 1) hv measurable_id
    rw [Measure.map_id] at this
    rw [this, integral_map (by exact (hv.prodMap measurable_id).aemeasurable) hF.aestronglyMeasurable]
    rfl
  have e2 : ∫ a : Ω' × ℝ, F (fun s => hcirc' a.1 R (z s), a.2) ∂(P'.prod (gaussianReal 0 1)) =
      ∫ p, F p ∂((P'.map fun ω => fun s : Fin 2 => hcirc' ω R (z s)).prod (gaussianReal 0 1)) := by
    have := Measure.map_prod_map (μa := P') (μc := gaussianReal 0 1) hv' measurable_id
    rw [Measure.map_id] at this
    rw [this, integral_map (by exact (hv'.prodMap measurable_id).aemeasurable) hF.aestronglyMeasurable]
    rfl
  rw [e1, e2, hmap]

/-- **Model independence of the weights.** For a measurable `G` of the pair `(W_0, W_1)`, the
expectation `E G(W_0, W_1)` is the same in every model of the whole-plane GFF. -/
theorem IsWholePlaneGFF.integral_comp_subSquareLognormal_eq (hh : IsWholePlaneGFF P hC hcirc)
    (hh' : IsWholePlaneGFF P' hC' hcirc') (γ : ℝ) (k : ℕ) (G : (Fin 2 → ℝ) → ℝ)
    (hG : Measurable G) :
    ∫ a : Ω × ℝ, G (fun s => subSquareLognormal γ hcirc k a s) ∂(P.prod (gaussianReal 0 1)) =
      ∫ a : Ω' × ℝ, G (fun s => subSquareLognormal γ hcirc' k a s)
        ∂(P'.prod (gaussianReal 0 1)) := by
  have hF : Measurable fun p : (Fin 2 → ℝ) × ℝ => G (fun s => Real.exp (γ * p.2 - γ ^ 2 / 2) *
      dyadicScale k ^ (2 + γ ^ 2 / 2) * Real.exp (γ * p.1 s)) := by
    refine hG.comp (Measurable.of_eval fun s => ?_)
    exact ((Real.measurable_exp.comp ((measurable_const.mul measurable_snd).sub
      measurable_const)).mul measurable_const).mul (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_pi_apply s).comp measurable_fst)))
  exact hh.integral_comp_circle_prod_eq hh' (dyadicScale_pos' k) (fun s => lqgSquareCentre s)
    _ hF

end Models

end LatticeProb.Gauss
