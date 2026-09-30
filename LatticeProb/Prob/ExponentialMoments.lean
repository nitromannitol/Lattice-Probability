/-
Uniform weighted moments and small-ball masses for laws with an exponential
moment, and the matching moment/mass bounds for their centred Gaussian
counterparts of the same second moment.

Moved from Divisible-Sandpile-Percolation, `Sandpile/Support/ExponentialMoments.lean`.
The source file's own imports (`Sandpile.Support.FiniteLindeberg`,
`Sandpile.Support.SubExponential`) are used only for, respectively, the
`MatchingThirdMoments` predicate (used by the source file's last two lemmas,
`matchingThirdMoments_gaussian_of_exp` and
`exists_uniform_matching_gaussian_inputs`, which are left behind: that
predicate is a separate, unaudited cluster, not part of this one) and the
sub-Gaussian toolkit already in `LatticeProb.Prob.SubGaussian` (a verified
exact duplicate of `Sandpile.Support.SubExponential`). `integral_ge_of_nonneg_and_bound`
is copied in from `Sandpile.Support.StableIntegral`, which is Mathlib-only and
purely generic (a set integral is at least the measure of the set times a
uniform lower bound on it).
-/
import LatticeProb.Prob.SubGaussian

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace LatticeProb

/-- A set integral of a nonnegative function is at least the measure of the
set times a uniform lower bound on it. -/
theorem integral_ge_of_nonneg_and_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hfi : Integrable f μ)
    (hf : ∀ x, 0 ≤ f x) {s : Set Ω} (hs : MeasurableSet s) {b : ℝ}
    (hb : ∀ x ∈ s, b ≤ f x) : μ.real s * b ≤ ∫ x, f x ∂μ := by
  have h := setIntegral_ge_of_const_le hs (measure_ne_top μ s) hb hfi.integrableOn
  exact h.trans (setIntegral_le_integral hfi (Filter.Eventually.of_forall hf))

/-- `|x|^3 exp(κ|x|)` is dominated by `exp(θ|x|)` up to a constant, when
`κ ≤ θ/2`. -/
theorem weighted_cube_le_exp {θ κ : ℝ} (hθ : 0 < θ) (hκ : κ ≤ θ / 2) (x : ℝ) :
    |x| ^ 3 * Real.exp (κ * |x|) ≤ (48 / θ ^ 3) * Real.exp (θ * |x|) := by
  have hp := Real.pow_div_factorial_le_exp (θ / 2 * |x|) (mul_nonneg (by linarith : 0 ≤ θ / 2) (abs_nonneg x)) 3
  norm_num [mul_pow] at hp
  have hc : |x| ^ 3 ≤ (48 / θ ^ 3) * Real.exp (θ / 2 * |x|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hθ 3)]
    nlinarith
  calc
    _ ≤ ((48 / θ ^ 3) * Real.exp (θ / 2 * |x|)) * Real.exp (θ / 2 * |x|) :=
      mul_le_mul hc (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hκ (abs_nonneg x)))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The weighted cube is integrable whenever the exponential moment is. -/
theorem integrable_weighted_cube_of_exp {μ : Measure ℝ} {θ κ : ℝ}
    (hθ : 0 < θ) (hκ : κ ≤ θ / 2)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ) :
    Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) μ := by
  apply (hexp.const_mul (48 / θ ^ 3)).mono'
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) μ)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x| ^ 3 * Real.exp (κ * |x|))]
  exact weighted_cube_le_exp hθ hκ x

/-- A uniform bound on the exponential moment bounds the weighted cube's
integral. -/
theorem integral_weighted_cube_le_of_exp {μ : Measure ℝ} {θ κ K : ℝ}
    (hθ : 0 < θ) (hκ : κ ≤ θ / 2)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K) :
    (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂μ) ≤ (48 / θ ^ 3) * K := by
  calc
    _ ≤ ∫ x : ℝ, (48 / θ ^ 3) * Real.exp (θ * |x|) ∂μ :=
      integral_mono (integrable_weighted_cube_of_exp hθ hκ hexp) (hexp.const_mul _)
        (weighted_cube_le_exp hθ hκ)
    _ = (48 / θ ^ 3) * ∫ x : ℝ, Real.exp (θ * |x|) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)

/-- The first absolute moment is controlled by a uniform exponential-moment
bound. -/
theorem integral_abs_le_of_exp {μ : Measure ℝ} {θ K : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K) :
    (∫ x : ℝ, |x| ∂μ) ≤ K / θ := by
  have hid : Integrable (fun x : ℝ => x) μ := integrable_id_of_exp_moment μ θ hθ hexp
  calc
    _ ≤ ∫ x : ℝ, (1 / θ) * Real.exp (θ * |x|) ∂μ := by
      apply integral_mono hid.abs (hexp.const_mul _)
      intro x
      change |x| ≤ (1 / θ) * Real.exp (θ * |x|)
      rw [one_div_mul_eq_div, le_div_iff₀ hθ]
      linarith [Real.add_one_le_exp (θ * |x|)]
    _ = (1 / θ) * ∫ x : ℝ, Real.exp (θ * |x|) ∂μ := integral_const_mul _ _
    _ ≤ K / θ := by
      simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ 1 / θ)

/-- A first-moment bound of `R/2` puts at least half the mass in `[-R, R]`. -/
theorem small_ball_of_first_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) {R : ℝ} (hR : 0 < R)
    (hM : (∫ x : ℝ, |x| ∂μ) ≤ R / 2) :
    (1 / 2 : ℝ) ≤ μ.real (Icc (-R) R) := by
  have hbound : ∀ x ∈ (Icc (-R) R)ᶜ, R ≤ |x| := by
    intro x hx
    exact le_of_lt (lt_of_not_ge (fun h => hx (abs_le.mp h)))
  have hi := integral_ge_of_nonneg_and_bound hμ.abs abs_nonneg measurableSet_Icc.compl hbound
  have hs := measureReal_add_measureReal_compl (μ := μ) (s := Icc (-R) R) measurableSet_Icc
  rw [probReal_univ] at hs
  nlinarith

/-- A uniform exponential-moment bound puts at least half the mass of the law
in a window of radius `2K/θ`. -/
theorem small_ball_of_exp {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {θ K : ℝ} (hθ : 0 < θ) (hKpos : 0 < K)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K) :
    (1 / 2 : ℝ) ≤ μ.real (Icc (-(2 * K / θ)) (2 * K / θ)) := by
  apply small_ball_of_first_moment (integrable_id_of_exp_moment μ θ hθ hexp)
    (by positivity)
  convert integral_abs_le_of_exp hθ hexp hK using 1
  first | rfl | ring

/-- An exponential moment implies a second moment. -/
theorem integrable_sq_of_exp {μ : Measure ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ) :
    Integrable (fun x : ℝ => x ^ 2) μ := by
  apply (hexp.const_mul (4 / θ ^ 2)).mono' (by fun_prop)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using sq_le_exp_mul θ hθ |x| (abs_nonneg x)

/-- A uniform exponential-moment bound controls the second moment. -/
theorem integral_sq_le_of_exp {μ : Measure ℝ} {θ K : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K) :
    (∫ x : ℝ, x ^ 2 ∂μ) ≤ (4 / θ ^ 2) * K := by
  calc
    _ ≤ ∫ x : ℝ, (4 / θ ^ 2) * Real.exp (θ * |x|) ∂μ :=
      integral_mono (integrable_sq_of_exp hθ hexp) (hexp.const_mul _)
        (fun x => by simpa only [sq_abs] using sq_le_exp_mul θ hθ |x| (abs_nonneg x))
    _ = (4 / θ ^ 2) * ∫ x : ℝ, Real.exp (θ * |x|) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hK (by positivity)

/-- `exp(θ|x|) ≤ exp(θx) + exp(-θx)`. -/
theorem exp_abs_le_exp_add (θ x : ℝ) :
    Real.exp (θ * |x|) ≤ Real.exp (θ * x) + Real.exp (-θ * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-θ * x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have he : θ * -x = -θ * x := by ring
    rw [he]
    linarith [Real.exp_pos (θ * x)]

/-- A centred Gaussian has every exponential moment. -/
theorem integrable_exp_abs_gaussian (θ : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => Real.exp (θ * |x|)) (gaussianReal 0 v) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) θ).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-θ))).mono' (by fun_prop)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using exp_abs_le_exp_add θ x

/-- A closed form for the exponential moment of a centred Gaussian's absolute
value. -/
theorem integral_exp_abs_gaussian_le (θ : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, Real.exp (θ * |x|) ∂gaussianReal 0 v) ≤ 2 * Real.exp (v * θ ^ 2 / 2) := by
  have he (t : ℝ) : (∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 v) = Real.exp (v * t ^ 2 / 2) := by
    simpa only [mgf, id_eq, zero_mul, zero_add] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) t
  calc
    _ ≤ ∫ x : ℝ, Real.exp (θ * x) + Real.exp (-θ * x) ∂gaussianReal 0 v :=
      integral_mono (integrable_exp_abs_gaussian θ v)
        ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) θ).add
          (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-θ))) (exp_abs_le_exp_add θ)
    _ = _ := by
      rw [integral_add (integrable_exp_mul_gaussianReal θ) (integrable_exp_mul_gaussianReal (-θ)), he, he]
      simp only [neg_sq]
      ring

/-- The second moment of a centred Gaussian is its variance parameter. -/
theorem integral_sq_gaussian_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_eq_integral (μ := gaussianReal 0 v) (X := id) measurable_id.aemeasurable
  simp only [id_eq, integral_id_gaussianReal, sub_zero] at h
  exact h.symm.trans variance_id_gaussianReal

/-- If the variance is controlled by an exponential-moment bound, so is the
Gaussian's own exponential moment. -/
theorem integral_exp_abs_gaussian_le_of_variance_bound {θ K : ℝ} (hθ : 0 < θ) (v : ℝ≥0)
    (hv : (v : ℝ) ≤ (4 / θ ^ 2) * K) :
    (∫ x : ℝ, Real.exp (θ * |x|) ∂gaussianReal 0 v) ≤ 2 * Real.exp (2 * K) := by
  apply (integral_exp_abs_gaussian_le θ v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hv (sq_nonneg θ)
  have he : ((4 / θ ^ 2) * K) * θ ^ 2 = 4 * K := by field_simp
  rw [he] at hh
  linarith

end LatticeProb
