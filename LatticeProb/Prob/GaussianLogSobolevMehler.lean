/-
# The Mehler interpolation of an exponential tilt of a standard Gaussian vector

Let `γ = stdGaussian E` be the standard Gaussian measure of a finite-dimensional real inner
product space `E`, and let `g : E → ℝ` be `K`-Lipschitz. For an angle `α`, the Mehler
interpolation of `exp ∘ g` is

  `mehler g α u = ∫ v, exp (g (sin α • u + cos α • v)) ∂γ`.

At `α = π / 2` it is `exp ∘ g`, at `α = 0` it is the constant `∫ exp ∘ g ∂γ`, and in between it
is the Ornstein–Uhlenbeck semigroup at time `t` with `sin α = e^{-t}`.

This module records the elementary properties used by the semigroup proof of the Gaussian
logarithmic Sobolev inequality:

* `exp_le_of_lipschitz`, `exp_ge_of_lipschitz`: the exponential growth bounds of `exp ∘ g`;
* `integrable_mehlerIntegrand`, `integrable_prod_mehlerIntegrand`: integrability of the integrand
  in `v` and on the product `γ ⊗ γ`;
* `mehler_pos`, `mehler_le_exp_mul`: positivity, and the multiplicative Lipschitz bound
  `mehler g α u' ≤ e^{K |sin α| ‖u' - u‖} mehler g α u`;
* `mehler_pi_div_two`, `mehler_zero`: the two endpoints;
* `integral_mehler`: invariance, `∫ mehler g α u ∂γ(u) = ∫ exp ∘ g ∂γ`, from the rotation
  invariance of `γ ⊗ γ` (`LatticeProb.GaussConc.measurePreserving_rotPair`).
-/
import LatticeProb.Prob.GaussKahaneStein
import LatticeProb.Prob.GaussSmoothBdd

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb.GaussLSI

open GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Mehler interpolation at angle `α` of `exp ∘ g` under the standard Gaussian measure. -/
def mehler (g : E → ℝ) (α : ℝ) (u : E) : ℝ :=
  ∫ v, Real.exp (g (Real.sin α • u + Real.cos α • v)) ∂(stdGaussian E)

variable {g : E → ℝ} {K : ℝ≥0}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Upper exponential growth of `exp ∘ g` for a `K`-Lipschitz `g`. -/
theorem exp_le_of_lipschitz (hg : LipschitzWith K g) (x : E) :
    Real.exp (g x) ≤ Real.exp (g 0) * Real.exp (K * ‖x‖) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := hg.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  linarith [le_abs_self (g x - g 0)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lower exponential growth of `exp ∘ g` for a `K`-Lipschitz `g`. -/
theorem exp_ge_of_lipschitz (hg : LipschitzWith K g) (x : E) :
    Real.exp (g 0) * Real.exp (-(K * ‖x‖)) ≤ Real.exp (g x) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := hg.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  linarith [neg_abs_le (g x - g 0)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The rotated point `sin α • u + cos α • v` has norm at most `‖u‖ + ‖v‖`. -/
theorem norm_sin_smul_add_cos_smul_le (α : ℝ) (u v : E) :
    ‖Real.sin α • u + Real.cos α • v‖ ≤ ‖u‖ + ‖v‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one α)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Mehler integrand is bounded by a product of exponentials of the norms. -/
theorem exp_rot_le (hg : LipschitzWith K g) (α : ℝ) (u v : E) :
    Real.exp (g (Real.sin α • u + Real.cos α • v))
      ≤ Real.exp (g 0) * Real.exp (K * ‖u‖) * Real.exp (K * ‖v‖) := by
  refine (exp_le_of_lipschitz hg _).trans ?_
  rw [mul_assoc, ← Real.exp_add (K * ‖u‖)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sin_smul_add_cos_smul_le α u v) K.coe_nonneg

/-- The Mehler integrand is integrable in `v`. -/
theorem integrable_mehlerIntegrand (hg : LipschitzWith K g) (α : ℝ) (u : E) :
    Integrable (fun v => Real.exp (g (Real.sin α • u + Real.cos α • v))) (stdGaussian E) := by
  refine Kahane.integrable_of_le_exp (A := Real.exp (g 0) * Real.exp (K * ‖u‖)) (B := K)
    (by have := hg.continuous; fun_prop) fun v => ?_
  rw [abs_of_pos (Real.exp_pos _)]
  exact exp_rot_le hg α u v

/-- The Mehler integrand is integrable on the product `γ ⊗ γ`. -/
theorem integrable_prod_mehlerIntegrand (hg : LipschitzWith K g) (α : ℝ) :
    Integrable (fun p : E × E => Real.exp (g (Real.sin α • p.1 + Real.cos α • p.2)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  have hb : Integrable (fun p : E × E => Real.exp (g 0) *
      (Real.exp (K * ‖p.1‖) * Real.exp (K * ‖p.2‖))) ((stdGaussian E).prod (stdGaussian E)) :=
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).mul_prod
      (Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K)).const_mul _
  refine hb.mono' (by have := hg.continuous; fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc]
  exact exp_rot_le hg α p.1 p.2

/-- The Mehler interpolation is positive. -/
theorem mehler_pos (hg : LipschitzWith K g) (α : ℝ) (u : E) : 0 < mehler g α u :=
  integral_exp_pos (integrable_mehlerIntegrand hg α u)

/-- **The multiplicative Lipschitz bound.** Moving the base point from `u` to `u'` changes the
Mehler interpolation by a factor at most `e^{K |sin α| ‖u' - u‖}`. -/
theorem mehler_le_exp_mul (hg : LipschitzWith K g) (α : ℝ) (u u' : E) :
    mehler g α u' ≤ Real.exp (K * |Real.sin α| * ‖u' - u‖) * mehler g α u := by
  rw [mehler, mehler, ← integral_const_mul]
  refine integral_mono (integrable_mehlerIntegrand hg α u')
    ((integrable_mehlerIntegrand hg α u).const_mul _) fun v => ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := hg.dist_le_mul (Real.sin α • u' + Real.cos α • v) (Real.sin α • u + Real.cos α • v)
  rw [Real.dist_eq, dist_eq_norm, add_sub_add_right_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs] at h
  have := le_abs_self (g (Real.sin α • u' + Real.cos α • v) - g (Real.sin α • u + Real.cos α • v))
  nlinarith

omit [BorelSpace E] in
/-- At `α = π / 2` the Mehler interpolation is `exp ∘ g`. -/
theorem mehler_pi_div_two (u : E) : mehler g (π / 2) u = Real.exp (g u) := by
  simp [mehler]

omit [BorelSpace E] in
/-- At `α = 0` the Mehler interpolation is the constant `∫ exp ∘ g ∂γ`. -/
theorem mehler_zero (u : E) : mehler g 0 u = ∫ v, Real.exp (g v) ∂(stdGaussian E) := by
  simp [mehler]

/-- **Invariance.** The Mehler interpolation preserves the integral against `γ`. -/
theorem integral_mehler (hg : LipschitzWith K g) (α : ℝ) :
    ∫ u, mehler g α u ∂(stdGaussian E) = ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  have hrot := measurePreserving_rotPair (E := E) α
  have hint := integrable_prod_mehlerIntegrand hg α
  have hc : Continuous fun p : E × E => Real.exp (g p.1) := by
    have := hg.continuous; fun_prop
  calc ∫ u, mehler g α u ∂(stdGaussian E)
      = ∫ p, Real.exp (g (rotPair α p).1) ∂((stdGaussian E).prod (stdGaussian E)) := by
        show _ = ∫ p : E × E, Real.exp (g (Real.sin α • p.1 + Real.cos α • p.2)) ∂_
        rw [integral_prod _ hint]; rfl
    _ = ∫ p, Real.exp (g p.1) ∂((stdGaussian E).prod (stdGaussian E)) := by
        rw [← integral_map hrot.measurable.aemeasurable hc.aestronglyMeasurable, hrot.map_eq]
    _ = ∫ x, Real.exp (g x) ∂(stdGaussian E) :=
        integral_prod_fst_stdGaussian (Kahane.integrable_of_le_exp (f := fun x => Real.exp (g x))
          (A := Real.exp (g 0)) (B := K) (by have := hg.continuous; fun_prop) fun x => by
            rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_of_lipschitz hg x)

end LatticeProb.GaussLSI
