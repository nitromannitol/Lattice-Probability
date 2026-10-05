/-
# Derivatives and Gaussian decay of the density `covDensity S` along a coordinate line

Li--Shao normal comparison, route items 3 and 4 (`scratch/pk/normalcompare-route.md`).  The mixed
derivative integration by parts `LatticeProb.integral_Iic_mixed_deriv₂`
(`LatticeProb/Prob/NormalComparisonOrthantMixed.lean`) needs, for the density
`p = covDensity S` of `N(0, S)` (`LatticeProb/Prob/GaussCovDensity.lean`), the first and second
coordinate partials along lines and their decay at `-∞`.  With `a x = S⁻¹ *ᵥ x`:

  `∂_i p = -(a x)_i p`,    `∂_j ∂_i p = ((a x)_i (a x)_j - S⁻¹ i j) p`.

Route.  Everything is one-dimensional calculus along `s ↦ Function.update x j s`.  Write
`y s = update x j s = y 0 + s • e_j`, `T = S⁻¹` (symmetric and positive definite).  Then
`(T y s)_i = (T y 0)_i + s T i j` and the quadratic form is
`y s ⬝ᵥ T y s = T j j s² + 2 (T y 0)_j s + y 0 ⬝ᵥ T y 0`, so
`p (y s) = K exp (-(T j j / 2) s² - (T y 0)_j s)` with `K > 0` independent of `s`.  The derivative
statements follow from the chain and product rules; the decay at `-∞` from the rapid decay
`exp (a u² + b u) = o (u ^ r)` at `+∞` (`a < 0`) applied to `u = -s`, using `T j j > 0`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensity

open Filter Topology Matrix MeasureTheory

namespace LatticeProb

section Algebra

variable {n : ℕ}

/-- The point `update x j s` is `update x j 0 + s • e_j`. -/
private lemma update_eq_add_smul_single (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    Function.update x j s = Function.update x j 0 + s • (Pi.single j 1 : Fin n → ℝ) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]

/-- The inverse of a positive definite real matrix is symmetric (entrywise). -/
private lemma inv_apply_comm {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (i j : Fin n) :
    S⁻¹ i j = S⁻¹ j i := by
  have h := hS.isHermitian.inv.apply i j
  simpa using h.symm

/-- Coordinates of `T *ᵥ update x j s`: affine in `s` with slope `T i j`. -/
private lemma mulVec_update_apply (T : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (i j : Fin n)
    (s : ℝ) :
    (T *ᵥ Function.update x j s) i = (T *ᵥ Function.update x j 0) i + s * T i j := by
  rw [update_eq_add_smul_single x j s, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- The quadratic form of a symmetric matrix along a coordinate line. -/
private lemma quad_update (T : Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i j, T i j = T j i)
    (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    Function.update x j s ⬝ᵥ (T *ᵥ Function.update x j s)
      = T j j * s ^ 2 + 2 * (T *ᵥ Function.update x j 0) j * s
          + Function.update x j 0 ⬝ᵥ (T *ᵥ Function.update x j 0) := by
  set y0 := Function.update x j 0 with hy0
  have hdot : y0 ⬝ᵥ (T *ᵥ (Pi.single j 1 : Fin n → ℝ)) = (T *ᵥ y0) j := by
    rw [Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.mulVec, Matrix.col_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hT k j, mul_comm]
  rw [update_eq_add_smul_single x j s, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, hdot, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]
  ring

end Algebra

section Line

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-- Along a coordinate line the density is a constant times `exp (a s² + b s)` with
`a = -(S⁻¹ j j / 2) < 0` and `b = -(S⁻¹ *ᵥ update x j 0) j`. -/
private lemma covDensity_update_eq (hS : S.PosDef) (x : Fin n → ℝ) (j : Fin n) :
    ∃ K : ℝ, ∀ s : ℝ, covDensity S (Function.update x j s)
      = K * Real.exp (-(S⁻¹ j j / 2) * s ^ 2 + (-((S⁻¹ *ᵥ Function.update x j 0) j)) * s) := by
  refine ⟨(2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(Function.update x j 0 ⬝ᵥ (S⁻¹ *ᵥ Function.update x j 0)) / 2), fun s => ?_⟩
  have key : ∀ α m γ s : ℝ, Real.exp (-(α * s ^ 2 + 2 * m * s + γ) / 2)
      = Real.exp (-γ / 2) * Real.exp (-(α / 2) * s ^ 2 + (-m) * s) := by
    intro α m γ s
    rw [← Real.exp_add]
    congr 1
    ring
  unfold covDensity
  rw [quad_update S⁻¹ (inv_apply_comm hS) x j s, key]
  ring

/-- `a = -(S⁻¹ j j / 2)` is negative. -/
private lemma neg_inv_diag_div_two_lt (hS : S.PosDef) (j : Fin n) : -(S⁻¹ j j / 2) < 0 := by
  have := hS.inv.diag_pos (i := j)
  linarith

/-- `∂_i p = -(S⁻¹ x)_i p` along the line through `x` in direction `e_i`. -/
theorem hasDerivAt_covDensity_update (hS : S.PosDef) (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => covDensity S (Function.update x i s))
      (-((S⁻¹ *ᵥ Function.update x i t) i) * covDensity S (Function.update x i t)) t := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x i
  have hfun : (fun s => covDensity S (Function.update x i s))
      = fun s => K * Real.exp (-(S⁻¹ i i / 2) * s ^ 2
          + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * s) := funext hK
  rw [hfun, hK t, mulVec_update_apply S⁻¹ x i i t]
  have hq : HasDerivAt (fun s : ℝ => -(S⁻¹ i i / 2) * s ^ 2
      + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * s)
      (-(S⁻¹ i i / 2) * ((2 : ℕ) * t ^ (2 - 1)) + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * 1) t :=
    ((hasDerivAt_pow 2 t).const_mul _).add ((hasDerivAt_id' t).const_mul _)
  refine (hq.exp.const_mul K).congr_deriv ?_
  push_cast
  ring

/-- The second derivative: `∂_j(-(S⁻¹ x)_i p) = ((S⁻¹ x)_i (S⁻¹ x)_j - S⁻¹ i j) p`. -/
theorem hasDerivAt_covDensity_partial_update (hS : S.PosDef) (x : Fin n → ℝ) (i j : Fin n)
    (t : ℝ) :
    HasDerivAt
      (fun s => -((S⁻¹ *ᵥ Function.update x j s) i) * covDensity S (Function.update x j s))
      ((((S⁻¹ *ᵥ Function.update x j t) i) * ((S⁻¹ *ᵥ Function.update x j t) j) - S⁻¹ i j)
        * covDensity S (Function.update x j t)) t := by
  have h1 : HasDerivAt (fun s => -((S⁻¹ *ᵥ Function.update x j s) i)) (-S⁻¹ i j) t := by
    have hfun : (fun s : ℝ => -((S⁻¹ *ᵥ Function.update x j s) i))
        = fun s => -((S⁻¹ *ᵥ Function.update x j 0) i + s * S⁻¹ i j) := by
      funext s
      rw [mulVec_update_apply]
    rw [hfun]
    exact ((((hasDerivAt_id' t).mul_const (S⁻¹ i j)).const_add _).neg).congr_deriv (by simp)
  refine (h1.mul (hasDerivAt_covDensity_update hS x j t)).congr_deriv ?_
  ring

/-- `exp (a u² + b u) → 0` as `u → +∞` for `a < 0`. -/
private lemma tendsto_exp_quad_atTop {a : ℝ} (ha : a < 0) (b : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (a * u ^ 2 + b * u)) atTop (𝓝 0) := by
  have h := rexp_neg_quadratic_isLittleO_rpow_atTop ha b 0
  simp only [Real.rpow_zero] at h
  exact (Asymptotics.isLittleO_one_iff ℝ).1 h

/-- `u exp (a u² + b u) → 0` as `u → +∞` for `a < 0`. -/
private lemma tendsto_mul_exp_quad_atTop {a : ℝ} (ha : a < 0) (b : ℝ) :
    Tendsto (fun u : ℝ => u * Real.exp (a * u ^ 2 + b * u)) atTop (𝓝 0) := by
  have h := rexp_neg_quadratic_isLittleO_rpow_atTop ha b (-1)
  have h2 := (Asymptotics.isLittleO_iff_tendsto' (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    intro h0
    exact absurd h0 (Real.rpow_pos_of_pos hu _).ne')).1 h
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [Real.rpow_neg hu.le, Real.rpow_one, div_inv_eq_mul, mul_comm]

/-- `exp (a s² + b s) → 0` as `s → -∞` for `a < 0`. -/
private lemma tendsto_exp_quad_atBot {a : ℝ} (ha : a < 0) (b : ℝ) :
    Tendsto (fun s : ℝ => Real.exp (a * s ^ 2 + b * s)) atBot (𝓝 0) := by
  have h := (tendsto_exp_quad_atTop ha (-b)).comp tendsto_neg_atBot_atTop
  refine h.congr fun s => ?_
  simp

/-- `s exp (a s² + b s) → 0` as `s → -∞` for `a < 0`. -/
private lemma tendsto_mul_exp_quad_atBot {a : ℝ} (ha : a < 0) (b : ℝ) :
    Tendsto (fun s : ℝ => s * Real.exp (a * s ^ 2 + b * s)) atBot (𝓝 0) := by
  have h := ((tendsto_mul_exp_quad_atTop ha (-b)).comp tendsto_neg_atBot_atTop).neg
  rw [neg_zero] at h
  refine h.congr fun s => ?_
  simp

/-- Gaussian decay of the density along a coordinate line. -/
theorem tendsto_covDensity_update_atBot (hS : S.PosDef) (x : Fin n → ℝ) (j : Fin n) :
    Tendsto (fun s => covDensity S (Function.update x j s)) atBot (𝓝 0) := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x j
  have h := (tendsto_exp_quad_atBot (neg_inv_diag_div_two_lt hS j)
    (-((S⁻¹ *ᵥ Function.update x j 0) j))).const_mul K
  rw [mul_zero] at h
  exact h.congr fun s => (hK s).symm

/-- Gaussian decay of the first partial along a coordinate line. -/
theorem tendsto_partial_covDensity_update_atBot (hS : S.PosDef) (x : Fin n → ℝ)
    (i j : Fin n) :
    Tendsto
      (fun s => -((S⁻¹ *ᵥ Function.update x j s) i) * covDensity S (Function.update x j s))
      atBot (𝓝 0) := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x j
  have ha := neg_inv_diag_div_two_lt hS j
  set b := -((S⁻¹ *ᵥ Function.update x j 0) j) with hb
  have h0 := (tendsto_exp_quad_atBot ha b).const_mul (-((S⁻¹ *ᵥ Function.update x j 0) i) * K)
  have h1 := (tendsto_mul_exp_quad_atBot ha b).const_mul (-(S⁻¹ i j) * K)
  have h := h0.add h1
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr fun s => ?_
  rw [hK s, mulVec_update_apply S⁻¹ x i j s]
  ring

/-- Completing the square: `exp (a s² + b s) = C exp (-(-a) (s - c)²)` for some constants. -/
private lemma exp_quad_eq {a : ℝ} (ha : a < 0) (b : ℝ) :
    ∃ C c : ℝ, ∀ s : ℝ, Real.exp (a * s ^ 2 + b * s)
      = C * Real.exp (-(-a) * (s - c) ^ 2) := by
  refine ⟨Real.exp (-(b ^ 2 / (4 * a))), -b / (2 * a), fun s => ?_⟩
  rw [← Real.exp_add]
  congr 1
  have ha0 : a ≠ 0 := ha.ne
  field_simp
  ring

/-- Shifted Gaussian moments are integrable. -/
private lemma integrable_pow_mul_exp_neg_sq_shift {w : ℝ} (hw : 0 < w) (c : ℝ) (k : ℕ) :
    Integrable (fun s : ℝ => (s - c) ^ k * Real.exp (-w * (s - c) ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hw (s := (k : ℝ))
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  simpa only [Real.rpow_natCast] using h.comp_sub_right c

/-- `s ^ k exp (a s² + b s)` is integrable for `a < 0` and `k ≤ 2`. -/
private lemma integrable_pow_mul_exp_quad {a : ℝ} (ha : a < 0) (b : ℝ) {k : ℕ} (hk : k ≤ 2) :
    Integrable (fun s : ℝ => s ^ k * Real.exp (a * s ^ 2 + b * s)) := by
  obtain ⟨C, c, hC⟩ := exp_quad_eq ha b
  have hw : 0 < -a := neg_pos.2 ha
  have g0 := integrable_pow_mul_exp_neg_sq_shift hw c 0
  have g1 := integrable_pow_mul_exp_neg_sq_shift hw c 1
  have g2 := integrable_pow_mul_exp_neg_sq_shift hw c 2
  interval_cases k
  · have hfun : (fun s : ℝ => s ^ 0 * Real.exp (a * s ^ 2 + b * s))
        = fun s => C * ((s - c) ^ 0 * Real.exp (-(-a) * (s - c) ^ 2)) := by
      funext s
      rw [hC s]
      ring
    rw [hfun]
    exact g0.const_mul C
  · have hfun : (fun s : ℝ => s ^ 1 * Real.exp (a * s ^ 2 + b * s))
        = fun s => C * ((s - c) ^ 1 * Real.exp (-(-a) * (s - c) ^ 2))
            + (C * c) * ((s - c) ^ 0 * Real.exp (-(-a) * (s - c) ^ 2)) := by
      funext s
      rw [hC s]
      ring
    rw [hfun]
    exact (g1.const_mul C).add (g0.const_mul (C * c))
  · have hfun : (fun s : ℝ => s ^ 2 * Real.exp (a * s ^ 2 + b * s))
        = fun s => C * ((s - c) ^ 2 * Real.exp (-(-a) * (s - c) ^ 2))
            + (2 * C * c) * ((s - c) ^ 1 * Real.exp (-(-a) * (s - c) ^ 2))
            + (C * c ^ 2) * ((s - c) ^ 0 * Real.exp (-(-a) * (s - c) ^ 2)) := by
      funext s
      rw [hC s]
      ring
    rw [hfun]
    exact ((g2.const_mul C).add (g1.const_mul (2 * C * c))).add (g0.const_mul (C * c ^ 2))

/-- A polynomial of degree at most two times `exp (a s² + b s)` is integrable for `a < 0`. -/
private lemma integrable_quad_mul_exp_quad {a : ℝ} (ha : a < 0) (b A B C : ℝ) :
    Integrable (fun s : ℝ => (A + B * s + C * s ^ 2) * Real.exp (a * s ^ 2 + b * s)) := by
  have g0 := integrable_pow_mul_exp_quad ha b (k := 0) (by norm_num)
  have g1 := integrable_pow_mul_exp_quad ha b (k := 1) (by norm_num)
  have g2 := integrable_pow_mul_exp_quad ha b (k := 2) (by norm_num)
  have hfun : (fun s : ℝ => (A + B * s + C * s ^ 2) * Real.exp (a * s ^ 2 + b * s))
      = fun s => A * (s ^ 0 * Real.exp (a * s ^ 2 + b * s))
          + B * (s ^ 1 * Real.exp (a * s ^ 2 + b * s))
          + C * (s ^ 2 * Real.exp (a * s ^ 2 + b * s)) := by
    funext s
    ring
  rw [hfun]
  exact ((g0.const_mul A).add (g1.const_mul B)).add (g2.const_mul C)

/-- Integrability of the density along a coordinate line. -/
theorem integrable_covDensity_update (hS : S.PosDef) (x : Fin n → ℝ) (j : Fin n) :
    Integrable (fun s => covDensity S (Function.update x j s)) := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x j
  have h := (integrable_quad_mul_exp_quad (neg_inv_diag_div_two_lt hS j)
    (-((S⁻¹ *ᵥ Function.update x j 0) j)) K 0 0)
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp [hK s, mul_comm]

/-- Integrability of the first partial of the density along a coordinate line. -/
theorem integrable_partial_covDensity_update (hS : S.PosDef) (x : Fin n → ℝ) (i j : Fin n) :
    Integrable
      (fun s => -((S⁻¹ *ᵥ Function.update x j s) i) * covDensity S (Function.update x j s)) := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x j
  have h := (integrable_quad_mul_exp_quad (neg_inv_diag_div_two_lt hS j)
    (-((S⁻¹ *ᵥ Function.update x j 0) j))
    (-((S⁻¹ *ᵥ Function.update x j 0) i) * K) (-(S⁻¹ i j) * K) 0)
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [hK s, mulVec_update_apply S⁻¹ x i j s]
  ring

/-- Integrability of the second partial of the density along a coordinate line. -/
theorem integrable_partial2_covDensity_update (hS : S.PosDef) (x : Fin n → ℝ) (i j : Fin n) :
    Integrable
      (fun s => (((S⁻¹ *ᵥ Function.update x j s) i) * ((S⁻¹ *ᵥ Function.update x j s) j)
        - S⁻¹ i j) * covDensity S (Function.update x j s)) := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x j
  set m := S⁻¹ *ᵥ Function.update x j 0 with hm
  have h := (integrable_quad_mul_exp_quad (neg_inv_diag_div_two_lt hS j)
    (-(m j))
    ((m i * m j - S⁻¹ i j) * K) ((m i * S⁻¹ j j + m j * S⁻¹ i j) * K) (S⁻¹ i j * S⁻¹ j j * K))
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [hK s, hm, mulVec_update_apply S⁻¹ x i j s, mulVec_update_apply S⁻¹ x j j s]
  ring

end Line

end LatticeProb
