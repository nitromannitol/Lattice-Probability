/-
# The covariance derivative of the Gaussian density along a line `t ↦ A + t B`

Li--Shao normal comparison, route item 3 (`scratch/pk/normalcompare-route.md`).  The orthant
probability is differentiated along the covariance path `t ↦ A + t B`; the pointwise core is the
derivative of the density `covDensity` (`LatticeProb/Prob/GaussCovDensity.lean`) in `t`.  The
classical identity is `∂ₜ p = (1/2) ∑ᵢⱼ Bᵢⱼ ∂ᵢ∂ⱼ p`, where
`∂ᵢ∂ⱼ p = ((S⁻¹x)ᵢ (S⁻¹x)ⱼ - S⁻¹ᵢⱼ) p`, `S = A + t₀ B`.  Here:

* `hasDerivAt_det_add_smul`: Jacobi's formula along a line,
  `d/dt det (A + t B) = det S * tr (S⁻¹ B)`.  Route: `A + t B = S * (1 + (t - t₀) • S⁻¹ B)`,
  `det` is multiplicative, and `det (1 + X • M)` is a polynomial whose derivative at `0` is
  `tr M` (`Matrix.derivative_det_one_add_X_smul`).
* `hasDerivAt_inv_entry_add_smul`: each entry of `(A + t B)⁻¹` has derivative
  `-(S⁻¹ B S⁻¹)ᵢⱼ`.  Route: the resolvent identity
  `T⁻¹ = S⁻¹ - (t - t₀) • T⁻¹ B S⁻¹` for `T = A + t B`, together with continuity of the matrix
  inverse at an invertible point (`continuousAt_matrix_inv`), gives the slope as a continuous
  function of `t`.
* `hasDerivAt_quadForm_inv_add_smul`: `d/dt (x ⬝ᵥ (A + t B)⁻¹ x) = -((S⁻¹x) ⬝ᵥ B (S⁻¹x))`,
  the sum of the entry derivatives, using the symmetry of `S⁻¹` for positive definite `S`.
* `hasDerivAt_covDensity_add_smul`: the chain rule on
  `covDensity (A + t B) x = (2π)^{-n/2} (det (A + t B))^{-1/2} exp (-(x ⬝ᵥ (A + t B)⁻¹ x)/2)`.
-/
import Mathlib
import LatticeProb.Prob.GaussCovDensity

open Matrix Polynomial Topology Filter

namespace LatticeProb

/-- Jacobi's formula along a line: `d/dt det (A + t B) = det S * tr (S⁻¹ B)` at `t₀`, where
`S = A + t₀ B` has unit determinant. -/
theorem hasDerivAt_det_add_smul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hS : IsUnit (A + t₀ • B).det) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      ((A + t₀ • B).det * ((A + t₀ • B)⁻¹ * B).trace) t₀ := by
  set S : Matrix (Fin n) (Fin n) ℝ := A + t₀ • B with hSdef
  set M : Matrix (Fin n) (Fin n) ℝ := S⁻¹ * B with hM
  have hfac : ∀ t : ℝ, A + t • B = S * (1 + (t - t₀) • M) := by
    intro t
    have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hM, ← Matrix.mul_assoc, hSS,
      Matrix.one_mul, hSdef, sub_smul]
    abel
  have hP : ∀ r : ℝ, (det (1 + (X : ℝ[X]) • M.map C)).eval r = det (1 + r • M) := by
    intro r
    simp [eval_det, ← smul_eq_mul_diagonal]
  have h0 := (det (1 + (X : ℝ[X]) • M.map C)).hasDerivAt (0 : ℝ)
  rw [derivative_det_one_add_X_smul] at h0
  have h1 : HasDerivAt (fun t : ℝ => det (1 + (t - t₀) • M)) M.trace t₀ := by
    have h0' : HasDerivAt (fun r : ℝ => det (1 + r • M)) M.trace (t₀ - t₀) := by
      rw [sub_self]
      simpa only [hP] using h0
    exact h0'.comp_sub_const t₀ t₀
  have h2 := h1.const_mul S.det
  refine h2.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun t => by simp only [hfac t, Matrix.det_mul]

/-- Every entry of the inverse along a line is differentiable:
`d/dt (A + t B)⁻¹ᵢⱼ = -(S⁻¹ B S⁻¹)ᵢⱼ` at `t₀`, where `S = A + t₀ B` has unit determinant. -/
theorem hasDerivAt_inv_entry_add_smul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hS : IsUnit (A + t₀ • B).det) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A + t • B)⁻¹ i j)
      (-((A + t₀ • B)⁻¹ * B * (A + t₀ • B)⁻¹) i j) t₀ := by
  set S : Matrix (Fin n) (Fin n) ℝ := A + t₀ • B with hSdef
  have hpath : Continuous fun t : ℝ => A + t • B :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet : Continuous fun t : ℝ => (A + t • B).det := hpath.matrix_det
  have hdet0 : S.det ≠ 0 := hS.ne_zero
  have hunit : ∀ᶠ t in 𝓝 t₀, IsUnit (A + t • B).det := by
    have := hdet.continuousAt (x := t₀) |>.eventually_ne hdet0
    exact this.mono fun t ht => isUnit_iff_ne_zero.mpr ht
  have hinv : ContinuousAt (fun t : ℝ => (A + t • B)⁻¹) t₀ := by
    have hr : ContinuousAt Ring.inverse S.det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet0
    exact (continuousAt_matrix_inv S hr).comp hpath.continuousAt
  have hid : ∀ t : ℝ, IsUnit (A + t • B).det →
      (A + t • B)⁻¹ = S⁻¹ - (t - t₀) • ((A + t • B)⁻¹ * B * S⁻¹) := by
    intro t ht
    have h1 : (A + t • B)⁻¹ * (A + t • B) = 1 := Matrix.nonsing_inv_mul _ ht
    have h2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ hS
    have h3 : A + t • B = S + (t - t₀) • B := by
      rw [hSdef, sub_smul]; abel
    calc (A + t • B)⁻¹
        = (A + t • B)⁻¹ * (S * S⁻¹) - ((A + t • B)⁻¹ * (A + t • B)) * S⁻¹ + S⁻¹ := by
          rw [h1, h2]; simp
      _ = S⁻¹ - (t - t₀) • ((A + t • B)⁻¹ * B * S⁻¹) := by
          rw [h3]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc]
          abel
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun t : ℝ => -((A + t • B)⁻¹ * (B * S⁻¹)) i j) (𝓝 t₀)
      (𝓝 (-(S⁻¹ * (B * S⁻¹)) i j)) := by
    have hc : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => -(M * (B * S⁻¹)) i j)
        (A + t₀ • B)⁻¹ := by
      apply Continuous.continuousAt
      exact ((continuous_id.matrix_mul continuous_const).neg.matrix_elem i j)
    exact (ContinuousAt.comp (f := fun t : ℝ => (A + t • B)⁻¹) hc hinv).tendsto
  have hlim' : Tendsto (fun t : ℝ => -((A + t • B)⁻¹ * (B * S⁻¹)) i j) (𝓝[≠] t₀)
      (𝓝 (-(S⁻¹ * (B * S⁻¹)) i j)) := hlim.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[≠] t₀, -((A + t • B)⁻¹ * (B * S⁻¹)) i j
      = slope (fun t : ℝ => (A + t • B)⁻¹ i j) t₀ t := by
    have hne : ∀ᶠ t in 𝓝[≠] t₀, t ≠ t₀ := self_mem_nhdsWithin
    have hu : ∀ᶠ t in 𝓝[≠] t₀, IsUnit (A + t • B).det := nhdsWithin_le_nhds hunit
    filter_upwards [hne, hu] with t ht htu
    have hsub : t - t₀ ≠ 0 := sub_ne_zero.mpr ht
    have h := congr_fun (congr_fun (hid t htu) i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc] at h
    rw [slope_def_module, smul_eq_mul, ← hSdef, h]
    field_simp
    ring
  have := hlim'.congr' hev
  simpa only [Matrix.neg_apply, Matrix.mul_assoc] using this

/-- Symmetric bilinear forms: `x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y` when `Mᵀ = M`. -/
theorem dotProduct_mulVec_of_transpose_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Mᵀ = M) (x y : Fin n → ℝ) : x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM]

/-- The derivative of the quadratic form `x ⬝ᵥ (A + t B)⁻¹ x` at `t₀` is
`-(S⁻¹ x) ⬝ᵥ B (S⁻¹ x)`, `S = A + t₀ B` positive definite (hence `S⁻¹` symmetric). -/
theorem hasDerivAt_quadForm_inv_add_smul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hS : (A + t₀ • B).PosDef) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => x ⬝ᵥ ((A + t • B)⁻¹ *ᵥ x))
      (-(((A + t₀ • B)⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ ((A + t₀ • B)⁻¹ *ᵥ x)))) t₀ := by
  have hU : IsUnit (A + t₀ • B).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hsym : ((A + t₀ • B)⁻¹)ᵀ = (A + t₀ • B)⁻¹ := by
    have h := hS.isHermitian.inv
    rwa [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm] at h
  have hsum : HasDerivAt (fun t : ℝ => ∑ i, x i * ∑ j, (A + t • B)⁻¹ i j * x j)
      (∑ i, x i * ∑ j, (-((A + t₀ • B)⁻¹ * B * (A + t₀ • B)⁻¹) i j) * x j) t₀ := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    refine HasDerivAt.const_mul (x i) ?_
    exact HasDerivAt.fun_sum fun j _ =>
      (hasDerivAt_inv_entry_add_smul A B t₀ hU i j).mul_const (x j)
  have hform : ∀ M : Matrix (Fin n) (Fin n) ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, x i * ∑ j, M i j * x j := by
    intro M
    simp [dotProduct, Matrix.mulVec]
  have hfun : (fun t : ℝ => x ⬝ᵥ ((A + t • B)⁻¹ *ᵥ x))
      = fun t : ℝ => ∑ i, x i * ∑ j, (A + t • B)⁻¹ i j * x j := funext fun t => hform _
  rw [hfun]
  refine hsum.congr_deriv ?_
  have hneg : ∑ i, x i * ∑ j, (-(((A + t₀ • B)⁻¹ * B * (A + t₀ • B)⁻¹) i j)) * x j
      = -(x ⬝ᵥ (((A + t₀ • B)⁻¹ * B * (A + t₀ • B)⁻¹) *ᵥ x)) := by
    rw [hform]
    simp [neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [hneg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec_of_transpose_eq hsym]

/-- The sum `∑ i j, B i j * M i j` is `tr (M * B)` for symmetric `M`. -/
theorem sum_sum_mul_eq_trace_mul {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M)
    (B : Matrix (Fin n) (Fin n) ℝ) : ∑ i, ∑ j, B i j * M i j = (M * B).trace := by
  have hsymm : ∀ i j, M j i = M i j := fun i j => by
    simpa only [Matrix.transpose_apply] using congr_fun (congr_fun hM i) j
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm, mul_comm]

/-- The double sum `∑ i j, B i j * ((a i * a j - M i j) * p)` equals
`((a ⬝ᵥ B a) - tr (M * B)) * p` for symmetric `M`. -/
theorem sum_sum_mul_sub_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : Mᵀ = M)
    (B : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) (p : ℝ) :
    ∑ i, ∑ j, B i j * ((a i * a j - M i j) * p)
      = ((a ⬝ᵥ (B *ᵥ a)) - (M * B).trace) * p := by
  rw [← sum_sum_mul_eq_trace_mul hM B]
  have h1 : a ⬝ᵥ (B *ᵥ a) = ∑ i, ∑ j, B i j * (a i * a j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The covariance derivative of the Gaussian density along `t ↦ A + t B`:
`d/dt covDensity (A + t B) x = (1/2) ∑ᵢⱼ Bᵢⱼ ((S⁻¹x)ᵢ (S⁻¹x)ⱼ - S⁻¹ᵢⱼ) covDensity S x` at `t₀`,
where `S = A + t₀ B` is positive definite. -/
theorem hasDerivAt_covDensity_add_smul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hS : (A + t₀ • B).PosDef) (x : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => covDensity (A + t • B) x)
      (1 / 2 * ∑ i, ∑ j, B i j *
        ((((A + t₀ • B)⁻¹ *ᵥ x) i * ((A + t₀ • B)⁻¹ *ᵥ x) j - (A + t₀ • B)⁻¹ i j)
          * covDensity (A + t₀ • B) x)) t₀ := by
  have hpos : 0 < (A + t₀ • B).det := hS.det_pos
  have hU : IsUnit (A + t₀ • B).det := isUnit_iff_ne_zero.mpr hpos.ne'
  have hsym : ((A + t₀ • B)⁻¹)ᵀ = (A + t₀ • B)⁻¹ := by
    have h := hS.isHermitian.inv
    rwa [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm] at h
  have hdet := hasDerivAt_det_add_smul A B t₀ hU
  have hQ := hasDerivAt_quadForm_inv_add_smul A B t₀ hS x
  have hP := hdet.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hpos.ne')
  have hE := (hQ.fun_neg.div_const 2).exp
  have h := ((hasDerivAt_const t₀ ((2 * Real.pi) ^ (-(n : ℝ) / 2))).fun_mul hP).fun_mul hE
  refine h.congr_deriv ?_
  rw [sum_sum_mul_sub_eq hsym B, Real.rpow_sub_one hpos.ne']
  unfold covDensity
  field_simp
  ring

end LatticeProb
