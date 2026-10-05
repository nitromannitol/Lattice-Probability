/-
# Schur-complement factorisation of the Gaussian density

Li--Shao normal comparison, route item 5 (`scratch/pk/normalcompare-route.md`).  The boundary
integral `D = ∫_{x'' ≤ b''} p(b_i, b_j, x'') dx''` of the Gaussian density `p` must be bounded by
the density of the pair `(Y_i, Y_j)` at `(b_i, b_j)`.  Instead of marginal measures, this file
proves the *conditional factorisation* of the density by a Schur complement, and then the
marginalisation by the normalisation `∫ covDensity = 1`
(`LatticeProb.integral_covDensity`, `LatticeProb/Prob/NormalComparisonBoundaryIntegral.lean`).

Setting.  `covDensityOn S x = (2π)^{-|ι|/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)` is the density
of `N(0, S)` on an arbitrary finite index type `ι` (for `ι = Fin n` it is `covDensity S`).

Route.
1. `covDensity_eq_covDensityOn` (`Fintype.card_fin`) and `covDensityOn_submatrix_equiv`
   (reindexing a coordinate bijection: `det_submatrix_equiv_self`, `inv_submatrix_equiv`,
   `submatrix_mulVec_equiv`, `comp_equiv_dotProduct_comp_equiv`).
2. Let `P = [[A, B], [Bᵀ, D]]` be positive definite.  Then `A` is positive definite (principal
   submatrix), and so is the Schur complement `Δ = D - Bᵀ A⁻¹ B`
   (`schur_complement_eq₁₁` evaluated at `(-(A⁻¹ B) z, z)`).
3. The quadratic form of the inverse completes the square: for `y = P⁻¹ (u, w)` with blocks
   `y₁, y₂` one has `A y₁ + B y₂ = u`, `Bᵀ y₁ + D y₂ = w`, hence `Δ y₂ = w - (A⁻¹ B)ᵀ u` and
   `(u, w) ⬝ᵥ P⁻¹ (u, w) = u ⬝ᵥ A⁻¹ u + c ⬝ᵥ Δ⁻¹ c`, `c = w - (A⁻¹ B)ᵀ u`.
4. `det P = det A * det Δ` (`Matrix.det_fromBlocks₁₁`), and the real powers and the exponential
   split: `covDensityOn P (u, w) = covDensityOn A u * covDensityOn Δ (w - (A⁻¹ B)ᵀ u)`.
5. Integrating in `w`: pull out `covDensityOn A u`, translate `w ↦ w - c`
   (`integral_sub_right_eq_self`), and transport `integral_covDensity` from `Fin m` to the index
   type `κ` along `MeasurableEquiv.piCongrLeft` (volume preserving).
-/
import Mathlib
import LatticeProb.Prob.NormalComparisonBoundaryIntegral

open MeasureTheory Matrix

namespace LatticeProb

/-- The density of N(0,S) on an arbitrary finite index type. -/
noncomputable def covDensityOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * S.det ^ (-(1 : ℝ) / 2) *
    Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2)

/-- On `Fin n` the density `covDensityOn` is `covDensity`. -/
theorem covDensity_eq_covDensityOn {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    covDensity S x = covDensityOn S x := by
  unfold covDensity covDensityOn
  rw [Fintype.card_fin]

/-- Reindexing a coordinate bijection leaves the density unchanged. -/
theorem covDensityOn_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (S : Matrix ι ι ℝ) (x : ι → ℝ) :
    covDensityOn (S.submatrix e e) (x ∘ e) = covDensityOn S x := by
  have hx : (x ∘ e) ∘ e.symm = x := by funext i; simp
  unfold covDensityOn
  rw [Fintype.card_congr e, Matrix.det_submatrix_equiv_self, Matrix.inv_submatrix_equiv,
    Matrix.submatrix_mulVec_equiv, hx, comp_equiv_dotProduct_comp_equiv]

section Schur

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The upper left block of a positive definite block matrix is positive definite. -/
private lemma posDef_block₁₁ {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (hS : (Matrix.fromBlocks A B Bᵀ D).PosDef) : A.PosDef := by
  have h := hS.submatrix (e := (Sum.inl : ι → ι ⊕ κ)) Sum.inl_injective
  have h2 : (Matrix.fromBlocks A B Bᵀ D).submatrix Sum.inl Sum.inl = A :=
    Matrix.toBlocks_fromBlocks₁₁ A B Bᵀ D
  rwa [h2] at h

/-- The inverse of a positive definite real matrix is symmetric. -/
private lemma transpose_inv_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) : (A⁻¹)ᵀ = A⁻¹ := by
  have h : Aᵀ = A := by
    have := hA.isHermitian.eq
    simpa using this
  rw [Matrix.transpose_nonsing_inv, h]

omit [DecidableEq κ] in
/-- The Schur complement `D - Bᵀ A⁻¹ B` of a positive definite block matrix is positive
definite. -/
private lemma posDef_schur {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (hS : (Matrix.fromBlocks A B Bᵀ D).PosDef) : (D - Bᵀ * A⁻¹ * B).PosDef := by
  have hA : A.PosDef := posDef_block₁₁ hS
  letI : Invertible A := hA.isUnit.invertible
  have hBt : Bᴴ = Bᵀ := Matrix.conjTranspose_eq_transpose_of_trivial B
  have hS' : (Matrix.fromBlocks A B Bᴴ D).PosDef := by rwa [hBt]
  rw [← hBt]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have hD : D.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hS'.isHermitian).2.2.2
    exact hD.sub (Matrix.isHermitian_conjTranspose_mul_mul B hA.isHermitian.inv)
  · intro z hz
    have hz' : (Sum.elim (-((A⁻¹ * B) *ᵥ z)) z : ι ⊕ κ → ℝ) ≠ 0 := by
      intro h
      apply hz
      funext k
      simpa using congrFun h (Sum.inr k)
    have h := hS'.dotProduct_mulVec_pos hz'
    rw [Matrix.dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel,
      dotProduct_zero, zero_add, ← Matrix.dotProduct_mulVec] at h
    exact h

/-- Completing the square for the quadratic form of the inverse of a positive definite block
matrix `P = [[A, B], [Bᵀ, D]]`: with `c = w - (A⁻¹ B)ᵀ u` and `Δ = D - Bᵀ A⁻¹ B`,
`(u, w) ⬝ᵥ P⁻¹ (u, w) = u ⬝ᵥ A⁻¹ u + c ⬝ᵥ Δ⁻¹ c`. -/
private lemma quad_inv_fromBlocks {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (hS : (Matrix.fromBlocks A B Bᵀ D).PosDef) (u : ι → ℝ) (w : κ → ℝ) :
    Sum.elim u w ⬝ᵥ ((Matrix.fromBlocks A B Bᵀ D)⁻¹ *ᵥ Sum.elim u w)
      = u ⬝ᵥ (A⁻¹ *ᵥ u) + (w - (A⁻¹ * B)ᵀ *ᵥ u) ⬝ᵥ
          ((D - Bᵀ * A⁻¹ * B)⁻¹ *ᵥ (w - (A⁻¹ * B)ᵀ *ᵥ u)) := by
  have hA : A.PosDef := posDef_block₁₁ hS
  have hΔ : (D - Bᵀ * A⁻¹ * B).PosDef := posDef_schur hS
  have hdA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hdΔ : IsUnit (D - Bᵀ * A⁻¹ * B).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hΔ.isUnit
  have hdP : IsUnit (Matrix.fromBlocks A B Bᵀ D).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  set P := Matrix.fromBlocks A B Bᵀ D with hP
  set y : ι ⊕ κ → ℝ := P⁻¹ *ᵥ Sum.elim u w with hy
  have hPy : P *ᵥ y = Sum.elim u w := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdP, Matrix.one_mulVec]
  have hy1 : A *ᵥ (y ∘ Sum.inl) + B *ᵥ (y ∘ Sum.inr) = u := by
    have := congrArg (fun v => v ∘ Sum.inl) hPy
    simpa [hP, Matrix.fromBlocks_mulVec] using this
  have hy2 : Bᵀ *ᵥ (y ∘ Sum.inl) + D *ᵥ (y ∘ Sum.inr) = w := by
    have := congrArg (fun v => v ∘ Sum.inr) hPy
    simpa [hP, Matrix.fromBlocks_mulVec] using this
  have hAinvT := transpose_inv_of_posDef hA
  have e1 : (A⁻¹ * B)ᵀ * A = Bᵀ := by
    rw [Matrix.transpose_mul, hAinvT, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdA,
      Matrix.mul_one]
  have e2 : (A⁻¹ * B)ᵀ * B = Bᵀ * A⁻¹ * B := by
    rw [Matrix.transpose_mul, hAinvT]
  have hc : w - (A⁻¹ * B)ᵀ *ᵥ u = (D - Bᵀ * A⁻¹ * B) *ᵥ (y ∘ Sum.inr) := by
    have : (A⁻¹ * B)ᵀ *ᵥ u = Bᵀ *ᵥ (y ∘ Sum.inl) + (Bᵀ * A⁻¹ * B) *ᵥ (y ∘ Sum.inr) := by
      conv_lhs => rw [← hy1]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, e2]
    rw [this, ← hy2, Matrix.sub_mulVec]
    abel
  have hy2' : y ∘ Sum.inr = (D - Bᵀ * A⁻¹ * B)⁻¹ *ᵥ (w - (A⁻¹ * B)ᵀ *ᵥ u) := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdΔ, Matrix.one_mulVec]
  have hy1' : y ∘ Sum.inl = A⁻¹ *ᵥ u - (A⁻¹ * B) *ᵥ (y ∘ Sum.inr) := by
    rw [← hy1, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hdA, Matrix.one_mulVec]
    abel
  have hdot : u ⬝ᵥ ((A⁻¹ * B) *ᵥ (y ∘ Sum.inr)) = ((A⁻¹ * B)ᵀ *ᵥ u) ⬝ᵥ (y ∘ Sum.inr) := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hxy : Sum.elim u w ⬝ᵥ y = u ⬝ᵥ (y ∘ Sum.inl) + w ⬝ᵥ (y ∘ Sum.inr) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr y]
    exact sumElim_dotProduct_sumElim ..
  show Sum.elim u w ⬝ᵥ y = _
  rw [hxy, hy1', dotProduct_sub, hdot, ← hy2', sub_dotProduct]
  ring

/-- **The Schur-complement factorisation of the Gaussian density.**  For
`S = [[A, B], [Bᵀ, D]]` positive definite, `K = A⁻¹ * B` and `Δ = D - Bᵀ * A⁻¹ * B`
(positive definite), and `u : ι → ℝ`, `w : κ → ℝ`,
`density_S (u, w) = density_A (u) * density_Δ (w - Kᵀ u)`. -/
theorem covDensityOn_fromBlocks (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (hS : (Matrix.fromBlocks A B Bᵀ D).PosDef) (u : ι → ℝ) (w : κ → ℝ) :
    covDensityOn (Matrix.fromBlocks A B Bᵀ D) (Sum.elim u w)
      = covDensityOn A u * covDensityOn (D - Bᵀ * A⁻¹ * B) (w - (A⁻¹ * B)ᵀ *ᵥ u) := by
  have hA : A.PosDef := posDef_block₁₁ hS
  have hΔ : (D - Bᵀ * A⁻¹ * B).PosDef := posDef_schur hS
  have hdet : (Matrix.fromBlocks A B Bᵀ D).det = A.det * (D - Bᵀ * A⁻¹ * B).det := by
    letI : Invertible A := hA.isUnit.invertible
    rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have h2pi : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  unfold covDensityOn
  rw [quad_inv_fromBlocks hS u w, hdet, Fintype.card_sum]
  have e1 : (2 * Real.pi) ^ (-((Fintype.card ι + Fintype.card κ : ℕ) : ℝ) / 2)
      = (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)
        * (2 * Real.pi) ^ (-(Fintype.card κ : ℝ) / 2) := by
    rw [← Real.rpow_add h2pi]
    congr 1
    push_cast
    ring
  have e2 : (A.det * (D - Bᵀ * A⁻¹ * B).det) ^ (-(1 : ℝ) / 2)
      = A.det ^ (-(1 : ℝ) / 2) * (D - Bᵀ * A⁻¹ * B).det ^ (-(1 : ℝ) / 2) :=
    Real.mul_rpow hA.det_pos.le hΔ.det_pos.le
  rw [e1, e2, show -(u ⬝ᵥ (A⁻¹ *ᵥ u) + (w - (A⁻¹ * B)ᵀ *ᵥ u) ⬝ᵥ
        ((D - Bᵀ * A⁻¹ * B)⁻¹ *ᵥ (w - (A⁻¹ * B)ᵀ *ᵥ u))) / 2
      = -(u ⬝ᵥ (A⁻¹ *ᵥ u)) / 2 + -((w - (A⁻¹ * B)ᵀ *ᵥ u) ⬝ᵥ
        ((D - Bᵀ * A⁻¹ * B)⁻¹ *ᵥ (w - (A⁻¹ * B)ᵀ *ᵥ u))) / 2 by ring, Real.exp_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate change `MeasurableEquiv.piCongrLeft (fun _ => ℝ) e` along an index
bijection is `y ↦ fun l => y (e.symm l)`. -/
private lemma piCongrLeft_const_eq {ι' : Type*} (e : ι' ≃ ι) (y : ι' → ℝ) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) y = fun l => y (e.symm l) := by
  funext l
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

/-- A positive definite `Δ : Matrix κ κ ℝ` has a Gaussian density of total mass one. -/
private lemma integral_covDensityOn {Δ : Matrix κ κ ℝ} (hΔ : Δ.PosDef) :
    ∫ w : κ → ℝ, covDensityOn Δ w = 1 := by
  set e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm with he
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : κ => ℝ) e
  rw [← hmp.integral_comp' (fun w => covDensityOn Δ w)]
  have h : ∀ y : Fin (Fintype.card κ) → ℝ,
      covDensityOn Δ ((MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e) y)
        = covDensity (Δ.submatrix e e) y := by
    intro y
    rw [covDensity_eq_covDensityOn, ← covDensityOn_submatrix_equiv e Δ, piCongrLeft_const_eq]
    congr 2
    funext i
    simp
  simp_rw [h]
  exact integral_covDensity (hΔ.submatrix e.injective)

/-- Integrating out the second block returns the density of the first. -/
theorem integral_covDensityOn_fromBlocks (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) (hS : (Matrix.fromBlocks A B Bᵀ D).PosDef) (u : ι → ℝ) :
    ∫ w : κ → ℝ, covDensityOn (Matrix.fromBlocks A B Bᵀ D) (Sum.elim u w) = covDensityOn A u := by
  have hΔ : (D - Bᵀ * A⁻¹ * B).PosDef := posDef_schur hS
  simp_rw [covDensityOn_fromBlocks A B D hS u]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun w : κ → ℝ => covDensityOn (D - Bᵀ * A⁻¹ * B) w)
      ((A⁻¹ * B)ᵀ *ᵥ u),
    integral_covDensityOn hΔ, mul_one]

end Schur

end LatticeProb
