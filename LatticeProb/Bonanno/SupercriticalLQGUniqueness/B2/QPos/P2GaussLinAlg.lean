/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2GaussLinAlg at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

 











set_option autoImplicit false
noncomputable section

open Matrix Complex
open scoped MatrixOrder

namespace SupercriticalLQGUniqueness.B2.QPos

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cfcSqrt_isHermitian (S : Matrix V V ℝ) : (CFC.sqrt S).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).1

theorem cfcSqrt_transpose (S : Matrix V V ℝ) : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  have h := (cfcSqrt_isHermitian S).eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem cfcSqrt_mul_self {S : Matrix V V ℝ} (hS : S.PosSemidef) :
    CFC.sqrt S * CFC.sqrt S = S :=
  CFC.sqrt_mul_sqrt_self S hS.nonneg

 
theorem dotProduct_mulVec_symm {R : Type*} [CommSemiring R] (A : Matrix V V R) (hA : Aᵀ = A)
    (x y : V → R) : (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

 
structure GaussDiag (K : Matrix V V ℝ) (θ : V → ℝ) where
  hS : (CFC.sqrt K⁻¹ * Matrix.diagonal θ * CFC.sqrt K⁻¹).IsHermitian

namespace GaussDiag

 
abbrev sq (K : Matrix V V ℝ) : Matrix V V ℝ := CFC.sqrt K⁻¹

theorem S_isHermitian (K : Matrix V V ℝ) (θ : V → ℝ) :
    (sq K * Matrix.diagonal θ * sq K).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_mul, Matrix.transpose_mul, cfcSqrt_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

variable (K : Matrix V V ℝ) (θ : V → ℝ)

 
def e (i : V) : V → ℝ := ⇑((S_isHermitian K θ).eigenvectorBasis i)

 
def μ (i : V) : ℝ := (S_isHermitian K θ).eigenvalues i

 
def β (i : V) : ℝ := (sq K *ᵥ θ) ⬝ᵥ e K θ i

theorem e_orthonormal (i j : V) : e K θ i ⬝ᵥ e K θ j = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.mp ((S_isHermitian K θ).eigenvectorBasis).orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at h
  exact h

theorem e_complete (v w : V) : ∑ i, e K θ i v * e K θ i w = if v = w then 1 else 0 := by
  set b := (S_isHermitian K θ).eigenvectorBasis
  have h := b.sum_repr' (EuclideanSpace.single w (1 : ℝ))
  have hv := congrArg (fun x : EuclideanSpace ℝ V => x v) h
  simp only at hv
  rw [PiLp.single_apply] at hv
  rw [← hv]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.inner_single_right, one_mul, e, b, starRingEnd_apply, star_trivial]
  ring

theorem S_mulVec_e (i : V) :
    (sq K * Matrix.diagonal θ * sq K) *ᵥ e K θ i = μ K θ i • e K θ i :=
  (S_isHermitian K θ).mulVec_eigenvectorBasis i

 
theorem sum_theta_sq (c : V → ℝ) :
    ∑ v, θ v * (sq K *ᵥ ∑ i, c i • e K θ i) v ^ 2 = ∑ i, μ K θ i * c i ^ 2 := by
  set x : V → ℝ := ∑ i, c i • e K θ i
  have h1 : ∑ v, θ v * (sq K *ᵥ x) v ^ 2 =
      (sq K *ᵥ x) ⬝ᵥ (Matrix.diagonal θ *ᵥ (sq K *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have h2 : (sq K *ᵥ x) ⬝ᵥ (Matrix.diagonal θ *ᵥ (sq K *ᵥ x)) =
      x ⬝ᵥ ((sq K * Matrix.diagonal θ * sq K) *ᵥ x) := by
    rw [dotProduct_mulVec_symm _ (cfcSqrt_transpose _), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
  rw [h1, h2]
  have hSx : (sq K * Matrix.diagonal θ * sq K) *ᵥ x = ∑ i, (c i * μ K θ i) • e K θ i := by
    simp only [x, Matrix.mulVec_sum, Matrix.mulVec_smul, S_mulVec_e, smul_smul]
  rw [hSx]
  simp only [x, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
    e_orthonormal, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  ring

 
theorem sum_theta_lin (c : V → ℝ) :
    ∑ v, θ v * (sq K *ᵥ ∑ i, c i • e K θ i) v = ∑ i, c i * β K θ i := by
  have h : ∑ v, θ v * (sq K *ᵥ ∑ i, c i • e K θ i) v =
      θ ⬝ᵥ (sq K *ᵥ ∑ i, c i • e K θ i) := rfl
  rw [h, ← dotProduct_mulVec_symm _ (cfcSqrt_transpose _)]
  simp only [β, dotProduct_sum, dotProduct_smul, smul_eq_mul]

 

theorem sum_beta_sq_div (hK : K.PosDef) (p : V → ℂ)
    (hp : (K.map (fun x => (x : ℂ)) - Matrix.diagonal fun v => (θ v : ℂ) * I) *ᵥ p =
      fun v => (θ v : ℂ)) :
    ∑ i, (β K θ i : ℂ) ^ 2 / (1 - μ K θ i * I) = ∑ v, (θ v : ℂ) * p v := by
  set A : Matrix V V ℂ := (sq K).map (fun x => (x : ℂ)) with hA
  set Kc : Matrix V V ℂ := K.map (fun x => (x : ℂ)) with hKc
  set Θc : Matrix V V ℂ := Matrix.diagonal fun v => (θ v : ℂ) with hΘc
  set Sc : Matrix V V ℂ := (sq K * Matrix.diagonal θ * sq K).map (fun x => (x : ℂ)) with hSc
  have cast_mul : ∀ M N : Matrix V V ℝ, (M * N).map (fun x => (x : ℂ)) =
      M.map (fun x => (x : ℂ)) * N.map (fun x => (x : ℂ)) := fun M N =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hAA : A * A * Kc = 1 := by
    rw [hA, hKc, ← cast_mul, ← cast_mul,
      cfcSqrt_mul_self hK.posSemidef.inv, Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit), Matrix.map_one _ (by simp) (by simp)]
  have hSc' : Sc = A * Θc * A := by
    rw [hSc, cast_mul, cast_mul, hA, hΘc, Matrix.diagonal_map (by simp)]
  have hAT : A.transpose = A := by
    rw [hA, ← Matrix.transpose_map, cfcSqrt_transpose]
  have hST : Sc.transpose = Sc := by
    have h := (S_isHermitian K θ).eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hSc, ← Matrix.transpose_map, h]
  set w : V → ℂ := fun v => ((sq K *ᵥ θ) v : ℂ) with hw
  have hwA : w = A *ᵥ fun v => (θ v : ℂ) := by
    funext v
    simp [hw, hA, Matrix.mulVec, dotProduct]
  set q : V → ℂ := (A * Kc) *ᵥ p with hq
  have hp' : Kc *ᵥ p - I • (Θc *ᵥ p) = fun v => (θ v : ℂ) := by
    rw [← hp, Matrix.sub_mulVec]
    funext v
    simp [Θc, Matrix.mulVec_diagonal]
    ring
  
  have hres : q - I • (Sc *ᵥ q) = w := by
    have hSq : Sc *ᵥ q = A *ᵥ (Θc *ᵥ p) := by
      rw [hSc', hq, Matrix.mulVec_mulVec, show A * Θc * A * (A * Kc) = A * Θc * (A * A * Kc) by
        simp only [Matrix.mul_assoc], hAA, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    rw [hSq, hq, ← Matrix.mulVec_mulVec, hwA, ← hp', Matrix.mulVec_sub, Matrix.mulVec_smul]
  
  set ec : V → V → ℂ := fun i v => (e K θ i v : ℂ) with hec
  have hcoef : ∀ i, (ec i) ⬝ᵥ q = (β K θ i : ℂ) / (1 - μ K θ i * I) := by
    intro i
    have hS_e : Sc *ᵥ ec i = (μ K θ i : ℂ) • ec i := by
      have := S_mulVec_e K θ i
      funext v
      have hv := congrFun this v
      simp only [Pi.smul_apply, smul_eq_mul] at hv
      simp only [hSc, hec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [← Complex.ofReal_mul, ← hv]
      simp [Matrix.mulVec, dotProduct]
    have hdot := congrArg (fun z => ec i ⬝ᵥ z) hres
    rw [dotProduct_sub, dotProduct_smul, ← dotProduct_mulVec_symm Sc hST, hS_e,
      smul_dotProduct, smul_eq_mul, smul_eq_mul] at hdot
    have hβ : ec i ⬝ᵥ w = (β K θ i : ℂ) := by
      simp only [hec, hw, β, dotProduct]
      push_cast
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [hβ] at hdot
    have hne : (1 : ℂ) - μ K θ i * I ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
    rw [eq_div_iff hne]
    linear_combination hdot
  
  have hcompl : ∀ v, q v = ∑ i, ((ec i) ⬝ᵥ q) * ec i v := by
    intro v
    simp only [dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ x : V, ∑ i, ec i x * q x * ec i v = q x * (if x = v then 1 else 0) := by
      intro x
      have hc := e_complete K θ x v
      have : ∑ i, ec i x * q x * ec i v = q x * ((∑ i, e K θ i x * e K θ i v : ℝ) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hec]
        ring
      rw [this, hc]
      split_ifs <;> simp
    simp_rw [this]
    simp
  have hwq : w ⬝ᵥ q = ∑ v, (θ v : ℂ) * p v := by
    rw [hwA, dotProduct_mulVec_symm A hAT, hq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hAA,
      Matrix.one_mulVec]
    rfl
  rw [← hwq]
  have : w ⬝ᵥ q = ∑ i, (β K θ i : ℂ) * ((ec i) ⬝ᵥ q) := by
    conv_lhs => rw [dotProduct]
    simp_rw [hcompl]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hβ' : (β K θ i : ℂ) = ∑ v, w v * ec i v := by
      simp only [hec, hw, β, dotProduct]
      push_cast
      rfl
    rw [hβ', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [this]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoef i]
  ring

end GaussDiag

end SupercriticalLQGUniqueness.B2.QPos
