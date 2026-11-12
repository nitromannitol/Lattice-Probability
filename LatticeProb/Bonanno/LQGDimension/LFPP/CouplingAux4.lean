/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.CouplingAux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Node `C36`, auxiliary file 4: Gram gluing

* `exists_linearIsometry_of_gram`: two families with the same Gram matrix in a
  finite-dimensional inner product space are related by a linear isometry of the space.
* `sumInl`, `sumInr`: the isometric embeddings of `EuclideanSpace ℝ α` and `EuclideanSpace ℝ β`
  into `EuclideanSpace ℝ (α ⊕ β)`.
* `glue`: if `w` (in `ℝ^{d₁}`) and `x₀` (in `EuclideanSpace ℝ κ`) have the same Gram matrix on a
  finite set `S`, there are a linear isometry `ι : ℝ^{d₁} → ℝ^d` and a linear isometry
  `J : EuclideanSpace ℝ κ → ℝ^d` with `ι (w s) = J (x₀ s)` on `S`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace LQGDimension.Coupling

section Glue

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma inner_linComb {ι : Type*} [Fintype ι] (u : ι → V) (c c' : ι → ℝ) :
    ⟪Fintype.linearCombination ℝ u c, Fintype.linearCombination ℝ u c'⟫ =
      ∑ i, ∑ j, c i * c' j * ⟪u i, u j⟫ := by
  simp only [Fintype.linearCombination_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Two families with equal Gram matrices are related by a linear isometry. -/
theorem exists_linearIsometry_of_gram [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (u v : ι → V) (h : ∀ i j, ⟪u i, u j⟫ = ⟪v i, v j⟫) :
    ∃ L : V →ₗᵢ[ℝ] V, ∀ i, L (u i) = v i := by
  set A := Fintype.linearCombination ℝ u with hA
  set B := Fintype.linearCombination ℝ v with hB
  have hAB : ∀ c, ⟪A c, A c⟫ = ⟪B c, B c⟫ := by
    intro c
    rw [hA, hB, inner_linComb, inner_linComb]
    simp_rw [h]
  have hnorm : ∀ c, ‖B c‖ = ‖A c‖ := by
    intro c
    have h2 := hAB c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h2
    have := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), eq_comm] at this
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let T₀ : LinearMap.range A →ₗ[ℝ] V :=
    ((LinearMap.ker A).liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hT₀ : ∀ c, T₀ ⟨A c, LinearMap.mem_range_self A c⟩ = B c := by
    intro c
    simp only [T₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let T : LinearMap.range A →ₗᵢ[ℝ] V :=
    { T₀ with
      norm_map' := by
        rintro ⟨y, c, rfl⟩
        show ‖T₀ ⟨A c, LinearMap.mem_range_self A c⟩‖ = ‖A c‖
        rw [hT₀, hnorm] }
  refine ⟨T.extend, fun i => ?_⟩
  have hu : u i = A (Pi.single i 1) := by
    rw [hA, Fintype.linearCombination_apply_single, one_smul]
  have hv : v i = B (Pi.single i 1) := by
    rw [hB, Fintype.linearCombination_apply_single, one_smul]
  have hmem : u i ∈ LinearMap.range A := hu ▸ LinearMap.mem_range_self A _
  have h1 : T.extend (u i) = T ⟨u i, hmem⟩ := LinearIsometry.extend_apply T ⟨u i, hmem⟩
  rw [h1, hv]
  show T₀ ⟨u i, hmem⟩ = B (Pi.single i 1)
  have : (⟨u i, hmem⟩ : LinearMap.range A) =
      ⟨A (Pi.single i 1), LinearMap.mem_range_self A _⟩ := Subtype.ext hu
  rw [this, hT₀]

end Glue

section Embed

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Extension by zero `ℝ^α → ℝ^(α ⊕ β)` (linear map). -/
def sumInlL : EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ (α ⊕ β) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun a => v a) 0)
  map_add' v w := by
    ext i; cases i <;> simp
  map_smul' c v := by
    ext i; cases i <;> simp

/-- Extension by zero `ℝ^β → ℝ^(α ⊕ β)` (linear map). -/
def sumInrL : EuclideanSpace ℝ β →ₗ[ℝ] EuclideanSpace ℝ (α ⊕ β) where
  toFun v := WithLp.toLp 2 (Sum.elim 0 (fun b => v b))
  map_add' v w := by
    ext i; cases i <;> simp
  map_smul' c v := by
    ext i; cases i <;> simp

/-- The isometric embedding `ℝ^α → ℝ^(α ⊕ β)`. -/
def sumInl : EuclideanSpace ℝ α →ₗᵢ[ℝ] EuclideanSpace ℝ (α ⊕ β) :=
  (sumInlL (α := α) (β := β)).isometryOfInner (by
    intro v w
    simp [sumInlL, PiLp.inner_apply, Fintype.sum_sum_type])

/-- The isometric embedding `ℝ^β → ℝ^(α ⊕ β)`. -/
def sumInr : EuclideanSpace ℝ β →ₗᵢ[ℝ] EuclideanSpace ℝ (α ⊕ β) :=
  (sumInrL (α := α) (β := β)).isometryOfInner (by
    intro v w
    simp [sumInrL, PiLp.inner_apply, Fintype.sum_sum_type])

end Embed

/-- **Gram gluing.** -/
theorem glue {d₁ : ℕ} {κ : Type*} [Fintype κ] (S : Finset ℂ)
    (w : ℂ → EuclideanSpace ℝ (Fin d₁)) (x₀ : ℂ → EuclideanSpace ℝ κ)
    (h : ∀ s ∈ S, ∀ s' ∈ S, ⟪w s, w s'⟫ = ⟪x₀ s, x₀ s'⟫) :
    ∃ (d : ℕ) (ι : EuclideanSpace ℝ (Fin d₁) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
      (J : EuclideanSpace ℝ κ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)), ∀ s ∈ S, ι (w s) = J (x₀ s) := by
  classical
  let u : S → EuclideanSpace ℝ (Fin d₁ ⊕ κ) := fun s => sumInl (w s)
  let v : S → EuclideanSpace ℝ (Fin d₁ ⊕ κ) := fun s => sumInr (x₀ s)
  have huv : ∀ i j, ⟪u i, u j⟫ = ⟪v i, v j⟫ := by
    intro i j
    simp only [u, v, LinearIsometry.inner_map_map]
    exact h i i.2 j j.2
  obtain ⟨L, hL⟩ := exists_linearIsometry_of_gram u v huv
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (Fin d₁ ⊕ κ))
  refine ⟨Fintype.card (Fin d₁ ⊕ κ), e.toLinearIsometry.comp (L.comp sumInl),
    e.toLinearIsometry.comp sumInr, fun s hs => ?_⟩
  have := hL ⟨s, hs⟩
  simp only [LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [show sumInl (w s) = u ⟨s, hs⟩ from rfl, this]

end LQGDimension.Coupling
