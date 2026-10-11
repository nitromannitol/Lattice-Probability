/-
# Domination of finite nested projection determinantal laws

Compatible orthonormal frames are constructed from symmetric idempotent kernels
with nested ranges. The original inclusion identities identify their endpoint
atoms; squared determinant comparison gives event domination, and finite-poset
transport produces a coupling with the literal original marginals.
-/
import LatticeProb.Prob.DPP.EndpointDomination
import LatticeProb.LinearAlgebra.NestedProjectionFrame


namespace LatticeProb.DPP
open scoped BigOperators Classical
open LatticeProb.SubsetContraction
noncomputable section

/-- **Finite nested projection determinantal domination.** Increasing events
and a subset-supported coupling of the original nonnegative laws follow from
nested real orthogonal projections and their all-subset inclusion identities.
This is the finite real form of Lyons (2003), Theorem 6.2, with the finite
monotone-coupling consequence proved from source-derived normalization. -/
theorem nested_projection_domination
    {E : Type*} [Fintype E] [DecidableEq E]
    (Q₁ Q₂ : Matrix E E ℝ)
    (hQ₁s : Q₁.IsSymm) (hQ₁i : Q₁ * Q₁ = Q₁)
    (hQ₂s : Q₂.IsSymm) (hQ₂i : Q₂ * Q₂ = Q₂)
    (hle : LinearMap.range Q₁.mulVecLin ≤ LinearMap.range Q₂.mulVecLin)
    (p₁ p₂ : Finset E → ℝ) (hp₁ : ∀ S, 0 ≤ p₁ S) (hp₂ : ∀ S, 0 ≤ p₂ S)
    (hdet₁ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₁ S =
      (Q₁.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (hdet₂ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₂ S =
      (Q₂.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    (∀ ev : Set (Finset E), (∀ S ∈ ev, ∀ e : E, insert e S ∈ ev) →
      ∑ S, Set.indicator ev p₁ S ≤ ∑ S, Set.indicator ev p₂ S) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = p₁ S) ∧
      (∀ T, ∑ S, q S T = p₂ T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, ¬ S ⊆ T → q S T = 0)) := by
  obtain ⟨k, m, W, hW, hWQ₂, hWQ₁⟩ :=
    LatticeProb.ProjectionFiltration.exists_nested_projection_frame Q₁ Q₂
      hQ₁s hQ₁i hQ₂s hQ₂i hle
  let e := Fintype.equivFin E
  let U : Matrix (Fin (Fintype.card E)) (Fin (k + m)) ℝ := W.submatrix e.symm id
  let V : Matrix E (Fin k) ℝ :=
    W.submatrix id (fun j => ⟨m + j.val, by omega⟩)
  have hU : U.transpose * U = 1 := (transpose_mul_equivFin_frame W).trans hW
  have hVQ₁ : V * V.transpose = Q₁ := hWQ₁
  have hQ₁ : Q₁ =
      (dropLeadingColumns U * (dropLeadingColumns U).transpose).submatrix e e := by
    rw [← hVQ₁]
    ext i j
    change (∑ l : Fin k, W i ⟨m + l.val, by omega⟩ * W j ⟨m + l.val, by omega⟩) =
      ∑ l : Fin k, W (e.symm (e i)) ⟨m + l.val, by omega⟩ *
        W (e.symm (e j)) ⟨m + l.val, by omega⟩
    rw [e.symm_apply_apply, e.symm_apply_apply]
  have hQ₂ : Q₂ = (U * U.transpose).submatrix e e := by
    rw [← hWQ₂]
    ext i j
    change (∑ l, W i l * W j l) =
      ∑ l, W (e.symm (e i)) l * W (e.symm (e j)) l
    rw [e.symm_apply_apply, e.symm_apply_apply]
  exact domination_coupling_of_endpoint_frames Q₁ Q₂ U hU hQ₁ hQ₂
    p₁ p₂ hp₁ hp₂ hdet₁ hdet₂

end
end LatticeProb.DPP
