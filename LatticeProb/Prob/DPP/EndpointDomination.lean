/-
# Projection-law domination from compatible endpoint frames

The original inclusion laws identify endpoint atoms with squared ordered
determinants. Carrier transport and repeated column deletion give event
domination; normalization from the empty minor gives the literal atom coupling.
-/
import LatticeProb.Prob.DPP.EventTransport
import LatticeProb.LinearAlgebra.DeterminantEndpointComparison
import LatticeProb.Prob.Strassen.FiniteSet


namespace LatticeProb.DPP
open scoped BigOperators Classical
open LatticeProb.SubsetContraction
noncomputable section

/-- Deleting leading columns of an orthonormal frame preserves orthonormality. -/
theorem dropLeadingColumns_orthonormal {n k m : ℕ}
    (U : Matrix (Fin n) (Fin (k + m)) ℝ) (hU : U.transpose * U = 1) :
    (dropLeadingColumns U).transpose * dropLeadingColumns U = 1 := by
  let f : Fin k → Fin (k + m) := fun j => ⟨m + j.val, by omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    exact Nat.add_left_cancel h
  have h : (U.transpose * U).submatrix f f = 1 := by
    rw [hU, Matrix.submatrix_one _ hf]
  rw [← Matrix.submatrix_mul_equiv U.transpose U f (Equiv.refl (Fin n)) f] at h
  exact h

/-- Original-carrier event mass equals the event-masked squared coordinate
coefficients after transport along the ground-set equivalence. -/
theorem event_mass_eq_coordinate_energy
    {E : Type*} [Fintype E] [DecidableEq E] {n k : ℕ}
    (e : Fin n ≃ E) (V : Matrix (Fin n) (Fin k) ℝ) (hV : V.transpose * V = 1)
    (p : Finset E → ℝ) (hp : ∀ S, 0 ≤ p S)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      (((V * V.transpose).submatrix e.symm e.symm).submatrix
        (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (ev : Set (Finset E)) :
    (∑ S, Set.indicator ev p S) =
      ∑ S, Set.indicator (e.finsetCongr ⁻¹' ev) (fun S => determinantCoeff V S ^ 2) S := by
  rw [← sum_indicator_finsetCongr e p ev]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ∈ e.finsetCongr ⁻¹' ev
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS]
    exact atom_finsetCongr_eq_determinantCoeff_sq e V hV p hp hdet S
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS]

/-- **Endpoint-frame event domination.** Actual nonnegative inclusion laws
on an arbitrary finite carrier are dominated when their kernels are represented
by an orthonormal frame and its trailing columns. This internal theorem keeps
the geometric representation premises explicit. -/
theorem event_domination_of_endpoint_frames
    {E : Type*} [Fintype E] [DecidableEq E] {k m : ℕ}
    (Q₁ Q₂ : Matrix E E ℝ)
    (U : Matrix (Fin (Fintype.card E)) (Fin (k + m)) ℝ)
    (hU : U.transpose * U = 1)
    (hQ₁ : Q₁ = ((dropLeadingColumns U) * (dropLeadingColumns U).transpose).submatrix
      (Fintype.equivFin E) (Fintype.equivFin E))
    (hQ₂ : Q₂ = (U * U.transpose).submatrix (Fintype.equivFin E) (Fintype.equivFin E))
    (p₁ p₂ : Finset E → ℝ) (hp₁ : ∀ S, 0 ≤ p₁ S) (hp₂ : ∀ S, 0 ≤ p₂ S)
    (hdet₁ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₁ S =
      (Q₁.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (hdet₂ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₂ S =
      (Q₂.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    ∀ ev : Set (Finset E), (∀ S ∈ ev, ∀ i : E, insert i S ∈ ev) →
      ∑ S, Set.indicator ev p₁ S ≤ ∑ S, Set.indicator ev p₂ S := by
  intro ev hev
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  have hdetV : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₁ S =
      (((dropLeadingColumns U * (dropLeadingColumns U).transpose).submatrix e.symm e.symm).submatrix
        (fun a : A => (a : E)) (fun a : A => (a : E))).det := by
    intro A
    have h := hdet₁ A
    rw [hQ₁] at h
    exact h
  have hdetU : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₂ S =
      (((U * U.transpose).submatrix e.symm e.symm).submatrix
        (fun a : A => (a : E)) (fun a : A => (a : E))).det := by
    intro A
    have h := hdet₂ A
    rw [hQ₂] at h
    exact h
  rw [event_mass_eq_coordinate_energy e (dropLeadingColumns U)
    (dropLeadingColumns_orthonormal U hU) p₁ hp₁ hdetV ev,
    event_mass_eq_coordinate_energy e U hU p₂ hp₂ hdetU ev]
  exact sum_indicator_determinantCoeff_sq_dropLeadingColumns_le U hU
    (e.finsetCongr ⁻¹' ev) (insertion_closed_preimage_finsetCongr e ev hev)

/-- **Endpoint-frame domination and coupling.** The two original inclusion
laws produce event domination and a nonnegative subset-supported coupling with
both exact marginals and total mass one. The frame representation is an explicit
internal geometric prerequisite, not an additional premise of Lyons's theorem. -/
theorem domination_coupling_of_endpoint_frames
    {E : Type*} [Fintype E] [DecidableEq E] {k m : ℕ}
    (Q₁ Q₂ : Matrix E E ℝ)
    (U : Matrix (Fin (Fintype.card E)) (Fin (k + m)) ℝ)
    (hU : U.transpose * U = 1)
    (hQ₁ : Q₁ = ((dropLeadingColumns U) * (dropLeadingColumns U).transpose).submatrix
      (Fintype.equivFin E) (Fintype.equivFin E))
    (hQ₂ : Q₂ = (U * U.transpose).submatrix (Fintype.equivFin E) (Fintype.equivFin E))
    (p₁ p₂ : Finset E → ℝ) (hp₁ : ∀ S, 0 ≤ p₁ S) (hp₂ : ∀ S, 0 ≤ p₂ S)
    (hdet₁ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₁ S =
      (Q₁.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det)
    (hdet₂ : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p₂ S =
      (Q₂.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    (∀ ev : Set (Finset E), (∀ S ∈ ev, ∀ i : E, insert i S ∈ ev) →
      ∑ S, Set.indicator ev p₁ S ≤ ∑ S, Set.indicator ev p₂ S) ∧
    (∃ q : Finset E → Finset E → ℝ,
      (∀ S T, 0 ≤ q S T) ∧
      (∀ S, ∑ T, q S T = p₁ S) ∧
      (∀ T, ∑ S, q S T = p₂ T) ∧
      (∑ S, ∑ T, q S T) = 1 ∧
      (∀ S T, ¬ S ⊆ T → q S T = 0)) := by
  have hdom := event_domination_of_endpoint_frames Q₁ Q₂ U hU hQ₁ hQ₂
    p₁ p₂ hp₁ hp₂ hdet₁ hdet₂
  exact ⟨hdom, LatticeProb.StrassenAux.exists_subset_matrix_of_event_domination
    p₁ p₂ hp₁ hp₂ (LatticeProb.DPP.sum_eq_one_of_inclusion_minors Q₁ p₁ hdet₁)
    (LatticeProb.DPP.sum_eq_one_of_inclusion_minors Q₂ p₂ hdet₂) hdom⟩

end
end LatticeProb.DPP
