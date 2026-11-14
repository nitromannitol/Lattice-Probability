import LatticeProb.Prob.ParentBlockDyadicSelector

/-!
# Finite dyadic selection with a uniform margin

A measurable selector among the finite family of dyadic descendants has a uniform ball inside
its selected parent-block interior.
-/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb.ParentBlock

/-- Select a finite dyadic index while in the outer parent block, with a ball of radius equal to
    the descendant side length contained in the selected exit domain. -/
theorem exists_measurable_finite_dyadic_selector_margin
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option ℕ)] [MeasurableSingletonClass (Option ℕ)]
    [MeasurableSpace (Option (ParentDyadicIndex n))] :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Option (ParentDyadicIndex n), Measurable f ∧
      (∀ x p, f x = some p →
        Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          closedSquare (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n) ∧
        ball x (2 * S / (2 : ℝ) ^ n) ⊆
          (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (parentBlock (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n)))) ∧
      (∀ x, f x = none ↔ Complex.orthonormalBasisOneI.repr.symm x ∉ parentBlock c S) := by
  let e := parentDyadicEnumeration n
  obtain ⟨g, hg, hsome, hnone⟩ :=
    exists_measurable_parentBlock_dyadic_selector c hS n e
      (parentDyadicEnumeration_surjective n)
  refine ⟨fun x => (g x).map e, (measurable_of_countable (fun a : Option ℕ => a.map e)).comp hg, ?_, ?_⟩
  · intro x p hp
    cases h : g x with
    | none => simp [h] at hp
    | some k =>
      have he : e k = p := by simpa [h] using hp
      obtain ⟨hout, hin, _, _⟩ := hsome x k h
      rw [parentDyadicSubsquare_eq_closedSquare, he] at hin
      refine ⟨hout, hin, ?_⟩
      intro y hy
      apply ball_subset_interior_parentBlock (by positivity) hin
      rw [mem_ball] at hy ⊢
      simpa only [Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq] using hy
  · intro x
    simpa using hnone x

end LatticeProb.ParentBlock
