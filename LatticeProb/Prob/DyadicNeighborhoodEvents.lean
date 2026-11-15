import LatticeProb.Prob.ParentBlockDyadicFiniteSelector
import LatticeProb.Prob.SelectedNeighborhoodMeasurable

/-! # Measurable events for selected dyadic neighborhoods -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb.ParentBlock

/-- Failure to share a selected dyadic parent-block interior is measurable. -/
theorem measurableSet_not_common_selected_dyadic_neighborhood
    (c : ℂ) (S : ℝ) (n : ℕ)
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentDyadicIndex n))]
    (f : EuclideanSpace ℝ (Fin 2) → Option (ParentDyadicIndex n))
    (hf : Measurable f) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) |
      ¬ ∃ i, f p.1 = some i ∧ f p.2 = some i ∧
        p.1 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n))) ∧
        p.2 ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n)))} := by
  apply measurableSet_not_common_selected_neighborhood f hf
  intro i
  exact (isOpen_interior.preimage Complex.orthonormalBasisOneI.repr.symm.continuous).measurableSet

/-- The same failure event is measurable for a pair of measurable endpoints. -/
theorem measurableSet_not_common_selected_dyadic_neighborhood_of_pair
    {Ω : Type*} [MeasurableSpace Ω] (c : ℂ) (S : ℝ) (n : ℕ)
    [MeasurableSpace (Option (ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (ParentDyadicIndex n))]
    (f : EuclideanSpace ℝ (Fin 2) → Option (ParentDyadicIndex n))
    (hf : Measurable f) (x y : Ω → EuclideanSpace ℝ (Fin 2))
    (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {ω | ¬ ∃ i, f (x ω) = some i ∧ f (y ω) = some i ∧
      x ω ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n))) ∧
      y ω ∈ (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (parentBlock (parentDyadicCentre c S n i) (2 * S / (2 : ℝ) ^ n)))} :=
  (measurableSet_not_common_selected_dyadic_neighborhood c S n f hf).preimage (hx.prodMk hy)

end LatticeProb.ParentBlock
