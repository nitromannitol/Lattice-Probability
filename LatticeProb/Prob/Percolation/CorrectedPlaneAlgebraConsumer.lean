import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra

/-!
# Affine corrected planes on the fully open two-dimensional lattice

The existing coordinate planes and constant plane combine to give the function
x₀ - 2x₁ + c on the actual infinite all-open component. Its values at the origin
and the two coordinate unit vertices certify a nonconstant function on a nonempty domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

noncomputable section

/-- The actual all-open coordinate planes combine with a constant plane to give
the affine function with slope (1, -2), for every real constant. -/
theorem allOpen_two_isCorrectedPlane_affine (c : ℝ) :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    IsCorrectedPlane C (Pi.single 0 1 - (2 : ℝ) • Pi.single 1 1)
      (fun x => (x.val 0 : ℝ) - 2 * (x.val 1 : ℝ) + c) := by
  dsimp only
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
  have hfirst := allOpen_isCorrectedPlane_coordinate 2 0
  have hsecond := isCorrectedPlane_smul C (allOpen_isCorrectedPlane_coordinate 2 1) 2
  have haffine := isCorrectedPlane_add C (isCorrectedPlane_sub C hfirst hsecond)
    (isCorrectedPlane_const C c)
  simpa only [add_zero, Pi.add_def, Pi.sub_def, Pi.smul_def, smul_eq_mul] using haffine

/-- Literal values at actual all-open component vertices show that the affine
corrected plane is nonconstant; no vertex membership is assumed. -/
theorem allOpen_two_nonconstant_affine_correctedPlane (c : ℝ) :
    let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
    let u : C → ℝ := fun x => (x.val 0 : ℝ) - 2 * (x.val 1 : ℝ) + c
    IsCorrectedPlane C (Pi.single 0 1 - (2 : ℝ) • Pi.single 1 1) u ∧
      ∃ x y z : C, x.val = 0 ∧ y.val = unit 0 ∧ z.val = unit 1 ∧
        u x = c ∧ u y = c + 1 ∧ u z = c - 2 ∧ u x ≠ u y := by
  dsimp only
  let C := uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)
  have hzero : (0 : Vertex 2) ∈ C.supp := by
    change (0 : Vertex 2) ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  have hunit (i : Fin 2) : unit i ∈ C.supp := by
    change unit i ∈
      (uniqueInfiniteComponent (allOpen_hasUniqueInfiniteOpenComponent 2)).supp
    rw [uniqueInfiniteComponent_allOpen_supp]
    trivial
  refine ⟨allOpen_two_isCorrectedPlane_affine c, ⟨0, hzero⟩,
    ⟨unit 0, hunit 0⟩, ⟨unit 1, hunit 1⟩, rfl, rfl, rfl, ?_⟩
  norm_num [unit, Pi.single_apply]
  constructor <;> ring

end

end LatticeProb.Percolation
