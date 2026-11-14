import LatticeProb.Euclidean.ParentBlockSeparation
import LatticeProb.Prob.MeasurableCoverSelector

/-!
# Measurable selection of squares for parent-block exits

A countable cover by squares yields a measurable selector on the Euclidean state space.  The
selector stops outside a prescribed outer parent block and each selected exit domain contains the
current point.
-/

set_option autoImplicit false

open MeasureTheory Set Metric

namespace LatticeProb.ParentBlock

/-- Select a square containing the current Euclidean point while it lies in the outer parent
block. The point lies in the interior of the selected square's parent block. -/
theorem exists_measurable_parentBlock_selector [MeasurableSpace (Option ℕ)]
    (c : ℂ) {S s : ℝ} (hS : 0 ≤ S) (hs : 0 < s) (centres : ℕ → ℂ)
    (hcover : parentBlock c S ⊆ ⋃ n, closedSquare (centres n) s) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Option ℕ, Measurable f ∧
      (∀ x n, f x = some n →
        Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ closedSquare (centres n) s ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ interior (parentBlock (centres n) s)) ∧
      (∀ x, f x = none ↔ Complex.orthonormalBasisOneI.repr.symm x ∉ parentBlock c S) := by
  have hC : MeasurableSet (parentBlock c S) := by
    rw [parentBlock_eq hS]
    exact (isClosed_closedSquare c (3 * S)).measurableSet
  obtain ⟨g, hg, hsome, _, hnone⟩ :=
    exists_measurable_cover_selector (parentBlock c S) (fun n => closedSquare (centres n) s)
      hC (fun n => (isClosed_closedSquare (centres n) s).measurableSet) hcover
  refine ⟨fun x => g (Complex.orthonormalBasisOneI.repr.symm x),
    hg.comp Complex.orthonormalBasisOneI.repr.symm.continuous.measurable, ?_, ?_⟩
  · intro x n hx
    obtain ⟨hout, hin⟩ := hsome _ _ hx
    refine ⟨hout, hin, ball_subset_interior_parentBlock hs.le hin ?_⟩
    simpa only [mem_ball, dist_self] using hs
  · intro x
    exact hnone _

end LatticeProb.ParentBlock
