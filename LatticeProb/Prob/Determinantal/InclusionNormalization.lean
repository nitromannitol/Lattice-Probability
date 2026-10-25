module

/- # Normalization of finite inclusion-minor laws

Apply the inclusion identity to the empty subset; its determinant is one.
-/

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Real.Basic

@[expose] public section



open scoped BigOperators

namespace LatticeProb.DPP

/-- **Inclusion-minor normalization.** The empty inclusion minor normalizes the original finite-set weights. -/
theorem sum_eq_one_of_inclusion_minors {E : Type*} [Fintype E] [DecidableEq E]
    (Q : Matrix E E ℝ) (p : Finset E → ℝ)
    (hdet : ∀ A : Finset E, ∑ S, Set.indicator {S : Finset E | A ⊆ S} p S =
      (Q.submatrix (fun a : A => (a : E)) (fun a : A => (a : E))).det) :
    ∑ S, p S = 1 := by
  calc
    ∑ S, p S = ∑ S, Set.indicator {S : Finset E | (∅ : Finset E) ⊆ S} p S :=
      Finset.sum_congr rfl fun S _ =>
        (Set.indicator_of_mem (show S ∈ {S : Finset E | (∅ : Finset E) ⊆ S} from
          Finset.empty_subset S) p).symm
    _ = (Q.submatrix (fun a : (∅ : Finset E) => (a : E))
        (fun a : (∅ : Finset E) => (a : E))).det := hdet ∅
    _ = 1 := Matrix.det_isEmpty

end LatticeProb.DPP
