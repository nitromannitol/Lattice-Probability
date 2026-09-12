import LatticeProb.Support.ContSums

/-!
# The ℓ²-to-ℓ^p comparison

Two elementary inequalities requested by the sandpile repository: the
coordinate bound `|c j| ≤ ‖c‖₂`.
-/

namespace LatticeProb

/-- Each coordinate is at most the ℓ² norm. -/
theorem abs_le_l2norm {N : ℕ} (c : Fin N → ℝ) (i : Fin N) :
    |c i| ≤ Real.sqrt (∑ i, c i ^ 2) := by
  have h2 : c i ^ 2 ≤ ∑ i, c i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (c i)) (Finset.mem_univ i)
  have h3 : |c i| ≤ Real.sqrt (c i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
  exact le_trans h3 (Real.sqrt_le_sqrt h2)

end LatticeProb
