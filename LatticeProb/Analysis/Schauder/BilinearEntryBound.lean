import LatticeProb.Analysis.Schauder.Continuum

/-!
# Operator norm of a bilinear form from its entries

The operator norm of a continuous bilinear form on `ℝ^d` is at most the sum of the absolute values
of its entries `M (e_j, e_k)` in the standard basis. This reduces a Hessian bound for a
function on `ℝ^d` to bounds on the scalar second partial derivatives.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- A vector of `ℝ^d` is the sum of its coordinates times the standard basis vectors. -/
theorem euc_eq_sum_smul_single (x : Euc d) :
    x = ∑ j : Fin d, x j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
  ext i
  simp [Pi.single_apply]

/-- A continuous bilinear form on `ℝ^d` expands over the standard basis:
`M (x, y) = ∑ j k, x_j y_k M (e_j, e_k)`. -/
theorem apply_eq_sum_apply_single
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) (m : Fin 2 → Euc d) :
    M m = ∑ j : Fin d, ∑ k : Fin d,
      (m 0 j * m 1 k) * M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] := by
  have hm : m = fun i => ∑ j : Fin d, m i j • (EuclideanSpace.single j (1 : ℝ) : Euc d) :=
    funext fun i => euc_eq_sum_smul_single (m i)
  conv_lhs => rw [hm]
  rw [ContinuousMultilinearMap.map_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin d) _ _ fun r => ?_
  have hv : (fun i : Fin 2 => (EuclideanSpace.single (r i) (1 : ℝ) : Euc d))
      = ![EuclideanSpace.single (r 0) 1, EuclideanSpace.single (r 1) 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ContinuousMultilinearMap.map_smul_univ, hv, Fin.prod_univ_two, smul_eq_mul]
  rfl

/-- The operator norm of a continuous bilinear form on `ℝ^d` is at most the sum of the absolute
values of its entries in the standard basis. -/
theorem norm_le_sum_abs_apply_single
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) :
    ‖M‖ ≤ ∑ j : Fin d, ∑ k : Fin d,
      |M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _) fun m => ?_
  rw [apply_eq_sum_apply_single M m, Fin.prod_univ_two]
  calc ‖∑ j : Fin d, ∑ k : Fin d,
        (m 0 j * m 1 k) * M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]‖
      ≤ ∑ j : Fin d, ∑ k : Fin d,
        ‖(m 0 j * m 1 k) * M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin d, ∑ k : Fin d,
        (‖m 0‖ * ‖m 1‖) * |M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_mul, Real.norm_eq_abs (M _)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (PiLp.norm_apply_le (m 0) j) (PiLp.norm_apply_le (m 1) k)
            (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)
    _ = (∑ j : Fin d, ∑ k : Fin d,
          |M ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]|) * (‖m 0‖ * ‖m 1‖) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end

end LatticeProb.Analysis.Schauder
