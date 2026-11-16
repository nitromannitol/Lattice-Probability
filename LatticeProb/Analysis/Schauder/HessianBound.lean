import LatticeProb.Analysis.Schauder.HessianEntryBound
import LatticeProb.Analysis.Schauder.BilinearEntryBound
import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
Ported from the Lattice-High-Contrast-Homogenization development, module `LatticeHC.Support.Heat.HessianBound`.

# A Schauder-free Hessian bound on `ℝ^d`

The interior Schauder estimate (GT01, Theorem 4.6) is replaced by a direct bound for the Hessian of
a smooth bounded function in terms of its sup norm and the sup norm of the gradient of its
Laplacian.  The pointwise bound for a second directional derivative in unit directions is
`abs_dirDeriv_dirDeriv_le_of_bounded`; here it is applied to the standard basis vectors, and the
operator norm of the Hessian is dominated by the sum of the absolute values of its entries.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- **A Schauder-free Hessian bound on `ℝ^d`.** There is `C(d)` such that every `C⁴` function `v`
with bounded derivatives, `|v| ≤ A` and `‖∇Δv‖ ≤ B` has `‖D²v‖ ≤ C (A + B)` everywhere. -/
theorem exists_norm_iteratedFDeriv_two_le_of_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Euc d → ℝ) (A B : ℝ), BoundedDerivs 4 v →
      (∀ y, |v y| ≤ A) → (∀ y, ‖fderiv ℝ (laplacianSum v) y‖ ≤ B) →
      ∀ x, ‖iteratedFDeriv ℝ 2 v x‖ ≤ C * (A + B) := by
  refine ⟨(d : ℝ) ^ 2 * (2 * 2 ^ ((d : ℝ) / 2) + 1), by positivity, ?_⟩
  intro v A B hv hvA hvB x
  have hA : 0 ≤ A := (abs_nonneg _).trans (hvA x)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hvB x)
  have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hv2 : ContDiff ℝ 2 v := hv.1.of_le (by norm_num)
  have hentry : ∀ j k : Fin d,
      |iteratedFDeriv ℝ 2 v x ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| ≤
        (2 * 2 ^ ((d : ℝ) / 2) + 1) * (A + B) := by
    intro j k
    rw [iteratedFDeriv_two_apply_eq_dirDeriv hv2]
    have h := abs_dirDeriv_dirDeriv_le_of_bounded hv hvA hvB x (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1) (by simp) (by simp)
    refine h.trans ?_
    nlinarith [mul_nonneg hc hA, mul_nonneg hc hB]
  calc ‖iteratedFDeriv ℝ 2 v x‖
      ≤ ∑ j : Fin d, ∑ k : Fin d,
        |iteratedFDeriv ℝ 2 v x ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]| :=
        norm_le_sum_abs_apply_single _
    _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, (2 * 2 ^ ((d : ℝ) / 2) + 1) * (A + B) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
    _ = (d : ℝ) ^ 2 * (2 * 2 ^ ((d : ℝ) / 2) + 1) * (A + B) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

end LatticeProb.Analysis.Schauder
