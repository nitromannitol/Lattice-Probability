/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetReal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalGaussianTail

 

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistLocalGaussianBudgetReal
    (ξ Q ζ L β T C Clam lam : ℝ) (n k₀ : ℕ) : ℝ :=
  let p (k : ℕ) : ℝ := (2 : ℝ) ^
    (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))
  let b (k : ℕ) : ℝ := 2 * T ^ 2 * Real.exp L * p k * lam
  let ell (k : ℕ) : ℝ := C * T ^ 2 * Real.exp L * p k * lam
  let term : ℝ := Clam * T ^ 2 * lam * Real.exp L * p n
  let arm : ℝ := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  term + arm + (b k₀ + ell k₀ + b k₀) + arm + term

theorem pt_dist_local_gaussian_budget_eq_ofReal
    (ξ Q ζ L β T C Clam lam : ℝ) (n k₀ : ℕ)
    (hC : 0 ≤ C) (hClam : 0 ≤ Clam) (hlam : 0 ≤ lam) :
    ptDistLocalGaussianBudget ξ Q ζ L β T C Clam lam n k₀ =
      ENNReal.ofReal (ptDistLocalGaussianBudgetReal ξ Q ζ L β T C Clam lam n k₀) := by
  let p (k : ℕ) : ℝ := (2 : ℝ) ^
    (-(ξ * Q - 3 * ζ - 2 * β) * (k : ℝ))
  let b (k : ℕ) : ℝ := 2 * T ^ 2 * Real.exp L * p k * lam
  let ell (k : ℕ) : ℝ := C * T ^ 2 * Real.exp L * p k * lam
  let term : ℝ := Clam * T ^ 2 * lam * Real.exp L * p n
  let arm : ℝ := ∑ j ∈ Finset.range (n - k₀),
    (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j))
  have hb (k : ℕ) : 0 ≤ b k := by dsimp [b, p]; positivity
  have he (k : ℕ) : 0 ≤ ell k := by dsimp [ell, p]; positivity
  have ht : 0 ≤ term := by dsimp [term, p]; positivity
  have ha : 0 ≤ arm := by
    dsimp [arm]
    exact Finset.sum_nonneg fun j hj =>
      add_nonneg (add_nonneg (hb _) (he _)) (hb _)
  have hitem (j : ℕ) :
      ENNReal.ofReal (b (k₀ + (j + 1))) +
        ENNReal.ofReal (ell (k₀ + (j + 1))) +
        ENNReal.ofReal (b (k₀ + j)) =
      ENNReal.ofReal
        (b (k₀ + (j + 1)) + ell (k₀ + (j + 1)) + b (k₀ + j)) := by
    rw [← ENNReal.ofReal_add (hb _) (he _),
      ← ENNReal.ofReal_add (add_nonneg (hb _) (he _)) (hb _)]
  have harm :
      (∑ j ∈ Finset.range (n - k₀),
        (ENNReal.ofReal (b (k₀ + (j + 1))) +
          ENNReal.ofReal (ell (k₀ + (j + 1))) +
          ENNReal.ofReal (b (k₀ + j)))) = ENNReal.ofReal arm := by
    simp_rw [hitem]
    exact (ENNReal.ofReal_sum_of_nonneg
      (fun j hj => add_nonneg (add_nonneg (hb _) (he _)) (hb _))).symm
  change ENNReal.ofReal term +
      (∑ j ∈ Finset.range (n - k₀),
        (ENNReal.ofReal (b (k₀ + (j + 1))) +
          ENNReal.ofReal (ell (k₀ + (j + 1))) +
          ENNReal.ofReal (b (k₀ + j)))) +
      (ENNReal.ofReal (b k₀) + ENNReal.ofReal (ell k₀) +
        ENNReal.ofReal (b k₀)) +
      (∑ j ∈ Finset.range (n - k₀),
        (ENNReal.ofReal (b (k₀ + (j + 1))) +
          ENNReal.ofReal (ell (k₀ + (j + 1))) +
          ENNReal.ofReal (b (k₀ + j)))) +
      ENNReal.ofReal term =
    ENNReal.ofReal (term + arm + (b k₀ + ell k₀ + b k₀) + arm + term)
  rw [harm]
  have hbridge : 0 ≤ b k₀ + ell k₀ + b k₀ :=
    add_nonneg (add_nonneg (hb _) (he _)) (hb _)
  rw [← ENNReal.ofReal_add (hb k₀) (he k₀),
    ← ENNReal.ofReal_add (add_nonneg (hb k₀) (he k₀)) (hb k₀)]
  rw [← ENNReal.ofReal_add ht ha,
    ← ENNReal.ofReal_add (add_nonneg ht ha) hbridge,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg ht ha) hbridge) ha,
    ← ENNReal.ofReal_add
      (add_nonneg (add_nonneg (add_nonneg ht ha) hbridge) ha) ht]

end SupercriticalLQGUniqueness.B2.DG20Pt
