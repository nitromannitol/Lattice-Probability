import LatticeProb.Analysis.Elliptic.WeakDirichletAlgebra

/-!
# Energy of homogeneous weak solutions

The energy identity forces the gradient of a homogeneous weak solution to vanish.
If the mass coefficient is positive, the solution itself also vanishes.
-/

namespace LatticeProb.Elliptic.WeakDirichlet

open scoped BigOperators

/-- A homogeneous weak solution has zero gradient coordinates. -/
theorem IsWeakSolution.grad_eq_zero_of_homogeneous {d : ℕ} {U : Set (Fin d → ℝ)}
    {μ a₀ : ℝ} (hμ : 0 ≤ μ) (ha₀ : 0 < a₀)
    (u : H10 U) (hu : IsWeakSolution U μ a₀ (fun _ => 0) u) :
    ∀ i : Fin d, u.val i.succ = 0 := by
  have he := hu.energyPair_eq_zero μ a₀ u u
  simp only [energyPair, real_inner_self_eq_norm_sq] at he
  have hs : 0 ≤ ∑ i : Fin d, ‖u.val i.succ‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm : 0 ≤ μ * ‖u.val 0‖ ^ 2 := mul_nonneg hμ (sq_nonneg _)
  have hsum : (∑ i : Fin d, ‖u.val i.succ‖ ^ 2) = 0 := by
    nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => sq_nonneg ‖u.val i.succ‖)).mp hsum i (Finset.mem_univ i)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- A homogeneous weak solution with positive mass is zero. -/
theorem IsWeakSolution.val_eq_zero_of_pos {d : ℕ} {U : Set (Fin d → ℝ)}
    {μ a₀ : ℝ} (hμ : 0 < μ) (ha₀ : 0 < a₀)
    (u : H10 U) (hu : IsWeakSolution U μ a₀ (fun _ => 0) u) : u.val = 0 := by
  have hg := hu.grad_eq_zero_of_homogeneous hμ.le ha₀ u
  have he := hu.energyPair_eq_zero μ a₀ u u
  simp only [energyPair, real_inner_self_eq_norm_sq] at he
  have hs : 0 ≤ ∑ i : Fin d, ‖u.val i.succ‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : ‖u.val 0‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖u.val 0‖]
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact norm_eq_zero.mp (sq_eq_zero_iff.mp hmass)
  · exact hg i

end LatticeProb.Elliptic.WeakDirichlet
