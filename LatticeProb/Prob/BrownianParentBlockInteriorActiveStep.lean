import LatticeProb.Prob.BrownianActiveClockExit
import LatticeProb.Prob.BrownianActiveClockInterval
import LatticeProb.Euclidean.ParentBlockDiameter

/-! # Parent-block geometry for active steps from interior points -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- An active finite selected step exits its parent-block interior, and the path
through the exit stays within six side lengths of its initial point. -/
theorem brownianSkeletonClock_active_parentBlock_interior_step {J : Type*}
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (n : ℕ) (ω : BrownianPath 2)
    (hactive : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector (n + 1) ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let τ := fun k => (brownianSkeletonClock U z j₀ selector k ω).2.toNNReal
    ∃ j, selector (n + 1) (z + ω (τ n)) = some j ∧
      Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n)) ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n)) ∈
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s) ∧
      Complex.orthonormalBasisOneI.repr.symm (z + ω (τ (n + 1))) ∉
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s) ∧
      ∀ t ∈ Icc (τ n) (τ (n + 1)),
        ‖Complex.orthonormalBasisOneI.repr.symm (z + ω t) -
          Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n))‖ ≤ 6 * s := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  have hU : ∀ j, IsOpen (U j) := fun j => isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hstart : ∀ k x j, selector k x = some j → x ∈ U j := by
    intro k x j h
    exact (hselector k x j h).2
  obtain ⟨j, hj, hout⟩ := brownianSkeletonClock_active_step_exit U hU z j₀ selector n ω hactive hfinite
  obtain ⟨i, hi, hint⟩ := brownianSkeletonClock_active_step_interval U hU z j₀ selector hstart n ω hactive hfinite
  have hij : i = j := Option.some.inj (hi.symm.trans hj)
  subst i
  refine ⟨j, hj, (hselector _ _ _ hj).1, (hselector _ _ _ hj).2, hout, ?_⟩
  intro t ht
  have hclosed : IsClosed (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock (centres j) s) := by
    have hc : IsClosed (LatticeProb.ParentBlock.parentBlock (centres j) s) := by
      rw [LatticeProb.ParentBlock.parentBlock_eq hs.le]
      exact LatticeProb.ParentBlock.isClosed_closedSquare _ _
    exact hc.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hsub : U j ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock (centres j) s := by
    intro x hx
    change Complex.orthonormalBasisOneI.repr.symm x ∈
      LatticeProb.ParentBlock.parentBlock (centres j) s
    exact interior_subset hx
  have hmem := closure_minimal hsub hclosed (hint t ht)
  exact LatticeProb.ParentBlock.norm_sub_le_six_mul_of_mem_parentBlock hs.le
    (interior_subset (hselector _ _ _ hj).2) hmem

end BouRabeeGwynne
