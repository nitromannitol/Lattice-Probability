import LatticeProb.Prob.ParentBlockDyadicFiniteSelector
import LatticeProb.Prob.BrownianOuterExitStoppedKnots

/-!
# Dyadic parent-block knots at the outer exit

A finite dyadic selector supplies the hypotheses for the stopped-knot construction.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A finite dyadic selector gives stopped knots at the exit from the outer parent block. -/
theorem brownianSkeletonClock_dyadic_outerExit_stopped_knots
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    [MeasurableSpace (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
    [MeasurableSingletonClass (Option (LatticeProb.ParentBlock.ParentDyadicIndex n))]
    (f : Euc 2 → Option (LatticeProb.ParentBlock.ParentDyadicIndex n))
    (hsome : ∀ x j, f x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ LatticeProb.ParentBlock.parentBlock c S ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
    (hnone : ∀ x, f x = none →
      Complex.orthonormalBasisOneI.repr.symm x ∉ LatticeProb.ParentBlock.parentBlock c S)
    (z : Euc 2) (j₀ : LatticeProb.ParentBlock.ParentDyadicIndex n)
    (hz : f z = some j₀) (K : ℕ) (ω : BrownianPath 2) (hzero : ω 0 = 0)
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
      z j₀ (fun _ => f) K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock
          (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n)))
      z j₀ (fun _ => f) K ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock
        (LatticeProb.ParentBlock.parentDyadicCentre c S n j) (2 * S / (2 : ℝ) ^ n))
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ (fun _ => f) m ω).2.toNNReal)
    let g : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock c S) z ω).toNNReal
    ∃ N ≤ K, min (T 0) τ = 0 ∧ min (T N) τ = τ ∧
      (∀ k < N, min (T k) τ < min (T (k + 1)) τ) ∧
      (∀ k < N, ∀ t ∈ Ico (min (T k) τ) (min (T (k + 1)) τ),
        dist (g (min t τ)) (g (min (T k) τ)) ≤ 4 * (2 * S / (2 : ℝ) ^ n)) ∧
      (∀ t, min (T N) τ ≤ t → g (min t τ) = g τ) := by
  apply brownianSkeletonClock_outerExit_parentBlock_stopped_knots
    (LatticeProb.ParentBlock.parentDyadicCentre c S n) (2 * S / (2 : ℝ) ^ n)
    (by positivity) (LatticeProb.ParentBlock.parentBlock c S) z j₀ (fun _ => f)
    (fun _ x j hj => hsome x j hj) (fun _ x hx => hnone x hx) K ω
  · simpa only [hzero, add_zero] using (hsome z j₀ hz).2
  · exact hstop
  · exact hfinite

end BouRabeeGwynne
