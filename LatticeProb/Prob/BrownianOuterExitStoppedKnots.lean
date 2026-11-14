import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton
import LatticeProb.Prob.BrownianAbsorbedStoppedKnots

/-!
# Stopped knots at the outer exit

A finite absorbed parent-block skeleton with a complete selector yields a
finite knot partition for the path stopped at the outer exit.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A complete selector supplies stopped knots up to the outer exit. -/
theorem brownianSkeletonClock_outerExit_parentBlock_stopped_knots {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (hnone : ∀ n x, selector n x = none →
      Complex.orthonormalBasisOneI.repr.symm x ∉ outer)
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      LatticeProb.ParentBlock.closedSquare (centres j₀) s)
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
    let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' outer) z ω).toNNReal
    ∃ N ≤ K, min (T 0) τ = 0 ∧ min (T N) τ = τ ∧
      (∀ n < N, min (T n) τ < min (T (n + 1)) τ) ∧
      (∀ n < N, ∀ t ∈ Ico (min (T n) τ) (min (T (n + 1)) τ),
        dist (f (min t τ)) (f (min (T n) τ)) ≤ 4 * s) ∧
      (∀ t, min (T N) τ ≤ t → f (min t τ) = f τ) := by
  apply brownianSkeletonClock_absorbed_parentBlock_stopped_knots
    centres s hs outer z j₀ selector hselector K ω hstart hstop hfinite
  exact brownianSkeletonClock_exit_le_of_stopped _ z j₀ selector hnone K ω hfinite hstop

end BouRabeeGwynne
