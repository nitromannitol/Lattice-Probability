import LatticeProb.Prob.BrownianFirstAbsorption
import LatticeProb.Prob.BrownianParentBlockStoppedKnots

/-!
# Stopped knots for absorbed parent-block skeletons

A finite absorbed skeleton gives a finite active prefix whose excursions
control the stopped path up to any cutoff reached by the terminal clock.
-/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- An absorbed parent-block skeleton supplies stopped knots for any reached cutoff. -/
theorem brownianSkeletonClock_absorbed_parentBlock_stopped_knots {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      LatticeProb.ParentBlock.closedSquare (centres j₀) s)
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞)
    (τ : ℝ≥0∞)
    (hreach : τ ≤ (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
    let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    ∃ N ≤ K, min (T 0) τ.toNNReal = 0 ∧ min (T N) τ.toNNReal = τ.toNNReal ∧
      (∀ n < N, min (T n) τ.toNNReal < min (T (n + 1)) τ.toNNReal) ∧
      (∀ n < N, ∀ t ∈ Ico (min (T n) τ.toNNReal) (min (T (n + 1)) τ.toNNReal),
        dist (f (min t τ.toNNReal)) (f (min (T n) τ.toNNReal)) ≤ 4 * s) ∧
      (∀ t, min (T N) τ.toNNReal ≤ t → f (min t τ.toNNReal) = f τ.toNNReal) := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  obtain ⟨m, hm, ha, _, heq, htime⟩ :=
    brownianSkeletonClock_exists_last_active U z j₀ selector ω K hstop
  have hclock : (brownianSkeletonClock U z j₀ selector K ω).2 =
      (brownianSkeletonClock U z j₀ selector m ω).2 := by
    rw [heq, htime]
  have hfinm : (brownianSkeletonClock U z j₀ selector m ω).2 ≠ ∞ := by
    rw [← hclock]
    exact hfinite
  have hreachm : τ.toNNReal ≤
      (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal := by
    apply ENNReal.toNNReal_mono hfinm
    rw [← hclock]
    exact hreach
  obtain ⟨N, hN, hk⟩ := brownianSkeletonClock_parentBlock_stopped_knots
    centres s hs outer z j₀ selector hselector m ω hstart ha hfinm τ.toNNReal hreachm
  exact ⟨N, by omega, hk⟩

end BouRabeeGwynne
