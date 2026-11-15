import LatticeProb.Prob.BrownianInteriorAbsorbedStoppedKnots

/-! # Stopped knots for interior parent blocks at a reached cutoff -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A finite parent-block skeleton supplies stopped knots for any reached cutoff. -/
theorem brownianSkeletonClock_reached_interior_parentBlock_stopped_knots {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      interior (LatticeProb.ParentBlock.parentBlock (centres j₀) s))
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
    ∃ N ≤ K + 1, min (T 0) τ.toNNReal = 0 ∧ min (T N) τ.toNNReal = τ.toNNReal ∧
      (∀ n < N, min (T n) τ.toNNReal < min (T (n + 1)) τ.toNNReal) ∧
      (∀ n < N, ∀ t ∈ Ico (min (T n) τ.toNNReal) (min (T (n + 1)) τ.toNNReal),
        dist (f (min t τ.toNNReal)) (f (min (T n) τ.toNNReal)) ≤ 6 * s) ∧
      (∀ t, min (T N) τ.toNNReal ≤ t → f (min t τ.toNNReal) = f τ.toNNReal) := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  cases hflag : (brownianSkeletonClock U z j₀ selector K ω).1 with
  | false =>
    have hreach' : τ.toNNReal ≤ (brownianSkeletonClock U z j₀ selector K ω).2.toNNReal :=
      ENNReal.toNNReal_mono hfinite hreach
    exact brownianSkeletonClock_interior_parentBlock_stopped_knots centres s hs outer z j₀ selector
      hselector K ω hstart hflag hfinite τ.toNNReal hreach'
  | true =>
    obtain ⟨N, hN, hk⟩ := brownianSkeletonClock_absorbed_interior_parentBlock_stopped_knots
      centres s hs outer z j₀ selector hselector K ω hstart hflag hfinite τ hreach
    exact ⟨N, Nat.le_trans hN (Nat.le_succ K), hk⟩

end BouRabeeGwynne
