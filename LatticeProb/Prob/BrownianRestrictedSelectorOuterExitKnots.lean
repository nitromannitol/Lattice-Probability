import LatticeProb.Prob.BrownianInteriorOuterExitStoppedKnots
import LatticeProb.Prob.SelectorOuterRestriction

/-! # Stopped Brownian knots from restricted margin selectors -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Restrict covered margin selectors to the outer set before constructing the
absorbed skeleton. A finite absorbed stage yields knots up to the outer exit. -/
theorem brownianSkeletonClock_restricted_margin_outerExit_knots
    {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (radius : ℝ) (hradius : 0 < radius)
    (hcover : ∀ n x, Complex.orthonormalBasisOneI.repr.symm x ∈ outer →
      selector n x ≠ none)
    (hmargin : ∀ n x j, selector n x = some j →
      ball x radius ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (K : ℕ) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      interior (LatticeProb.ParentBlock.parentBlock (centres j₀) s))
    (hstop : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀
      (fun n => LatticeProb.restrictSelector
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' outer) (selector n)) K ω).1 = true)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀
      (fun n => LatticeProb.restrictSelector
        (Complex.orthonormalBasisOneI.repr.symm ⁻¹' outer) (selector n)) K ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    let restricted := fun n => LatticeProb.restrictSelector
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹' outer) (selector n)
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ restricted m ω).2.toNNReal)
    let f : ℝ≥0 → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (z + ω t)
    let τ := (continuousExitTime (Complex.orthonormalBasisOneI.repr.symm ⁻¹' outer) z ω).toNNReal
    ∃ N ≤ K, min (T 0) τ = 0 ∧ min (T N) τ = τ ∧
      (∀ n < N, min (T n) τ < min (T (n + 1)) τ) ∧
      (∀ n < N, ∀ t ∈ Ico (min (T n) τ) (min (T (n + 1)) τ),
        dist (f (min t τ)) (f (min (T n) τ)) ≤ 6 * s) ∧
      (∀ t, min (T N) τ ≤ t → f (min t τ) = f τ) := by
  apply brownianSkeletonClock_outerExit_interior_parentBlock_stopped_knots
    centres s hs outer z j₀ _ ?_ ?_ K ω hstart hstop hfinite
  · intro n x j h
    obtain ⟨hout, hselected⟩ := LatticeProb.restrictSelector_some _ _ h
    exact ⟨hout, hmargin n x j hselected (mem_ball_self hradius)⟩
  · intro n x h
    exact LatticeProb.restrictSelector_none_not_mem _ _ (hcover n) h

end BouRabeeGwynne
