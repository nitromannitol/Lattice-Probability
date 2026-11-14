import LatticeProb.Prob.BrownianParentBlockActiveStep

/-!
# Active parent-block clock prefixes

A finite active clock gives a monotone sequence of successive parent-block excursions.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- The successive intervals of an active finite clock form a parent-block excursion prefix. -/
theorem brownianSkeletonClock_active_parentBlock_prefix {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (hs : 0 < s) (outer : Set ℂ)
    (z : Euc 2) (j₀ : J) (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈ outer ∧
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (K : ℕ) (ω : BrownianPath 2)
    (hactive : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector K ω).2 ≠ ∞) :
    ∃ (τ : ℕ → ℝ≥0) (selected : ℕ → J), Monotone τ ∧
      (∀ n ≤ K, τ n = (brownianSkeletonClock
        (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
          interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
          z j₀ selector n ω).2.toNNReal) ∧
      ∀ n < K,
        selector (n + 1) (z + ω (τ n)) = some (selected n) ∧
        Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n)) ∈ outer ∧
        Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n)) ∈
          LatticeProb.ParentBlock.closedSquare (centres (selected n)) s ∧
        Complex.orthonormalBasisOneI.repr.symm (z + ω (τ (n + 1))) ∉
          interior (LatticeProb.ParentBlock.parentBlock (centres (selected n)) s) ∧
        ∀ t ∈ Icc (τ n) (τ (n + 1)),
          ‖Complex.orthonormalBasisOneI.repr.symm (z + ω t) -
            Complex.orthonormalBasisOneI.repr.symm (z + ω (τ n))‖ ≤ 4 * s := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  let τ : ℕ → ℝ≥0 := fun n => (brownianSkeletonClock U z j₀ selector (min n K) ω).2.toNNReal
  let selected : ℕ → J := fun n => (selector (n + 1) (z + ω (τ n))).getD j₀
  have hmono : Monotone τ := by
    intro m n hmn
    exact ENNReal.toNNReal_mono
      (brownianSkeletonClock_finite_of_le U z j₀ selector ω (min_le_right n K) hfinite)
      (brownianSkeletonClock_time_monotone U z j₀ selector ω (min_le_min_right K hmn))
  refine ⟨τ, selected, hmono, ?_, ?_⟩
  · intro n hn
    simp only [τ, min_eq_left hn, U]
  · intro n hn
    have hn' : n + 1 ≤ K := Nat.succ_le_of_lt hn
    have ha := brownianSkeletonClock_active_of_le U z j₀ selector ω hn' hactive
    have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω hn' hfinite
    obtain ⟨j, hj, ho, hsquare, hexit, hosc⟩ :=
      brownianSkeletonClock_active_parentBlock_step centres s hs outer z j₀ selector hselector n ω ha hf
    have ht : τ n = (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal := by
      simp only [τ, min_eq_left hn.le]
    have ht' : τ (n + 1) = (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal := by
      simp only [τ, min_eq_left hn']
    change selector (n + 1) (z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) = some j at hj
    have hselected : selected n = j := by
      change (selector (n + 1) (z + ω (τ n))).getD j₀ = j
      rw [ht, hj]
      rfl
    simpa only [ht, ht', hselected] using And.intro hj (And.intro ho (And.intro hsquare (And.intro hexit hosc)))

end BouRabeeGwynne
