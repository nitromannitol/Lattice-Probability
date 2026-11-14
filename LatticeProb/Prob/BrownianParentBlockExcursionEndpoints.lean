import LatticeProb.Prob.BrownianActiveClockExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonExcursion
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Full endpoints of parent-block excursions -/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace BouRabeeGwynne

/-- An active finite step starts in its selected square and its full excursion
endpoint lies outside that square's parent-block interior. -/
theorem brownianSkeletonExcursion_active_parentBlock_endpoints {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (z : Euc 2) (j₀ : J)
    (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (n : ℕ) (ω : BrownianPath 2)
    (hactive : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector (n + 1) ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    ∃ j, selector (n + 1) ((brownianSkeletonExcursion U z j₀ selector n ω).2 1) = some j ∧
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector n ω).2 1) ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s ∧
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector (n + 1) ω).2 1) ∉
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s) := by
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  have hU : ∀ j, IsOpen (U j) := fun j => isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hprev : (brownianSkeletonClock U z j₀ selector n ω).2 ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (brownianSkeletonClock_time_le_succ U z j₀ selector n ω)
  obtain ⟨j, hj, hout⟩ :=
    brownianSkeletonClock_active_step_exit U hU z j₀ selector n ω hactive hfinite
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [brownianSkeletonExcursion_endPoint U z j₀ selector n ω hprev]
    exact hj
  · rw [brownianSkeletonExcursion_endPoint U z j₀ selector n ω hprev]
    exact hselector _ _ _ hj
  · rw [brownianSkeletonExcursion_endPoint U z j₀ selector (n + 1) ω hfinite]
    exact hout

/-- On a finite active prefix, one centre for each pair of consecutive full
endpoints witnesses both the square start and the parent-block exit. -/
theorem brownianSkeletonExcursion_parentBlock_endpoint_prefix {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (centres : J → ℂ) (s : ℝ) (z : Euc 2) (j₀ : J)
    (selector : ℕ → Euc 2 → Option J)
    (hselector : ∀ n x j, selector n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (M : ℕ) (ω : BrownianPath 2)
    (hactive : ∀ n, n + 1 < M → (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s)) z j₀ selector M ω).2 ≠ ∞) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    ∃ c : ℕ → ℂ, ∀ n, n + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector n ω).2 1) ∈
        LatticeProb.ParentBlock.closedSquare (c n) s ∧
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector (n + 1) ω).2 1) ∉
        interior (LatticeProb.ParentBlock.parentBlock (c n) s) := by
  classical
  let U : J → Set (Euc 2) := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
  have h : ∀ n, ∃ j, n + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector n ω).2 1) ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s ∧
      Complex.orthonormalBasisOneI.repr.symm ((brownianSkeletonExcursion U z j₀ selector (n + 1) ω).2 1) ∉
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s) := by
    intro n
    by_cases hn : n + 1 < M
    · have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω hn.le hfinite
      obtain ⟨j, _, hsquare, hexit⟩ :=
        brownianSkeletonExcursion_active_parentBlock_endpoints centres s z j₀ selector hselector n ω (hactive n hn) hf
      exact ⟨j, fun _ => ⟨hsquare, hexit⟩⟩
    · exact ⟨j₀, fun hn' => False.elim (hn hn')⟩
  choose selected hselected using h
  exact ⟨fun n => centres (selected n), hselected⟩

end BouRabeeGwynne
