import LatticeProb.Walk.ActualGoodExcursionIndexGap
import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Terminal indices for actual parent-block excursions -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace BouRabeeGwynne

/-- Actual matched walk and Brownian skeletons have terminal indices at most one
apart when successive full endpoints start in a square and exit its parent block.
Index zero denotes the first full excursion endpoint. -/
theorem actualSkeleton_terminal_indices_close_of_parentBlock_exits
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc 2) (B : J → Set V) (U : J → Set (Euc 2))
    (initial : J) (z : Euc 2) (j₀ : J)
    (wselect : ℕ → V → Option J) (bselect : ℕ → Euc 2 → Option J)
    (ω : ℕ → V) (η : BrownianPath 2)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (K N M : ℕ) (a s : ℝ) (cw cb : ℕ → ℂ)
    (hN : N ≤ K) (hM : M ≤ K) (hs : 0 ≤ s) (ha : 2 * a < s)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K,
      ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
        brownianSkeletonExcursion U z j₀ bselect i η) ∈ goodExcursionPair pos (E i) a)
    (hwfin : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).1 ≠ ⊤)
    (hwstop : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).2.1 = true)
    (hbfin : (brownianSkeletonClock U z j₀ bselect M η).2 ≠ ∞)
    (hbstop : (brownianSkeletonExcursion U z j₀ bselect M η).1 = true)
    (hwstart : ∀ i, i + 1 < N →
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.2) ∈
        LatticeProb.ParentBlock.closedSquare (cw i) s)
    (hwexit : ∀ i, i + 1 < N →
      Complex.orthonormalBasisOneI.repr.symm
        (ClockedWalkExcursion.endPoint (FiniteConductanceNetwork.actualWalkStage pos B initial wselect (i + 1) ω).2.2) ∉
        interior (LatticeProb.ParentBlock.parentBlock (cw i) s))
    (hbstart : ∀ i, i + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm
        ((brownianSkeletonExcursion U z j₀ bselect i η).2 1) ∈
        LatticeProb.ParentBlock.closedSquare (cb i) s)
    (hbexit : ∀ i, i + 1 < M →
      Complex.orthonormalBasisOneI.repr.symm
        ((brownianSkeletonExcursion U z j₀ bselect (i + 1) η).2 1) ∉
        interior (LatticeProb.ParentBlock.parentBlock (cb i) s)) :
    (∀ i ≤ K, (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.1 =
      (brownianSkeletonExcursion U z j₀ bselect i η).1) ∧ N ≤ M + 1 ∧ M ≤ N + 1 := by
  apply actualSkeleton_terminal_indices_close pos B U initial z j₀ wselect bselect ω η
    m E K N M a s hN hM ha hdiam hgood hwfin hwstop hbfin hbstop
  · intro i hi
    have h := LatticeProb.ParentBlock.side_le_norm_sub_of_not_mem_interior_parentBlock hs
      (hwstart i hi) (hwexit i hi)
    simpa only [← dist_eq_norm, LinearIsometryEquiv.dist_map, dist_comm] using h
  · intro i hi
    have h := LatticeProb.ParentBlock.side_le_norm_sub_of_not_mem_interior_parentBlock hs
      (hbstart i hi) (hbexit i hi)
    simpa only [← dist_eq_norm, LinearIsometryEquiv.dist_map, dist_comm] using h

end BouRabeeGwynne
