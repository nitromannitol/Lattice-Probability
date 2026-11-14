import LatticeProb.Walk.ActualParentBlockExcursionEndpoints
import LatticeProb.Prob.BrownianParentBlockExcursionEndpoints
import LatticeProb.Walk.ActualParentBlockIndexGap

/-! # Terminal indices from actual parent-block excursion geometry -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace BouRabeeGwynne

/-- Finite active prefixes of matched parent-block skeletons have terminal
indices at most one apart, under the good-excursion and separation bounds. -/
theorem actualSkeleton_terminal_indices_close_of_active_parentBlock_prefixes
    {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc 2) (B : J → Set V) (centres : J → ℂ)
    (initial : J) (z : Euc 2) (j₀ : J)
    (wselect : ℕ → V → Option J) (bselect : ℕ → Euc 2 → Option J)
    (ω : ℕ → V) (η : BrownianPath 2)
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc 2))
    (K N M : ℕ) (a s : ℝ)
    (hN : N ≤ K) (hM : M ≤ K) (hs : 0 ≤ s) (ha : 2 * a < s)
    (hwselect : ∀ n v j, wselect n v = some j →
      Complex.orthonormalBasisOneI.repr.symm (pos v) ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (hB : ∀ j v, v ∉ B j → Complex.orthonormalBasisOneI.repr.symm (pos v) ∉
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
    (hbselect : ∀ n x j, bselect n x = some j →
      Complex.orthonormalBasisOneI.repr.symm x ∈
        LatticeProb.ParentBlock.closedSquare (centres j) s)
    (hdiam : ∀ i ≤ K, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ K,
      ((FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2,
        brownianSkeletonExcursion
          (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
            interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
          z j₀ bselect i η) ∈ goodExcursionPair pos (E i) a)
    (hwfin : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).1 ≠ ⊤)
    (hwstop : (FiniteConductanceNetwork.actualWalkStage pos B initial wselect N ω).2.1 = true)
    (hwactive : ∀ n, n + 1 < N →
      (FiniteConductanceNetwork.actualWalkStage pos B initial wselect (n + 1) ω).2.1 = false)
    (hbfin : (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
      z j₀ bselect M η).2 ≠ ∞)
    (hbstop : (brownianSkeletonExcursion
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
      z j₀ bselect M η).1 = true)
    (hbactive : ∀ n, n + 1 < M → (brownianSkeletonClock
      (fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock (centres j) s))
      z j₀ bselect (n + 1) η).1 = false) :
    let U := fun j => Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock (centres j) s)
    (∀ i ≤ K, (FiniteConductanceNetwork.actualWalkStage pos B initial wselect i ω).2.1 =
      (brownianSkeletonExcursion U z j₀ bselect i η).1) ∧ N ≤ M + 1 ∧ M ≤ N + 1 := by
  obtain ⟨cw, hw⟩ := FiniteConductanceNetwork.actualWalkStage_parentBlock_endpoint_prefix
    pos B initial wselect centres s hwselect hB N ω hwactive hwfin
  obtain ⟨cb, hb⟩ := brownianSkeletonExcursion_parentBlock_endpoint_prefix
    centres s z j₀ bselect hbselect M η hbactive hbfin
  exact actualSkeleton_terminal_indices_close_of_parentBlock_exits pos B _ initial z j₀
    wselect bselect ω η m E K N M a s cw cb hN hM hs ha hdiam hgood hwfin hwstop
    hbfin hbstop (fun i hi => (hw i hi).1) (fun i hi => (hw i hi).2)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)

end BouRabeeGwynne
