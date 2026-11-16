import LatticeProb.Topology.CompactComponentClopenPartition
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Locally constant classes from components

Clopen sets separating chosen components yield independent locally constant functions modulo
constant functions.
-/

open Set

namespace LatticeProb.Topology

/-- Disjoint clopen sets with chosen points and a point outside all of them determine linearly
independent classes of characteristic functions modulo constants. -/
theorem linearIndependent_clopen_classes
    {X I K : Type*} [TopologicalSpace X] [Field K]
    (C : I → Set X) (hC : ∀ i, IsClopen (C i))
    (x : I → X) (hx : ∀ i, x i ∈ C i)
    (hdis : univ.PairwiseDisjoint C) (b : X) (hb : ∀ i, b ∉ C i) :
    LinearIndependent K (fun i =>
      (LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)).mkQ
        (LocallyConstant.charFn K (hC i))) := by
  classical
  let P := LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hm : (∑ j ∈ s, g j • LocallyConstant.charFn K (hC j)) ∈ P := by
    apply (Submodule.Quotient.mk_eq_zero P).mp
    simpa only [← Submodule.mkQ_apply, map_sum, map_smul] using hg
  obtain ⟨a, ha⟩ := hm
  have ha0 : a = 0 := by
    have h := congrArg (LocallyConstant.evalₗ K b) ha
    simpa [LocallyConstant.charFn, LocallyConstant.indicator_of_notMem, hb] using h
  subst a
  have h := congrArg (LocallyConstant.evalₗ K (x i)) ha
  have hnot : ∀ j ∈ s, j ≠ i → x i ∉ C j := by
    intro j _ hji hmem
    exact (Set.disjoint_left.mp (hdis (mem_univ i) (mem_univ j) hji.symm)) (hx i) hmem
  simp only [map_sum, map_smul, LocallyConstant.evalₗ_apply, map_zero, smul_eq_mul] at h
  have hs : (∑ j ∈ s, g j * LocallyConstant.charFn K (hC j) (x i)) = g i := by
    rw [Finset.sum_eq_single i]
    · simp [LocallyConstant.charFn, hx]
    · intro j hj hji
      simp [LocallyConstant.charFn, hnot j hj hji]
    · simp [hi]
  rw [hs] at h
  exact h.symm

/-- Distinct components of a compact Hausdorff space give independent locally constant
classes modulo constants. No finiteness assumption is made on the set of all components. -/
theorem exists_linearIndependent_classes_of_distinct_components
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Field K]
    (n : ℕ) (x : Fin (n + 1) → X)
    (hx : Function.Injective (fun i => ConnectedComponents.mk (x i))) :
    ∃ (C : Fin n → Set X) (hC : ∀ i, IsClopen (C i)),
      LinearIndependent K (fun i =>
        (LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)).mkQ
          (LocallyConstant.charFn K (hC i))) := by
  obtain ⟨C, hC, hxC, _, hdis⟩ := exists_clopen_partition_of_distinct_components x hx
  refine ⟨fun i => C i.succ, fun i => hC i.succ, ?_⟩
  apply linearIndependent_clopen_classes (x := fun i => x i.succ) (b := x 0)
  · intro i
    exact hxC i.succ
  · intro i _ j _ hij
    exact hdis (mem_univ _) (mem_univ _) (fun h => hij (Fin.succ_injective n h))
  · intro i hi
    exact (Set.disjoint_left.mp
      (hdis (mem_univ _) (mem_univ _) (Fin.succ_ne_zero i).symm)) (hxC 0) hi

end LatticeProb.Topology
