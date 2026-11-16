import LatticeProb.Topology.CompactComponentClopenPartition
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Constructions

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

/-- If locally constant functions modulo constants have finite dimension, the number of
connected components is at most one more than that dimension. -/
theorem cardinal_components_le_finrank_succ
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Field K]
    [Module.Finite K (LocallyConstant X K ⧸
      LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K))] :
    Cardinal.mk (ConnectedComponents X) ≤
      (Module.finrank K (LocallyConstant X K ⧸
        LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)) + 1 : ℕ) := by
  classical
  let d := Module.finrank K (LocallyConstant X K ⧸
    LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K))
  by_contra h
  have hc : ((d + 2 : ℕ) : Cardinal) ≤ Cardinal.mk (ConnectedComponents X) := by
    have := Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge h)
    simpa [d, Nat.cast_add, add_assoc, ← one_add_one_eq_two] using this
  obtain ⟨s, hs⟩ := Cardinal.exists_finset_eq_card hc
  let e : Fin (d + 2) ≃ s := (s.equivFinOfCardEq hs.symm).symm
  let y : Fin (d + 2) → ConnectedComponents X := fun i => (e i).val
  let x : Fin (d + 2) → X := fun i => Classical.choose (ConnectedComponents.surjective_coe (y i))
  have hx : Function.Injective (fun i => ConnectedComponents.mk (x i)) := by
    intro i j hij
    have heq : y i = y j := by
      simpa [x, Classical.choose_spec (ConnectedComponents.surjective_coe (y i)),
        Classical.choose_spec (ConnectedComponents.surjective_coe (y j))] using hij
    exact e.injective (Subtype.ext heq)
  obtain ⟨C, hC, hli⟩ :=
    exists_linearIndependent_classes_of_distinct_components (K := K) (d + 1) x hx
  have hdim := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hdim
  omega

/-- A space with finitely many connected components has a finite-dimensional space of
locally constant functions. -/
theorem finite_locallyConstant_of_finite_components
    {X K : Type*} [TopologicalSpace X] [Field K] [Finite (ConnectedComponents X)] :
    Module.Finite K (LocallyConstant X K) := by
  classical
  let := Fintype.ofFinite (ConnectedComponents X)
  let rep : ConnectedComponents X → X := fun c =>
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hrep (c : ConnectedComponents X) : ConnectedComponents.mk (rep c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let eval : LocallyConstant X K →ₗ[K] (ConnectedComponents X → K) :=
    { toFun := fun f c => f (rep c)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective eval
  intro f g h
  ext x
  have hx : x ∈ connectedComponent (rep (ConnectedComponents.mk x)) :=
    ConnectedComponents.coe_eq_coe'.mp (hrep (ConnectedComponents.mk x)).symm
  have hf := f.apply_eq_of_isPreconnected isPreconnected_connectedComponent hx
    (mem_connectedComponent)
  have hg := g.apply_eq_of_isPreconnected isPreconnected_connectedComponent hx
    (mem_connectedComponent)
  have he := congrFun h (ConnectedComponents.mk x)
  exact hf.trans (he.trans hg.symm)

/-- For compact Hausdorff spaces, the quotient of locally constant functions by constants
is finite-dimensional exactly when there are finitely many connected components. -/
theorem finite_component_classes_iff_finite_components
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Field K] :
    Module.Finite K (LocallyConstant X K ⧸
      LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)) ↔
      Finite (ConnectedComponents X) := by
  constructor
  · intro h
    let := h
    apply Cardinal.mk_lt_aleph0_iff.mp
    exact lt_of_le_of_lt (cardinal_components_le_finrank_succ (K := K))
      Cardinal.natCast_lt_aleph0
  · intro h
    let := h
    let := finite_locallyConstant_of_finite_components (X := X) (K := K)
    exact Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)

/-- The dimension of locally constant functions modulo constants is one less than the
number of components, with natural subtraction including the empty space. -/
theorem finrank_component_classes_eq_card_sub_one
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Field K]
    [Finite (ConnectedComponents X)] :
    Module.finrank K (LocallyConstant X K ⧸
      LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)) =
      Nat.card (ConnectedComponents X) - 1 := by
  classical
  let := Fintype.ofFinite (ConnectedComponents X)
  let := finite_locallyConstant_of_finite_components (X := X) (K := K)
  let P := LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K)
  change Module.finrank K (LocallyConstant X K ⧸ P) = _
  by_cases hX : Nonempty X
  · let := hX
    let rep : ConnectedComponents X → X := fun c =>
      Classical.choose (ConnectedComponents.surjective_coe c)
    have hrep (c : ConnectedComponents X) : ConnectedComponents.mk (rep c) = c :=
      Classical.choose_spec (ConnectedComponents.surjective_coe c)
    let eval : LocallyConstant X K →ₗ[K] (ConnectedComponents X → K) :=
      { toFun := fun f c => f (rep c)
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have heval : Function.Injective eval := by
      intro f g h
      ext x
      have hx : x ∈ connectedComponent (rep (ConnectedComponents.mk x)) :=
        ConnectedComponents.coe_eq_coe'.mp (hrep (ConnectedComponents.mk x)).symm
      have hf := f.apply_eq_of_isPreconnected isPreconnected_connectedComponent hx
        (mem_connectedComponent)
      have hg := g.apply_eq_of_isPreconnected isPreconnected_connectedComponent hx
        (mem_connectedComponent)
      exact hf.trans ((congrFun h _).trans hg.symm)
    have hd := LinearMap.finrank_le_finrank_of_injective heval
    rw [Module.finrank_pi] at hd
    have hconst : Function.Injective (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K) := by
      intro a b h
      have := congrArg (LocallyConstant.evalₗ K (Classical.choice hX)) h
      simpa using this
    have hp : Module.finrank K P = 1 := by
      rw [show P = LinearMap.range (LocallyConstant.constₗ K : K →ₗ[K] LocallyConstant X K) from rfl,
        LinearMap.finrank_range_of_inj hconst, Module.finrank_self]
    have hr := P.finrank_quotient_add_finrank
    rw [hp] at hr
    have hb := cardinal_components_le_finrank_succ (X := X) (K := K)
    rw [Cardinal.mk_fintype] at hb
    have hb' : Fintype.card (ConnectedComponents X) ≤
        Module.finrank K (LocallyConstant X K ⧸ P) + 1 := by exact_mod_cast hb
    rw [Nat.card_eq_fintype_card]
    omega
  · let : IsEmpty X := not_nonempty_iff.mp hX
    have : Subsingleton (LocallyConstant X K) := ⟨fun f g => by ext x; exact isEmptyElim x⟩
    have hz : Module.finrank K (LocallyConstant X K) = 0 := Module.finrank_zero_of_subsingleton
    have hr := P.finrank_quotient_add_finrank
    let : IsEmpty (ConnectedComponents X) := not_nonempty_iff.mp
      (fun h => hX (ConnectedComponents.nonempty_iff_nonempty.mp h))
    have hn : Nat.card (ConnectedComponents X) = 0 := by simp
    rw [hn, Nat.zero_sub]
    omega

end LatticeProb.Topology
