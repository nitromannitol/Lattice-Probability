import LatticeProb.Topology.SeparationOrder
import LatticeProb.Topology.IntervalCharacterization

/-!
# A continuum with exactly two non-cut points is an arc

Let `X` be a compact connected `T₁` space and let `a ≠ b` be points of `X` such that `a` and `b` are the only
non-cut points of `X`: `X \ {x}` is connected exactly when `x = a` or `x = b`. For `x : X` write `L x` for the
connected component of `a` in `X \ {x}` (the side of `x` towards `a`) and `R x` for the component of `b`; these are
disjoint open sets covering `X \ {x}` (`isOpen_connectedComponentIn_compl_singleton_and`).

The *separation order* of `X` is `x < y :↔ x ∈ L y`: the point `y ≠ x` does not separate `x` from `a`. This file
proves that it is a strict total order (`isStrictTotalOrder_separationOrder`) whose open rays are `L y` and `R y`,
and concludes with the classical characterisation of the arc (R. L. Moore; see Willard, *General Topology*, §28):

* `nonempty_homeomorph_unitInterval_of_isPreconnected_compl_singleton_iff`: a separable compact connected `T₁` space
  with exactly two non-cut points is homeomorphic to `[0, 1]`.

The key step (`connectedComponentIn_subset_and_mem_of_mem`) is: if `x ∈ L y`, then `L x ⊆ L y` and `y ∈ R x`.
Indeed, `R x ∪ {x}` and `L x ∪ {x}` are connected; if `y ∉ R x`, the connected set `R x ∪ {x}` avoids `y` and meets
`L y` at `x`, so `b ∈ R x ⊆ L y`, which is impossible; and then `L x ∪ {x}` avoids `y`, so it lies in `L y`.
-/

namespace LatticeProb.Topology

open Set

variable {X : Type*} [TopologicalSpace X] [T1Space X] [CompactSpace X] [ConnectedSpace X] {a b : X}

/-- The side of any point towards `a` does not contain `b`. -/
theorem notMem_connectedComponentIn_compl_singleton_of_isPreconnected_iff (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) (y : X) :
    b ∉ connectedComponentIn {y}ᶜ a := by
  intro h
  obtain ⟨-, -, hdisj, -⟩ := isOpen_connectedComponentIn_compl_singleton_and hab honly y
  have hb : b ∈ connectedComponentIn {y}ᶜ b := mem_connectedComponentIn (connectedComponentIn_subset _ _ h)
  rw [connectedComponentIn_eq h] at hdisj
  exact disjoint_left.1 hdisj hb hb

/-- **Monotonicity of the sides.** If `x` lies on the side of `y` towards `a`, then the side of `x` towards `a` is
contained in the side of `y` towards `a`, and `y` lies on the side of `x` towards `b`. -/
theorem connectedComponentIn_subset_and_mem_of_mem (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) {x y : X}
    (hxy : x ∈ connectedComponentIn {y}ᶜ a) :
    connectedComponentIn {x}ᶜ a ⊆ connectedComponentIn {y}ᶜ a ∧ y ∈ connectedComponentIn {x}ᶜ b := by
  obtain ⟨hLo, hRo, hdx, hcx⟩ := isOpen_connectedComponentIn_compl_singleton_and hab honly x
  have hne : x ≠ y := mem_compl_singleton_iff.1 (connectedComponentIn_subset _ _ hxy)
  have hxb : x ≠ b := fun h =>
    notMem_connectedComponentIn_compl_singleton_of_isPreconnected_iff hab honly y (h ▸ hxy)
  have hyR : y ∈ connectedComponentIn {x}ᶜ b := by
    by_contra hyR
    have hpre : IsPreconnected (insert x (connectedComponentIn {x}ᶜ b)) :=
      isPreconnected_insert_of_union_eq_compl_singleton hRo hLo hdx.symm ((union_comm _ _).trans hcx)
    have hsub : insert x (connectedComponentIn {x}ᶜ b) ⊆ {y}ᶜ := by
      intro z hz
      rcases hz with hz | hz
      · exact mem_compl_singleton_iff.2 (hz ▸ hne)
      · exact mem_compl_singleton_iff.2 fun h => hyR (h ▸ hz)
    have hbR : b ∈ connectedComponentIn {x}ᶜ b :=
      mem_connectedComponentIn (mem_compl_singleton_iff.2 hxb.symm)
    have hS := hpre.subset_connectedComponentIn (mem_insert x _) hsub
    rw [← connectedComponentIn_eq hxy] at hS
    exact notMem_connectedComponentIn_compl_singleton_of_isPreconnected_iff hab honly y
      (hS (mem_insert_of_mem x hbR))
  refine ⟨fun z hz => ?_, hyR⟩
  have hpre : IsPreconnected (insert x (connectedComponentIn {x}ᶜ a)) :=
    isPreconnected_insert_of_union_eq_compl_singleton hLo hRo hdx hcx
  have hsub : insert x (connectedComponentIn {x}ᶜ a) ⊆ {y}ᶜ := by
    intro w hw
    rcases hw with hw | hw
    · exact mem_compl_singleton_iff.2 (hw ▸ hne)
    · exact mem_compl_singleton_iff.2 fun h => disjoint_left.1 hdx hw (h ▸ hyR)
  have hS := hpre.subset_connectedComponentIn (mem_insert x _) hsub
  rw [← connectedComponentIn_eq hxy] at hS
  exact hS (mem_insert_of_mem x hz)

/-- **The separation order is a strict total order.** The relation `x < y :↔ x ∈ L y` (`x` lies on the side of
`y` towards `a`) is irreflexive, transitive and trichotomous. -/
theorem isStrictTotalOrder_separationOrder (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) :
    IsStrictTotalOrder X (fun x y => x ∈ connectedComponentIn {y}ᶜ a) where
  irrefl x h := mem_compl_singleton_iff.1 (connectedComponentIn_subset _ _ h) rfl
  trans x y z hxy hyz := (connectedComponentIn_subset_and_mem_of_mem hab honly hyz).1 hxy
  trichotomous x y hxy hyx := by
    by_contra hne
    have honly' : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = b ∨ x = a := fun x => (honly x).trans or_comm
    obtain ⟨-, -, -, hcy⟩ := isOpen_connectedComponentIn_compl_singleton_and hab honly y
    have hxR : x ∈ connectedComponentIn {y}ᶜ b := by
      have hx : x ∈ ({y}ᶜ : Set X) := mem_compl_singleton_iff.2 hne
      rw [← hcy] at hx
      exact hx.resolve_left hxy
    exact hyx (connectedComponentIn_subset_and_mem_of_mem hab.symm honly' hxR).2

/-- The side of `y` towards `b` is the set of points `z` such that `y` lies on the side of `z` towards `a`. -/
theorem connectedComponentIn_compl_singleton_right_eq (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) (y : X) :
    connectedComponentIn {y}ᶜ b = {z | y ∈ connectedComponentIn {z}ᶜ a} := by
  have honly' : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = b ∨ x = a := fun x => (honly x).trans or_comm
  ext z
  exact ⟨fun hz => (connectedComponentIn_subset_and_mem_of_mem hab.symm honly' hz).2,
    fun hz => (connectedComponentIn_subset_and_mem_of_mem hab honly hz).2⟩

/-- **Characterisation of the arc.** A separable compact connected `T₁` space whose only non-cut points are two
distinct points `a` and `b` is homeomorphic to the unit interval. -/
theorem nonempty_homeomorph_unitInterval_of_isPreconnected_compl_singleton_iff
    [TopologicalSpace.SeparableSpace X] (hab : a ≠ b)
    (honly : ∀ x : X, IsPreconnected ({x}ᶜ : Set X) ↔ x = a ∨ x = b) : Nonempty (X ≃ₜ unitInterval) := by
  classical
  have hsto := isStrictTotalOrder_separationOrder hab honly
  let _ : LinearOrder X := linearOrderOfSTO (fun x y => x ∈ connectedComponentIn {y}ᶜ a)
  have : Nontrivial X := ⟨⟨a, b, hab⟩⟩
  refine nonempty_homeomorph_unitInterval_of_isOpen_rays (fun y => ?_) (fun y => ?_)
  · exact (isOpen_connectedComponentIn_compl_singleton_and hab honly y).1
  · have hR := (isOpen_connectedComponentIn_compl_singleton_and hab honly y).2.1
    rw [connectedComponentIn_compl_singleton_right_eq hab honly y] at hR
    exact hR

end LatticeProb.Topology
