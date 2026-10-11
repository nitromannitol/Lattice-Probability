/-
Labels defined on a dense subset of a preconnected set agree when they are constant
in each ambient open neighborhood of a covering family. The proof constructs two
open unions of neighborhoods and excludes their intersection using density.
-/
import Mathlib.Topology.Connected.Basic
open Set

namespace LatticeProb.Topology

/-- **Dense local labels.** A label on a relatively dense subset of a preconnected set
is constant if every point has an ambient open neighborhood on which the defined
labels agree. The neighborhood condition is an explicit premise of this general lemma. -/
theorem eq_of_dense_local_labels {X Y : Type*} [TopologicalSpace X]
    {S A : Set X} (hS : IsPreconnected S) (hAS : A ⊆ S)
    (hdense : S ⊆ closure A) (f : A → Y)
    (hlocal : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ y : Y, ∀ z : A, z.val ∈ U → f z = y)
    (p q : A) : f p = f q := by
  classical
  let U : Set X := {x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
    ∀ z : A, z.val ∈ W → f z = f p}
  let T : Set X := {x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
    ∀ z : A, z.val ∈ W → f z ≠ f p}
  have hU : IsOpen U := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro x ⟨W, hW, hx, hf⟩
    exact ⟨W, fun w hw => ⟨W, hW, hw, hf⟩, hW, hx⟩
  have hT : IsOpen T := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro x ⟨W, hW, hx, hf⟩
    exact ⟨W, fun w hw => ⟨W, hW, hw, hf⟩, hW, hx⟩
  have hcover : S ⊆ U ∪ T := by
    intro x hx
    obtain ⟨W, hW, hxW, y, hy⟩ := hlocal x hx
    by_cases h : y = f p
    · exact Or.inl ⟨W, hW, hxW, fun z hz => (hy z hz).trans h⟩
    · exact Or.inr ⟨W, hW, hxW, fun z hz heq => h ((hy z hz).symm.trans heq)⟩
  have hpU : p.val ∈ U := by
    obtain ⟨W, hW, hpW, y, hy⟩ := hlocal p.val (hAS p.property)
    exact ⟨W, hW, hpW, fun z hz => (hy z hz).trans (hy p hpW).symm⟩
  by_contra hpq
  have hqT : q.val ∈ T := by
    obtain ⟨W, hW, hqW, y, hy⟩ := hlocal q.val (hAS q.property)
    refine ⟨W, hW, hqW, ?_⟩
    intro z hz heq
    exact hpq (heq.symm.trans ((hy z hz).trans (hy q hqW).symm))
  obtain ⟨x, hxS, hxU, hxT⟩ := hS U T hU hT hcover
    ⟨p.val, hAS p.property, hpU⟩ ⟨q.val, hAS q.property, hqT⟩
  obtain ⟨W, hW, hxW, hWU⟩ := hxU
  obtain ⟨Z, hZ, hxZ, hZT⟩ := hxT
  obtain ⟨z, hzWZ, hzA⟩ := mem_closure_iff.mp (hdense hxS) (W ∩ Z)
    (hW.inter hZ) ⟨hxW, hxZ⟩
  exact hZT ⟨z, hzA⟩ hzWZ.2 (hWU ⟨z, hzA⟩ hzWZ.1)

end LatticeProb.Topology
