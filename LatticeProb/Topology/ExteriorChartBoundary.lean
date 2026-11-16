import LatticeProb.Topology.EmbeddedChartAlternation
import LatticeProb.Topology.OrderedContactGaps

/-! # Boundary parametrization adapted to an exterior disk chart -/

open Set Metric Complex

namespace LatticeProb.Topology

/-- An exterior disk chart has a periodic boundary parametrization whose
chart values are the standard parametrization of the unit circle. -/
theorem exists_exterior_chart_boundary_parametrization {A : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ A) :
    ∃ (g : closure Aᶜ → ℂ) (f : ℝ → frontier A),
      Continuous g ∧ Function.Injective g ∧
      (∀ x, g x ∈ closedBall (0 : ℂ) 1) ∧
      Continuous f ∧ Function.Periodic f (2 * Real.pi) ∧
      (∀ x : frontier A, ∃ t ∈ Ico 0 (2 * Real.pi), f t = x) ∧
      ∀ t, g ⟨f t, by
        exact (show (f t : ℂ) ∈ closure A ∩ closure Aᶜ from
          (frontier_eq_closure_inter_closure (s := A)) ▸ (f t).property).2⟩ = circleMap 0 1 t := by
  obtain ⟨g, hg, hgi, hgd, hgb⟩ := exists_embedded_disk_exterior_chart e
  have hfrontsub : frontier A ⊆ closure Aᶜ := by
    intro x hx
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  let j : frontier A → closure Aᶜ := fun x => ⟨x, hfrontsub x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hm (x : frontier A) : g (j x) ∈ sphere (0 : ℂ) 1 := by
    rw [← hgb]
    exact ⟨j x, x.property, rfl⟩
  let v : frontier A → sphere (0 : ℂ) 1 := fun x => ⟨g (j x), hm x⟩
  have hv : Continuous v := (hg.comp hj).subtype_mk _
  have hvi : Function.Injective v := by
    intro x y h
    apply Subtype.ext
    have heq : g (j x) = g (j y) := congrArg Subtype.val h
    exact congrArg (fun z : closure Aᶜ => (z : ℂ)) (hgi heq)
  have hvs : Function.Surjective v := by
    intro y
    have hy : (y : ℂ) ∈ g '' {x | (x : ℂ) ∈ frontier A} := by
      rw [hgb]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hA : IsCompact A := by
    let : CompactSpace A := e.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  let : CompactSpace (frontier A) :=
    isCompact_iff_compactSpace.mp (hA.of_isClosed_subset isClosed_frontier hA.isClosed.frontier_subset)
  let E : frontier A ≃ₜ sphere (0 : ℂ) 1 :=
    (hv.isClosedEmbedding hvi).isEmbedding.toHomeomorphOfSurjective hvs
  let c : ℝ → sphere (0 : ℂ) 1 := fun t =>
    ⟨circleMap 0 1 t, circleMap_mem_sphere 0 (by norm_num) t⟩
  let f : ℝ → frontier A := fun t => E.symm (c t)
  refine ⟨g, f, hg, hgi, hgd, E.symm.continuous.comp
    ((continuous_circleMap 0 1).subtype_mk _), ?_, ?_, ?_⟩
  · intro t
    change E.symm (c (t + 2 * Real.pi)) = E.symm (c t)
    congr 1
    apply Subtype.ext
    exact periodic_circleMap 0 1 t
  · intro x
    obtain ⟨t, ht, he⟩ := exists_mem_Ico_circleMap_eq
      (mem_sphere.mp (E x).property) 0
    refine ⟨t, by simpa only [zero_add] using ht, ?_⟩
    change E.symm (c t) = x
    have hc : c t = E x := Subtype.ext he
    rw [hc, Homeomorph.symm_apply_apply]
  · intro t
    have h : v (f t) = c t := E.apply_symm_apply (c t)
    exact congrArg Subtype.val h

/-- Three distinct contact components determine accessible gaps in the cyclic
order of an exterior disk chart. -/
theorem exists_chart_ordered_contacts_and_accessible_gaps {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    {x y z : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hz : z ∈ A ∩ B)
    (hxy : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) y)
    (hxz : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) z)
    (hyz : connectedComponentIn (A ∩ B) y ≠ connectedComponentIn (A ∩ B) z) :
    ∃ (g : closure Aᶜ → ℂ) (f : ℝ → frontier A),
      Continuous g ∧ Function.Injective g ∧
      (∀ w, g w ∈ closedBall (0 : ℂ) 1) ∧
      (∀ t, g ⟨f t, by
        exact (show (f t : ℂ) ∈ closure A ∩ closure Aᶜ from
          (frontier_eq_closure_inter_closure (s := A)) ▸ (f t).property).2⟩ =
        circleMap 0 1 t) ∧
      ∃ a b c, a < b ∧ b < c ∧ c < a + 2 * Real.pi ∧
        (f a : ℂ) ∈ A ∩ B ∧ (f b : ℂ) ∈ A ∩ B ∧ (f c : ℂ) ∈ A ∩ B ∧
        (f b : ℂ) ∉ connectedComponentIn (A ∩ B) (f a) ∧
        (f c : ℂ) ∉ connectedComponentIn (A ∩ B) (f b) ∧
        (f a : ℂ) ∉ connectedComponentIn (A ∩ B) (f c) ∧
        ∃ t₁ ∈ Ioo a b, ∃ t₂ ∈ Ioo b c, ∃ t₃ ∈ Ioo c (a + 2 * Real.pi),
          ∀ t ∈ ({t₁, t₂, t₃} : Set ℝ),
            ∃ (q : ℂ) (P : Set ℂ), q ∈ (A ∪ B)ᶜ ∧ IsCompact P ∧ IsConnected P ∧
              (f t : ℂ) ∈ P ∧ q ∈ P ∧ P ⊆ Bᶜ ∩ closure Aᶜ := by
  obtain ⟨g, f, hg, hgi, hgd, hf, hp, hcover, hgf⟩ :=
    exists_exterior_chart_boundary_parametrization eA
  have hinter := LatticeProb.embedded_disks_inter_frontiers eA eB hdis
  have hB : IsClosed B := (LatticeProb.closure_interior_of_homeomorph_closedDisk eB) ▸ isClosed_closure
  have hcont : Continuous (fun t : ℝ => (f t : ℂ)) := continuous_subtype_val.comp hf
  have hperiod : Function.Periodic (fun t : ℝ => (f t : ℂ)) (2 * Real.pi) :=
    fun t => congrArg Subtype.val (hp t)
  have hc : ∀ w ∈ A ∩ B, ∃ t ∈ Ico 0 (2 * Real.pi), (f t : ℂ) = w := by
    intro w hw
    obtain ⟨t, ht, he⟩ := hcover ⟨w, hinter.2.1 hw⟩
    exact ⟨t, ht, congrArg Subtype.val he⟩
  exact ⟨g, f, hg, hgi, hgd, hgf,
    exists_ordered_contacts_and_accessible_gaps eA hB hcont
      (fun t => (f t).property) hperiod hc hx hy hz hxy hxz hyz⟩

end LatticeProb.Topology
