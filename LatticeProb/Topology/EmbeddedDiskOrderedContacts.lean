import LatticeProb.Topology.OrderedContactGaps
import LatticeProb.Topology.JordanDiskIntersectionBoundary
import LatticeProb.Topology.AnnulusGaps

/-! # Periodic parametrizations of embedded disk boundaries -/

open Set Metric Complex

namespace LatticeProb.Topology

/-- The boundary of an embedded disk is continuously parametrized by one period of the circle. -/
theorem exists_periodic_embedded_disk_boundary {A : Set ℂ}
    (e : closedBall (0 : ℂ) 1 ≃ₜ A) :
    ∃ f : ℝ → ℂ, Continuous f ∧ Function.Periodic f (2 * Real.pi) ∧
      (∀ t, f t ∈ frontier A) ∧
      ∀ x ∈ frontier A, ∃ t ∈ Ico 0 (2 * Real.pi), f t = x := by
  obtain ⟨γ, hγ, _, hγimage⟩ := LatticeProb.isJordanCurve_frontier_of_homeomorph_closedDisk e
  let f : ℝ → ℂ := fun t => γ (circleMap 0 1 t)
  have hsphere (t : ℝ) : circleMap 0 1 t ∈ sphere (0 : ℂ) 1 :=
    circleMap_mem_sphere 0 (by norm_num) t
  refine ⟨f, hγ.comp_continuous (continuous_circleMap 0 1) hsphere, ?_, ?_, ?_⟩
  · intro t
    change γ (circleMap 0 1 (t + 2 * Real.pi)) = γ (circleMap 0 1 t)
    rw [periodic_circleMap 0 1 t]
  · intro t
    rw [← hγimage]
    exact ⟨circleMap 0 1 t, hsphere t, rfl⟩
  · intro x hx
    rw [← hγimage] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := exists_mem_Ico_circleMap_eq (mem_sphere.mp hz) 0
    refine ⟨t, ?_, ?_⟩
    · simpa only [zero_add] using ht
    · change γ (circleMap 0 1 t) = γ z
      rw [he]

/-- Three contacts in distinct components of two embedded disks determine ordered,
accessible gaps on the first disk boundary. -/
theorem exists_embedded_disk_ordered_contacts_and_gaps {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    {x y z : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hz : z ∈ A ∩ B)
    (hxy : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) y)
    (hxz : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) z)
    (hyz : connectedComponentIn (A ∩ B) y ≠ connectedComponentIn (A ∩ B) z) :
    ∃ f : ℝ → ℂ, Continuous f ∧ Function.Periodic f (2 * Real.pi) ∧
      (∀ t, f t ∈ frontier A) ∧
      ∃ a b c, a < b ∧ b < c ∧ c < a + 2 * Real.pi ∧
        f a ∈ A ∩ B ∧ f b ∈ A ∩ B ∧ f c ∈ A ∩ B ∧
        f b ∉ connectedComponentIn (A ∩ B) (f a) ∧
        f c ∉ connectedComponentIn (A ∩ B) (f b) ∧
        f a ∉ connectedComponentIn (A ∩ B) (f c) ∧
        ∃ t₁ ∈ Ioo a b, ∃ t₂ ∈ Ioo b c, ∃ t₃ ∈ Ioo c (a + 2 * Real.pi),
          ∀ t ∈ ({t₁, t₂, t₃} : Set ℝ),
            ∃ (q : ℂ) (P : Set ℂ), q ∈ (A ∪ B)ᶜ ∧ IsCompact P ∧ IsConnected P ∧
              f t ∈ P ∧ q ∈ P ∧ P ⊆ Bᶜ ∩ closure Aᶜ := by
  obtain ⟨f, hf, hp, hfront, hcover⟩ := exists_periodic_embedded_disk_boundary eA
  have hinter := LatticeProb.embedded_disks_inter_frontiers eA eB hdis
  have hB : IsClosed B := (LatticeProb.closure_interior_of_homeomorph_closedDisk eB) ▸ isClosed_closure
  refine ⟨f, hf, hp, hfront, ?_⟩
  exact exists_ordered_contacts_and_accessible_gaps eA hB hf hfront hp
    (fun q hq => hcover q (hinter.2.1 hq)) hx hy hz hxy hxz hyz

end LatticeProb.Topology
