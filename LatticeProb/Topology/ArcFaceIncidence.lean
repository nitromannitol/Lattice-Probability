/- Propagation of complement-component incidence along a locally isolated horizontal arc. -/
import LatticeProb.Topology.LocalFaceIncidence
namespace LatticeProb.PlaneTopology

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Closure incidence is open on the interior parameter interval when every point admits
an isolated horizontal-axis window. The local windows may have different radii. -/
theorem isOpen_interior_component_incidence
    (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (gamma : Icc (0 : ℝ) 1 → X)
    (haxis : ∀ t, h (gamma t) = (t.val, 0))
    (hregular : ∀ t : Icc (0 : ℝ) 1, 0 < t.val → t.val < 1 →
      ∃ r : ℝ, 0 < r ∧ ∀ z ∈ axisBox t.val r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) :
    IsOpen {t : Ioo (0 : ℝ) 1 |
      gamma ⟨t.val, t.property.1.le, t.property.2.le⟩ ∈
        closure (connectedComponentIn Sᶜ p)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  let tc : Icc (0 : ℝ) 1 := ⟨t.val, t.property.1.le, t.property.2.le⟩
  obtain ⟨r, hr, htrace⟩ := hregular tc t.property.1 t.property.2
  have heq (s : Icc (0 : ℝ) 1) : gamma s = h.symm (s.val, 0) := by
    apply h.injective
    rw [haxis, h.apply_symm_apply]
  have hbase : h.symm (t.val, 0) ∈ closure (connectedComponentIn Sᶜ p) := by
    rw [← heq tc]
    exact ht
  have hopen : IsOpen {s : Ioo (0 : ℝ) 1 | s.val ∈ Ioo (t.val - r) (t.val + r)} :=
    isOpen_Ioo.preimage continuous_subtype_val
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨by linarith, by linarith⟩)
  intro s hs
  change gamma ⟨s.val, s.property.1.le, s.property.2.le⟩ ∈
    closure (connectedComponentIn Sᶜ p)
  rw [heq]
  exact (axis_mem_closure_component_iff_axis_mem_closure_component S h t.val r hr
    htrace p t.val s.val ⟨by linarith, by linarith⟩ hs).mp hbase

/-- **Interior incidence propagation.** A face component incident at one interior point is incident at every interior point
of a continuous arc with locally isolated horizontal-axis windows. -/
theorem interior_subset_component_incidence_of_regular_axis
    (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (gamma : Icc (0 : ℝ) 1 → X) (hc : Continuous gamma)
    (haxis : ∀ t, h (gamma t) = (t.val, 0))
    (hregular : ∀ t : Icc (0 : ℝ) 1, 0 < t.val → t.val < 1 →
      ∃ r : ℝ, 0 < r ∧ ∀ z ∈ axisBox t.val r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) (t0 : Icc (0 : ℝ) 1) (ht0 : 0 < t0.val) (ht1 : t0.val < 1)
    (hbase : gamma t0 ∈ closure (connectedComponentIn Sᶜ p)) :
    ∀ t : Icc (0 : ℝ) 1, 0 < t.val → t.val < 1 →
      gamma t ∈ closure (connectedComponentIn Sᶜ p) := by
  let T : Set (Ioo (0 : ℝ) 1) := {t |
    gamma ⟨t.val, t.property.1.le, t.property.2.le⟩ ∈
      closure (connectedComponentIn Sᶜ p)}
  have hclosed : IsClosed T :=
    isClosed_closure.preimage (hc.comp (continuous_subtype_val.subtype_mk _))
  have hopen : IsOpen T := isOpen_interior_component_incidence S h gamma haxis hregular p
  letI : PreconnectedSpace (Ioo (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hall : T = univ := (show IsClopen T from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨t0.val, ht0, ht1⟩, hbase⟩
  intro t ht ht'
  have hmem : (⟨t.val, ht, ht'⟩ : Ioo (0 : ℝ) 1) ∈ T := by
    rw [hall]
    exact mem_univ _
  exact hmem

end LatticeProb.PlaneTopology
