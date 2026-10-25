module

/-
A regular horizontal-axis chart determines the actual complementary components on its
upper and lower sides and their closure incidence. The proof maps the preconnected
half rectangles into the complement and uses open neighborhoods to classify incidence.
-/
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

@[expose] public section
open Set

namespace LatticeProb.PlaneTopology

/-- The upper half of an open rectangle centered on the horizontal axis. -/
def upperHalfBox (a r : ℝ) : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo 0 r

/-- The lower half of an open rectangle centered on the horizontal axis. -/
def lowerHalfBox (a r : ℝ) : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) 0

/-- The full open rectangle about the horizontal axis. -/
def axisBox (a r : ℝ) : Set (ℝ × ℝ) := Ioo (a - r) (a + r) ×ˢ Ioo (-r) r

variable {X : Type*} [TopologicalSpace X]

/-- Every upper-half chart point belongs to the complement component of the upper seed. -/
theorem upper_half_box_subset_component (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0) :
    h.symm '' upperHalfBox a r ⊆ connectedComponentIn Sᶜ (h.symm (a, r / 2)) := by
  apply ((isPreconnected_Ioo.prod isPreconnected_Ioo).image h.symm
    h.symm.continuous.continuousOn).subset_connectedComponentIn
  · exact ⟨(a, r / 2), ⟨⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩, rfl⟩
  · rintro p ⟨z, hz, rfl⟩
    have hb : z ∈ axisBox a r := ⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
    exact fun hp => (ne_of_gt hz.2.1) ((htrace z hb).mp hp)

/-- Every lower-half chart point belongs to the complement component of the lower seed. -/
theorem lower_half_box_subset_component (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0) :
    h.symm '' lowerHalfBox a r ⊆ connectedComponentIn Sᶜ (h.symm (a, -(r / 2))) := by
  apply ((isPreconnected_Ioo.prod isPreconnected_Ioo).image h.symm
    h.symm.continuous.continuousOn).subset_connectedComponentIn
  · exact ⟨(a, -(r / 2)), ⟨⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩, rfl⟩
  · rintro p ⟨z, hz, rfl⟩
    have hb : z ∈ axisBox a r := ⟨hz.1, ⟨hz.2.1, by linarith [hz.2.2]⟩⟩
    exact fun hp => (ne_of_lt hz.2.2) ((htrace z hb).mp hp)

/-- Both actual side components accumulate at every axis point inside the chart. -/
theorem axis_mem_closure_side_components (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (x : ℝ) (hx : x ∈ Ioo (a - r) (a + r)) :
    h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ (h.symm (a, r / 2))) ∧
    h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ (h.symm (a, -(r / 2)))) := by
  have hxclosed : x ∈ Icc (a - r) (a + r) := ⟨hx.1.le, hx.2.le⟩
  constructor
  · apply closure_mono (upper_half_box_subset_component S h a r hr htrace)
    apply image_closure_subset_closure_image h.symm.continuous
    refine ⟨(x, 0), ?_, rfl⟩
    rw [upperHalfBox, closure_prod_eq, closure_Ioo (by linarith : a-r ≠ a+r),
      closure_Ioo (ne_of_lt hr)]
    exact ⟨hxclosed, ⟨le_rfl, hr.le⟩⟩
  · apply closure_mono (lower_half_box_subset_component S h a r hr htrace)
    apply image_closure_subset_closure_image h.symm.continuous
    refine ⟨(x, 0), ?_, rfl⟩
    rw [lowerHalfBox, closure_prod_eq, closure_Ioo (by linarith : a-r ≠ a+r),
      closure_Ioo (by linarith : -r ≠ 0)]
    exact ⟨hxclosed, ⟨by linarith, le_rfl⟩⟩

 /-- A complement component accumulating at an interior axis point is one of the two sides.
 The two components are allowed to coincide. -/
theorem component_eq_side_of_axis_mem_closure (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) (x : ℝ) (hx : x ∈ Ioo (a - r) (a + r))
    (hclosure : h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ p)) :
    connectedComponentIn Sᶜ p = connectedComponentIn Sᶜ (h.symm (a, r / 2)) ∨
    connectedComponentIn Sᶜ p = connectedComponentIn Sᶜ (h.symm (a, -(r / 2))) := by
  have hopen : IsOpen (h.symm '' axisBox a r) :=
    h.symm.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)
  have haxis : h.symm (x, 0) ∈ h.symm '' axisBox a r :=
    ⟨(x, 0), ⟨hx, ⟨by linarith, hr⟩⟩, rfl⟩
  obtain ⟨q, ⟨z, hz, rfl⟩, hq⟩ := mem_closure_iff.mp hclosure _ hopen haxis
  have hne : z.2 ≠ 0 := fun hz0 =>
    (connectedComponentIn_subset Sᶜ p hq) ((htrace z hz).mpr hz0)
  rcases lt_or_gt_of_ne hne with hn | hp
  · have hs := lower_half_box_subset_component S h a r hr htrace
      ⟨z, ⟨hz.1, hz.2.1, hn⟩, rfl⟩
    exact Or.inr ((connectedComponentIn_eq hq).trans (connectedComponentIn_eq hs).symm)
  · have hs := upper_half_box_subset_component S h a r hr htrace
      ⟨z, ⟨hz.1, hp, hz.2.2⟩, rfl⟩
    exact Or.inl ((connectedComponentIn_eq hq).trans (connectedComponentIn_eq hs).symm)

/-- **Chart-side incidence.** Incidence at an axis point is characterized by the two
actual side components, which are allowed to coincide. -/
theorem axis_mem_closure_component_iff (S : Set X) (h : X ≃ₜ (ℝ × ℝ))
    (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) (x : ℝ) (hx : x ∈ Ioo (a - r) (a + r)) :
    h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ p) ↔
    connectedComponentIn Sᶜ p = connectedComponentIn Sᶜ (h.symm (a, r / 2)) ∨
    connectedComponentIn Sᶜ p = connectedComponentIn Sᶜ (h.symm (a, -(r / 2))) := by
  constructor
  · exact component_eq_side_of_axis_mem_closure S h a r hr htrace p x hx
  · intro heq
    obtain ⟨hpos, hneg⟩ := axis_mem_closure_side_components S h a r hr htrace x hx
    rcases heq with heq | heq
    · rw [heq]
      exact hpos
    · rw [heq]
      exact hneg

/-- Closure incidence propagates between any two axis points inside a regular chart. -/
theorem axis_mem_closure_component_iff_axis_mem_closure_component
    (S : Set X) (h : X ≃ₜ (ℝ × ℝ)) (a r : ℝ) (hr : 0 < r)
    (htrace : ∀ z ∈ axisBox a r, h.symm z ∈ S ↔ z.2 = 0)
    (p : X) (x y : ℝ) (hx : x ∈ Ioo (a - r) (a + r))
    (hy : y ∈ Ioo (a - r) (a + r)) :
    h.symm (x, 0) ∈ closure (connectedComponentIn Sᶜ p) ↔
    h.symm (y, 0) ∈ closure (connectedComponentIn Sᶜ p) :=
  (axis_mem_closure_component_iff S h a r hr htrace p x hx).trans
    (axis_mem_closure_component_iff S h a r hr htrace p y hy).symm

end LatticeProb.PlaneTopology
