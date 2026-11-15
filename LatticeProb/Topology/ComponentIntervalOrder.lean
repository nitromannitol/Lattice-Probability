import LatticeProb.Topology.ComponentVisitIdentity

/-! # Ordering intervals of disjoint curve regions -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Disjoint regions whose visits agree almost everywhere with nondegenerate
open intervals have disjoint time interiors, in one order or the other. -/
theorem interval_order_of_ae_visit_disjoint
    {E : Type*} (η : ℝ → E) (U V : Set E) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hUV : Disjoint U V)
    (hU : ∀ᵐ t ∂volume, η t ∈ U ↔ t ∈ Ioo a b)
    (hV : ∀ᵐ t ∂volume, η t ∈ V ↔ t ∈ Ioo c d) :
    b ≤ c ∨ d ≤ a := by
  have hnone : ∀ᵐ t ∂volume, t ∉ Ioo (max a c) (min b d) := by
    filter_upwards [hU, hV] with t htU htV ht
    have h1 : t ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have h2 : t ∈ Ioo c d := ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    exact Set.disjoint_left.mp hUV (htU.mpr h1) (htV.mpr h2)
  have hz : volume (Ioo (max a c) (min b d)) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hnone
  by_contra hn
  push Not at hn
  have hp : max a c < min b d := by
    apply max_lt <;> apply lt_min <;> linarith
  rw [Real.volume_Ioo] at hz
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp))) hz

/-- If two disjoint open regions are represented by interval images of a
measure-parametrized curve and have null frontiers, their intervals are ordered. -/
theorem interval_order_of_disjoint_open_curve_regions
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (U V : Set E) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hη : Measurable η)
    (hmap : Measure.map η volume = μ) (hUV : Disjoint U V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hfrontU : μ (frontier U) = 0) (hfrontV : μ (frontier V) = 0)
    (himageU : η '' Icc a b = closure U) (himageV : η '' Icc c d = closure V)
    (hmassU : μ (η '' Icc a b) = volume (Icc a b))
    (hmassV : μ (η '' Icc c d) = volume (Icc c d)) : b ≤ c ∨ d ≤ a :=
  interval_order_of_ae_visit_disjoint η U V hab hcd hUV
    (ae_visit_open_eq_interval η μ U a b hη hmap hU hfrontU himageU hmassU)
    (ae_visit_open_eq_interval η μ V c d hη hmap hV hfrontV himageV hmassV)

end LatticeProb
