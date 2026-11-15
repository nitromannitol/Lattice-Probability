import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Basic

/-! # Curve images from almost-everywhere interval visits -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- If the visits of a continuous curve to an open set on a nondegenerate
segment agree almost everywhere with a nondegenerate subinterval, and the
segment covers the open set, the subinterval image is its closure. -/
theorem image_Icc_eq_closure_of_ae_open_visits
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (μ : Measure ℝ) [Measure.IsOpenPosMeasure μ]
    (η : ℝ → X) (U : Set X) {a b A B : ℝ}
    (hη : Continuous η) (hU : IsOpen U) (hab : a < b)
    (haA : a ≤ A) (hAB : A < B) (hBb : B ≤ b)
    (hcover : U ⊆ η '' Icc a b)
    (hae : ∀ᵐ t ∂(μ.restrict (Icc a b)), η t ∈ U ↔ t ∈ Ioo A B) :
    η '' Icc A B = closure U := by
  have hgood : ∀ᵐ t ∂μ, t ∈ Icc a b → (η t ∈ U ↔ t ∈ Ioo A B) :=
    (ae_restrict_iff' isClosed_Icc.measurableSet).mp hae
  have hd : Dense {t : ℝ | t ∈ Icc a b → (η t ∈ U ↔ t ∈ Ioo A B)} :=
    μ.dense_of_ae hgood
  have hclosed : IsClosed ((η ⁻¹' U)ᶜ ∪ Icc A B) :=
    (hU.preimage hη).isClosed_compl.union isClosed_Icc
  have hinner : Ioo a b ⊆ (η ⁻¹' U)ᶜ ∪ Icc A B := by
    intro t ht
    by_contra hn
    have htU : η t ∈ U := by simpa using (not_or.mp hn).1
    have htI : t ∉ Icc A B := (not_or.mp hn).2
    let V := Ioo a b ∩ (η ⁻¹' U) ∩ (Icc A B)ᶜ
    have hV : IsOpen V := (isOpen_Ioo.inter (hU.preimage hη)).inter isClosed_Icc.isOpen_compl
    obtain ⟨x, hxgood, hx⟩ := hd.exists_mem_open hV ⟨t, ⟨ht, htU⟩, htI⟩
    have hxAB := (hxgood ⟨hx.1.1.1.le, hx.1.1.2.le⟩).mp hx.1.2
    exact hx.2 ⟨hxAB.1.le, hxAB.2.le⟩
  have hbound : Icc a b ⊆ (η ⁻¹' U)ᶜ ∪ Icc A B := by
    rw [← closure_Ioo hab.ne]
    exact closure_minimal hinner hclosed
  have hclosed' : IsClosed (η ⁻¹' closure U) := isClosed_closure.preimage hη
  have hinner' : Ioo A B ⊆ η ⁻¹' closure U := by
    intro t ht
    by_contra hn
    let V := Ioo A B ∩ (η ⁻¹' closure U)ᶜ
    have hV : IsOpen V := isOpen_Ioo.inter hclosed'.isOpen_compl
    obtain ⟨x, hxgood, hx⟩ := hd.exists_mem_open hV ⟨t, ht, hn⟩
    have hxout : x ∈ Icc a b := ⟨haA.trans hx.1.1.le, hx.1.2.le.trans hBb⟩
    exact hx.2 (subset_closure ((hxgood hxout).mpr hx.1))
  have hsub : Icc A B ⊆ η ⁻¹' closure U := by
    rw [← closure_Ioo hAB.ne]
    exact closure_minimal hinner' hclosed'
  apply subset_antisymm
  · rintro x ⟨t, ht, rfl⟩
    exact hsub ht
  · apply closure_minimal _ (isCompact_Icc.image hη).isClosed
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hcover hx
    have hbnd := hbound ht
    exact ⟨t, hbnd.resolve_left (by simpa using hx), rfl⟩

end LatticeProb
