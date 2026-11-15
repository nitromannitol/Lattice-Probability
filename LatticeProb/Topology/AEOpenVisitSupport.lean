import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Closed supports of open visit times -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Open sets that agree almost everywhere on an open set have the same local closure. -/
theorem closure_inter_eq_of_ae_mem_iff
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [Measure.IsOpenPosMeasure μ] {U V W : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (h : ∀ᵐ x ∂(μ.restrict W), x ∈ U ↔ x ∈ V) :
    closure (U ∩ W) = closure (V ∩ W) := by
  have hd : Dense {x : X | x ∈ W → (x ∈ U ↔ x ∈ V)} :=
    μ.dense_of_ae (ae_imp_of_ae_restrict h)
  apply subset_antisymm
  · apply closure_minimal _ isClosed_closure
    refine (hd.open_subset_closure_inter (hU.inter hW)).trans ?_
    apply closure_mono
    intro x hx
    exact ⟨(hx.2 hx.1.2).mp hx.1.1, hx.1.2⟩
  · apply closure_minimal _ isClosed_closure
    refine (hd.open_subset_closure_inter (hV.inter hW)).trans ?_
    apply closure_mono
    intro x hx
    exact ⟨(hx.2 hx.1.2).mpr hx.1.1, hx.1.2⟩

end LatticeProb
