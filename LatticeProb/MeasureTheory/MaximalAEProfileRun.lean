import LatticeProb.MeasureTheory.MaximalAEConnectedRun
import LatticeProb.MeasureTheory.IntervalProfileOverlap
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Maximal almost-everywhere constant runs -/

set_option autoImplicit false

open Set MeasureTheory Filter

namespace LatticeProb

/-- A maximal almost-everywhere constant run absorbs every overlapping open
preconnected set on which the same function is almost everywhere constant. -/
theorem exists_maximal_ae_profile_run
    {α β : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyConnectedSpace α] [MeasurableSpace α]
    (μ : Measure α) [μ.IsOpenPosMeasure] (s : Set α) (f : α → β) (c : β) (x : α)
    (hx : ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ V ⊆ s ∧
      ∀ᵐ y ∂(μ.restrict V), f y = c) :
    ∃ C : Set α, IsOpen C ∧ IsPreconnected C ∧ x ∈ C ∧ C ⊆ s ∧
      (∀ᵐ y ∂(μ.restrict C), f y = c) ∧
      ∀ V : Set α, IsOpen V → IsPreconnected V → V ⊆ s →
        (C ∩ V).Nonempty → ∀ d : β,
        (∀ᵐ y ∂(μ.restrict V), f y = d) → d = c ∧ V ⊆ C := by
  obtain ⟨C, hCopen, hCconn, hxC, hCs, hCae, hmax⟩ :=
    exists_maximal_connected_open_ae_run μ s (fun y => f y = c) x hx
  refine ⟨C, hCopen, hCconn, hxC, hCs, hCae, ?_⟩
  intro V hVopen hVconn hVs hCV d hVae
  have hpos : μ (C ∩ V) ≠ 0 := ne_of_gt ((hCopen.inter hVopen).measure_pos μ hCV)
  have hcd : c = d :=
    ae_constants_eq_of_overlap μ C V f f c d hpos hCae hVae (Eventually.of_forall fun _ => rfl)
  have hVae' : ∀ᵐ y ∂(μ.restrict V), f y = c := by simpa only [hcd] using hVae
  have hunion : C ∪ V ⊆ C := hmax (C ∪ V) (hCopen.union hVopen)
    (hCconn.union' hCV hVconn) (Or.inl hxC) (union_subset hCs hVs)
    ((ae_restrict_union_iff C V (fun y => f y = c)).2 ⟨hCae, hVae'⟩)
  exact ⟨hcd.symm, subset_union_right.trans hunion⟩

end LatticeProb
