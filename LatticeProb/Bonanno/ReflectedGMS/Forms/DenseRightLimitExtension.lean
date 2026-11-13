/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DenseRightLimitExtension at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Order.Cadlag

/-!
# Extending one-sided limits from a time support

This adapts the closed-neighborhood proof of mathlib's
`continuousWithinAt_rightLim_Ici` to limits taken only along a support `S`.
Nontrivial right-neighborhood filters express the needed local density.
-/

set_option autoImplicit false

open Set Filter Topology

namespace ReflectedGMS

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [TopologicalSpace β] [T3Space β] {S : Set α} {f g : α → β}

/-- Limits from the right on a locally dense support define a right-continuous
extension, even when the original function is unspecified outside the support. -/
theorem continuousWithinAt_of_supported_right_limits
    (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (hg : ∀ t, Tendsto f (𝓝[S ∩ Ioi t] t) (𝓝 (g t))) (t : α) :
    ContinuousWithinAt g (Ici t) t := by
  apply (closed_nhds_basis (g t)).tendsto_right_iff.2
  rintro C ⟨hC, hclosed⟩
  obtain ⟨U, hU, hUC⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hg t hC)
  obtain ⟨O, hOU, hO, htO⟩ := mem_nhds_iff.1 hU
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds htO),
    self_mem_nhdsWithin] with s hsO hts
  rcases eq_or_lt_of_le hts with rfl | hts
  · exact mem_of_mem_nhds hC
  · letI := hS s
    apply hclosed.mem_of_tendsto (hg s)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hsO),
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hts),
      self_mem_nhdsWithin] with r hrO htr hrS
    exact hUC ⟨hOU hrO, hrS.1, htr⟩

/-- A left limit on the same support is retained by its right-limit extension. -/
theorem tendsto_left_of_supported_right_limits
    (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (hg : ∀ t, Tendsto f (𝓝[S ∩ Ioi t] t) (𝓝 (g t)))
    {t : α} {l : β} (hl : Tendsto f (𝓝[S ∩ Iio t] t) (𝓝 l)) :
    Tendsto g (𝓝[<] t) (𝓝 l) := by
  apply (closed_nhds_basis l).tendsto_right_iff.2
  rintro C ⟨hC, hclosed⟩
  obtain ⟨U, hU, hUC⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hl hC)
  obtain ⟨O, hOU, hO, htO⟩ := mem_nhds_iff.1 hU
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds htO),
    self_mem_nhdsWithin] with s hsO hst
  letI := hS s
  apply hclosed.mem_of_tendsto (hg s)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hsO),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hst),
    self_mem_nhdsWithin] with r hrO hrt hrS
  exact hUC ⟨hOU hrO, hrS.1, hrt⟩

/-- The right-limit extension is càdlàg once both one-sided limits exist on
its locally dense time support. -/
theorem isCadlag_of_supported_one_sided_limits
    (hS : ∀ t, (𝓝[S ∩ Ioi t] t).NeBot)
    (hg : ∀ t, Tendsto f (𝓝[S ∩ Ioi t] t) (𝓝 (g t)))
    (hl : ∀ t, ∃ l, Tendsto f (𝓝[S ∩ Iio t] t) (𝓝 l)) :
    IsCadlag g where
  isRightContinuous t :=
    (continuousWithinAt_of_supported_right_limits hS hg t).mono Ioi_subset_Ici_self
  tendsto_nhdsLT t := by
    obtain ⟨l, hlt⟩ := hl t
    exact ⟨l, tendsto_left_of_supported_right_limits hS hg hlt⟩

end ReflectedGMS
