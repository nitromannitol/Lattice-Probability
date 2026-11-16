import LatticeProb.Topology.EqualGapCollapseRetained

/-! # Continuity of equal-image gap filling -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Filling the gaps of a closed set with their common endpoint images preserves
continuity. Outside the given interval the original map is unchanged. -/
theorem continuous_equalGapCollapse {Y : Type*} [PseudoMetricSpace Y]
    (f : ℝ → Y) {K : Set ℝ} (hK : IsClosed K) {a b : ℝ}
    (ha : a ∈ K) (hb : b ∈ K)
    (hgap : ∀ u ∈ K, ∀ v ∈ K, u < v →
      (∀ w ∈ K, ¬ (u < w ∧ w < v)) → f u = f v)
    (hf : Continuous f) : Continuous (equalGapCollapse f hK ha hb hgap) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxK : x ∈ K
  · exact continuousAt_equalGapCollapse_of_mem f hK ha hb hgap hxK hf.continuousAt
  · by_cases hx : x ∈ Icc a b
    · have hax : a < x := lt_of_le_of_ne hx.1 (fun h => hxK (h ▸ ha))
      have hxb : x < b := lt_of_le_of_ne hx.2 (fun h => hxK (h ▸ hb))
      obtain ⟨u, hu, v, hv, hux, hxv, huv, hfree⟩ :=
        exists_equal_gap_bracketing_point f hK ha hb hx hgap
      have hux' : u < x := lt_of_le_of_ne hux (fun h => hxK (h ▸ hu))
      have hxv' : x < v := lt_of_le_of_ne hxv (fun h => hxK (h.symm ▸ hv))
      have hneigh : Ioo u v ∩ Ioo a b ∈ 𝓝 x :=
        (isOpen_Ioo.inter isOpen_Ioo).mem_nhds ⟨⟨hux', hxv'⟩, ⟨hax, hxb⟩⟩
      have heq : equalGapCollapse f hK ha hb hgap =ᶠ[𝓝 x] fun _ => f u := by
        filter_upwards [hneigh] with y hy
        exact equalGapCollapse_eq_of_bracket f hK ha hb hgap
          ⟨hy.2.1.le, hy.2.2.le⟩ hu hy.1.1.le hy.1.2.le huv hfree
      exact heq.continuousAt
    · have hneigh : (Icc a b)ᶜ ∈ 𝓝 x := isClosed_Icc.isOpen_compl.mem_nhds hx
      have heq : equalGapCollapse f hK ha hb hgap =ᶠ[𝓝 x] f := by
        filter_upwards [hneigh] with y hy
        simp only [equalGapCollapse, dite_eq_right hy]
      exact (continuousAt_congr heq).2 hf.continuousAt

end LatticeProb
