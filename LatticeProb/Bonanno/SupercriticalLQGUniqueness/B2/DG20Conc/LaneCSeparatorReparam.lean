/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorReparam at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorRatioLoop
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 

theorem laneC_seg_image_Icc
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    (SupercriticalLQGUniqueness.B2.Strong.seg ρ a b) '' Icc (0 : ℝ) 1 =
      ρ '' Icc a b := by
  let p : ℝ → ℝ := fun u => a + u * (b - a)
  have hpcont : ContinuousOn p (Icc (0 : ℝ) 1) := by
    fun_prop
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨p u,
      SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
        (a := a) (b := b) (left_mem_Icc.mpr hab)
        (right_mem_Icc.mpr hab) hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    have hmem : u ∈ Icc (p 0) (p 1) := by
      simpa [p] using hu
    obtain ⟨t, ht, hpt⟩ := intermediate_value_Icc zero_le_one hpcont hmem
    refine ⟨t, ht, ?_⟩
    change ρ (p t) = ρ u
    rw [hpt]

 

theorem laneC_separator_ratio_loop
    (D : ContMetric)
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ t ∈ Icc a b,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r))) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      let σ := SupercriticalLQGUniqueness.B2.Strong.seg ρ a b
      let τ := SupercriticalLQGUniqueness.B2.Strong.seg σ s t
      τ 0 = τ 1 ∧ D.len τ 0 1 ≤ D.len ρ a b ∧
      ∃ (G : C(unitInterval, ℂ)) (hG : ∀ u, G u ≠ 0),
        (∀ u, G u = (τ u - c) / (τ u - v)) ∧
        QuantumZipper.CA.Topo.loopDeg G hG ≠ 0 := by
  let σ := SupercriticalLQGUniqueness.B2.Strong.seg ρ a b
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hσ : ContinuousOn σ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ ha hb
  have hσann : ∀ u ∈ Icc (0 : ℝ) 1,
      r < dist (σ u) c ∧ dist (σ u) c < 2 * r := by
    intro u hu
    exact hρann _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem ha hb hu)
  have hσsep : LQGMetric.Disconnects (σ '' Icc (0 : ℝ) 1)
      (sphere c r) (sphere c (2 * r)) := by
    rw [laneC_seg_image_Icc hab]
    exact hsep
  obtain ⟨s, hs, t, ht, heq, hlen, G, hG, hGdef, hdeg⟩ :=
    laneC_normalized_separator_ratio_loop D hσ hr hσann hv hσsep
  refine ⟨s, hs, t, ht, ?_, ?_, G, hG, hGdef, hdeg⟩
  · simpa only [SupercriticalLQGUniqueness.B2.Strong.seg_zero,
      SupercriticalLQGUniqueness.B2.Strong.seg_one] using heq
  · exact hlen.trans (SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) ha hb)

end SupercriticalLQGUniqueness.B2.DG20Conc
