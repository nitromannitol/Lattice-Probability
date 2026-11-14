/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorCenterDegree

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_exists_paid_essential_loop
    (D : ContMetric)
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ t ∈ Icc a b,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r))) :
    ∃ τ : ℝ → ℂ, ContinuousOn τ (Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        r < dist (τ u) c ∧ dist (τ u) c < 2 * r) ∧
      τ 0 = τ 1 ∧ D.len τ 0 1 ≤ D.len ρ a b ∧
      ∃ (L : C(unitInterval, ℂ)) (hL : ∀ u, L u ≠ 0),
        (∀ u, L u = τ u - c) ∧
        QuantumZipper.CA.Topo.loopDeg L hL ≠ 0 := by
  obtain ⟨s, hs, t, ht, hclosed, hlen, G, hG, hGdef, hGdeg⟩ :=
    laneC_separator_ratio_loop D hab hρ hr hρann hv hsep
  let σ := SupercriticalLQGUniqueness.B2.Strong.seg ρ a b
  let τ := SupercriticalLQGUniqueness.B2.Strong.seg σ s t
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hσ : ContinuousOn σ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ ha hb
  have hτ : ContinuousOn τ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hσ hs ht
  have hτann : ∀ u ∈ Icc (0 : ℝ) 1,
      r < dist (τ u) c ∧ dist (τ u) c < 2 * r := by
    intro u hu
    have huσ := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs ht hu
    exact hρann _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem ha hb huσ)
  let L : C(unitInterval, ℂ) := ⟨fun u => τ u - c, by
    have hc : Continuous (fun u : unitInterval => τ u) :=
      hτ.comp_continuous continuous_subtype_val (fun u => u.2)
    exact hc.sub continuous_const⟩
  have hL : ∀ u, L u ≠ 0 := by
    intro u heq
    have h := (hτann u u.2).1
    have : τ u = c := sub_eq_zero.mp heq
    rw [this, dist_self] at h
    linarith
  have hdegEq := laneC_ratio_degree_eq_center_degree hτ hclosed hr hτann hv hG hGdef
  have hLdeg : QuantumZipper.CA.Topo.loopDeg L hL ≠ 0 := by
    intro hzero
    apply hGdeg
    simpa only [L] using hdegEq.trans hzero
  exact ⟨τ, hτ, hτann, hclosed, hlen, L, hL, (fun _ => rfl), hLdeg⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
