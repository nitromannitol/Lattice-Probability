/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorLoopSeed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorNoLog
import Mathlib.Topology.Order.ProjIcc

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_normalized_separator_lifted_return
    {ρ : ℝ → ℂ} (hρ : ContinuousOn ρ (Icc (0 : ℝ) 1))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ t ∈ Icc (0 : ℝ) 1,
      r < dist (ρ t) c ∧ dist (ρ t) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc (0 : ℝ) 1)
      (sphere c r) (sphere c (2 * r))) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = (ρ t - c) / (ρ t - v)) ∧
      ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        ρ s = ρ t ∧ L s ≠ L t := by
  have hcv : ∀ t ∈ Icc (0 : ℝ) 1, ρ t ≠ v := by
    intro t ht heq
    have h := (hρann t ht).2
    rw [heq] at h
    linarith
  have hcc : ∀ t ∈ Icc (0 : ℝ) 1, ρ t ≠ c := by
    intro t ht heq
    have h := (hρann t ht).1
    rw [heq, dist_self] at h
    linarith
  let G : C(unitInterval, ℂ) := ⟨fun t => (ρ t - c) / (ρ t - v), by
    have hc : Continuous (fun t : unitInterval => ρ t) :=
      hρ.comp_continuous continuous_subtype_val (fun t => t.2)
    exact (hc.sub continuous_const).div (hc.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hcv t t.2))⟩
  have hG : ∀ t : unitInterval, G t ≠ 0 := by
    intro t
    exact div_ne_zero (sub_ne_zero.mpr (hcc t t.2))
      (sub_ne_zero.mpr (hcv t t.2))
  obtain ⟨M, hM⟩ := QuantumZipper.CA.Topo.exists_lift_exp G hG
  let L : ℝ → ℂ := fun t => M (projIcc 0 1 zero_le_one t)
  have hL : ContinuousOn L (Icc (0 : ℝ) 1) :=
    (M.continuous.comp continuous_projIcc).continuousOn
  have hExp : ∀ t ∈ Icc (0 : ℝ) 1,
      Complex.exp (L t) = (ρ t - c) / (ρ t - v) := by
    intro t ht
    simpa [L, G, projIcc_of_mem zero_le_one ht] using hM ⟨t, ht⟩
  have hNoLog : ¬ QuantumZipper.CA.Topo.HasLogOn
      (fun z => (z - c) / (z - v)) (ρ '' Icc (0 : ℝ) 1) :=
    laneC_separator_has_no_ratio_log
      (isCompact_Icc.image_of_continuousOn hρ)
      hr (by rintro z ⟨t, ht, rfl⟩; exact hρann t ht) hv hsep
  obtain ⟨s, hs, t, ht, heq, hne⟩ :=
    laneC_exists_fiber_lift_disagreement hρ hL hExp hNoLog
  exact ⟨L, hL, hExp, s, hs, t, ht, heq, hne⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
