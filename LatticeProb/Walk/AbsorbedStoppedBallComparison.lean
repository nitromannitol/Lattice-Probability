import LatticeProb.Walk.AbsorbedBallExitCoverage
import LatticeProb.Walk.CellConfigStoppedBallOscillation
import LatticeProb.Prob.OpenExitTimeReparam

/-! # Stopped ball comparison for terminal-absorbed paths -/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- Absorbing a path at a point outside a set preserves its first exit time. -/
theorem openExitTime_min_eq_of_terminal_not_mem
    {E : Type*} (f : ℝ≥0 → E) (U : Set E) (T : ℝ≥0) (hT : f T ∉ U) :
    openExitTime (fun t (_ : Unit) => f (min t T)) U () =
      openExitTime (fun t (_ : Unit) => f t) U () := by
  apply le_antisymm
  · apply le_iInf
    intro t
    by_cases ht : t.val ≤ T
    · exact openExitTime_le_of_not_mem (by simpa only [min_eq_left ht] using t.property)
    · have h := openExitTime_le_of_not_mem (B := fun s (_ : Unit) => f (min s T))
        (ω := ()) (t := T) (by simpa only [min_self] using hT)
      exact h.trans (ENNReal.coe_le_coe.mpr (le_of_not_ge ht))
  · apply le_iInf
    intro t
    exact (openExitTime_le_of_not_mem (B := fun s (_ : Unit) => f s)
      (ω := ()) (t := min t.val T) t.property).trans
        (ENNReal.coe_le_coe.mpr (min_le_left _ _))

/-- Uniformly close terminal-absorbed paths remain close after stopping at
inner-ball exits when the reference path has small neighboring-exit
oscillation and its terminal point lies beyond the buffered ball. -/
theorem dist_stopped_ball_le_of_absorbed_dist_le
    {E : Type*} [PseudoMetricSpace E] (f g : ℝ≥0 → E)
    (T U : ℝ≥0) (φ : ℝ≥0 ≃o ℝ≥0) (z : E) (R e η : ℝ)
    (hf : Continuous f)
    (hclose : ∀ t, dist (f (min t T)) (g (min (φ t) U)) ≤ e)
    (hmargin : R + 2 * e ≤ dist (g U) z)
    (hosc : ∀ s ∈ Icc
        (openExitTime (fun t (_ : Unit) => g t) (Metric.ball z (R - e)) ()).toNNReal
        (openExitTime (fun t (_ : Unit) => g t) (Metric.ball z (R + e)) ()).toNNReal,
      ∀ t ∈ Icc
        (openExitTime (fun t (_ : Unit) => g t) (Metric.ball z (R - e)) ()).toNNReal
        (openExitTime (fun t (_ : Unit) => g t) (Metric.ball z (R + e)) ()).toNNReal,
      dist (g s) (g t) ≤ η) (t : ℝ≥0) :
    dist (f (min t (openExitTime (fun s (_ : Unit) => f s) (Metric.ball z R) ()).toNNReal))
      (g (min (φ t) (openExitTime (fun s (_ : Unit) => g s) (Metric.ball z R) ()).toNNReal)) ≤ e + η := by
  have he : 0 ≤ e := (dist_nonneg : 0 ≤ dist (f (min 0 T)) (g (min (φ 0) U))).trans (hclose 0)
  have hc : dist (f T) (g U) ≤ e := by
    simpa only [min_eq_right (le_max_left T (φ.symm U)),
      min_eq_right (show U ≤ φ (max T (φ.symm U)) by simp)] using hclose (max T (φ.symm U))
  have hfout : f T ∉ Metric.ball z (R + e) := by
    simp only [Metric.mem_ball, not_lt]
    linarith [dist_triangle (g U) (f T) z, dist_comm (g U) (f T)]
  have hgout : g U ∉ Metric.ball z (R + e) := by
    simp only [Metric.mem_ball, not_lt]
    linarith
  have hgout' (r : ℝ) (hr : r ≤ R + e) : g U ∉ Metric.ball z r := by
    simp only [Metric.mem_ball, not_lt] at hgout ⊢
    linarith
  have hfout' : f T ∉ Metric.ball z R := by
    simp only [Metric.mem_ball, not_lt] at hfout ⊢
    linarith
  let F : ℝ≥0 → Unit → E := fun s _ => g (min s U)
  let G : ℝ≥0 → Unit → E := fun s _ => f (min (φ.symm s) T)
  have hF (r : ℝ) (hr : r ≤ R + e) :
      openExitTime F (Metric.ball z r) () =
        openExitTime (fun s (_ : Unit) => g s) (Metric.ball z r) () :=
    openExitTime_min_eq_of_terminal_not_mem g _ U (hgout' r hr)
  have hfinite : openExitTime F (Metric.ball z (R + e)) () ≠ ∞ := by
    rw [hF _ le_rfl]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem hgout)
  have hforig : openExitTime (fun s (_ : Unit) => f s) (Metric.ball z R) () ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem hfout')
  have hgorig : openExitTime (fun s (_ : Unit) => g s) (Metric.ball z R) () ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (openExitTime_le_of_not_mem (hgout' R (by linarith)))
  have hG : (openExitTime G (Metric.ball z R) ()).toNNReal =
      φ (openExitTime (fun s (_ : Unit) => f s) (Metric.ball z R) ()).toNNReal := by
    change (openExitTime (fun s (_ : Unit) => (fun u => f (min u T)) (φ.symm s))
      (Metric.ball z R) ()).toNNReal = _
    rw [openExitTime_comp_orderIso_toNNReal (fun u => f (min u T)) _ φ.symm
      Metric.isOpen_ball (hf.comp (continuous_id.min continuous_const))]
    · simp only [OrderIso.symm_symm]
      rw [openExitTime_min_eq_of_terminal_not_mem f _ T hfout']
    · rw [openExitTime_min_eq_of_terminal_not_mem f _ T hfout']
      exact hforig
  have hU : (openExitTime (fun s (_ : Unit) => g s)
      (Metric.ball z (R + e)) ()).toNNReal ≤ U := by
    have hfinite' := hfinite
    rw [hF _ le_rfl] at hfinite'
    apply ENNReal.toNNReal_le_toNNReal hfinite' ENNReal.coe_ne_top |>.2
    exact openExitTime_le_of_not_mem hgout
  have ho : ∀ s ∈ Icc (openExitTime F (Metric.ball z (R - e)) ()).toNNReal
      (openExitTime F (Metric.ball z (R + e)) ()).toNNReal,
      ∀ u ∈ Icc (openExitTime F (Metric.ball z (R - e)) ()).toNNReal
      (openExitTime F (Metric.ball z (R + e)) ()).toNNReal,
      dist (F s ()) (F u ()) ≤ η := by
    rw [hF _ (by linarith), hF _ le_rfl]
    intro s hs u hu
    simpa only [F, min_eq_left (hs.2.trans hU), min_eq_left (hu.2.trans hU)] using
      hosc s hs u hu
  have h := dist_stopped_openExitTime_ball_le_of_oscillation F G () z R e η
    (fun s => by
      have hs := hclose (φ.symm s)
      simpa only [F, G, φ.apply_symm_apply, dist_comm] using hs)
    hfinite ho (φ t)
  rw [hF _ (by linarith), hG] at h
  have hfT : (openExitTime (fun s (_ : Unit) => f s) (Metric.ball z R) ()).toNNReal ≤ T := by
    apply ENNReal.toNNReal_le_toNNReal hforig ENNReal.coe_ne_top |>.2
    exact openExitTime_le_of_not_mem hfout'
  have hgU : (openExitTime (fun s (_ : Unit) => g s) (Metric.ball z R) ()).toNNReal ≤ U := by
    apply ENNReal.toNNReal_le_toNNReal hgorig ENNReal.coe_ne_top |>.2
    exact openExitTime_le_of_not_mem (hgout' R (by linarith))
  simp only [F, G, OrderIso.map_inf, φ.symm_apply_apply,
    min_eq_left ((min_le_right _ _).trans hfT),
    min_eq_left ((min_le_right _ _).trans hgU), dist_comm] at h
  exact h

end LatticeProb
