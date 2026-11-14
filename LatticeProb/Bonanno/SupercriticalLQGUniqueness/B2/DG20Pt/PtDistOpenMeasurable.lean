/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenInfCompact
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffSq

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_measurable_crossLenIn_open
    {Ω : Type*} [MeasurableSpace Ω] (ξ : ℝ)
    (U A B : Set ℂ) (hU : IsOpen U)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => crossLenIn ξ (fun x => Y x ω) U A B := by
  obtain ⟨J, hJc, hJU, hcover⟩ := pt_dist_open_compact_exhaustion hU
  have heq : (fun ω => crossLenIn ξ (fun x => Y x ω) U A B) =
      (fun ω => ⨅ n, crossLenIn ξ (fun x => Y x ω) (J n) A B) := by
    funext ω
    exact pt_dist_crossLenIn_eq_iInf_compacts ξ (fun x => Y x ω)
      U A B J hJU hcover
  rw [heq]
  exact Measurable.iInf fun n => measurable_crossLenIn (hJc n) hYc hYm

theorem pt_dist_measurable_lfppDOn_open
    {Ω : Type*} [MeasurableSpace Ω] (ξ : ℝ)
    (U : Set ℂ) (hU : IsOpen U) (z w : ℂ)
    {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) :
    Measurable fun ω => lfppDOn ξ (fun x => Y x ω) U z w := by
  have h := pt_dist_measurable_crossLenIn_open ξ U {z} {w} hU hYc hYm
  simpa only [LQGMetric.DFGPS.crossLenIn_singleton] using h

end SupercriticalLQGUniqueness.B2.DG20Pt
