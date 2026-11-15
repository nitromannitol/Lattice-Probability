import LatticeProb.Gauss.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeOfFun
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleKolm

/-! # Circle averages of logarithmically shifted fields -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric MatedCRTHarmonic MatedCRTHarmonic.LQGCoord

namespace LatticeProb.LQG

/-- On one event, the circle averages of a logarithmically shifted whole-plane
field agree with the inserted profile for almost every center at every positive radius. -/
theorem ae_logInsertion_circleAvg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ᵐ z ∂(volume : Measure ℂ),
      Gauss.fieldCircleAverage α (fun s w => circleAvg (X ω) s w) r z =
        circleAvg (GMSCase.addLogSing α (X ω)) r z := by
  filter_upwards [ae_tendsto_mollAvgS_circleAvg hX] with ω hω r hr
  filter_upwards [ae_norm_ne r] with z hz
  have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))
  have hlim : Tendsto (fun n => LQGMetric.CircleAvg.mollAvg (X ω) n z r) atTop
      (𝓝 (circleAvg (X ω) r z)) := by
    exact ((hω.2 r hr z).comp ht).congr fun n => mollAvgS_dyadic _ n z r
  have hc : ContinuousOn (GMSCase.logSing α) ({0}ᶜ : Set ℂ) := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact (continuousAt_const.mul ((continuousAt_id.norm.log (norm_ne_zero_iff.mpr hx0)).neg)).continuousWithinAt
  have he := MoTPort.ConeArea3.circleAvg_add_ofFunC (GMSCase.locallyIntegrable_logSing α)
    isOpen_compl_singleton hc hr (sphere_subset_compl_zero hz) hlim
  have havg : Real.circleAverage (GMSCase.logSing α) z r =
      -(α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z r) := by
    have hf : GMSCase.logSing α = (-α) • (fun x : ℂ => Real.log ‖x‖) := by
      funext x
      simp [GMSCase.logSing, smul_eq_mul]
    rw [hf, Real.circleAverage_smul]
    simp [smul_eq_mul]
  rw [GMSCase.addLogSing, he, havg]
  simp [Gauss.fieldCircleAverage, sub_eq_add_neg]

end LatticeProb.LQG
