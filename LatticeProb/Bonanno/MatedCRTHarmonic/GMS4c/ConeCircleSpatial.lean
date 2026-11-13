/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4c.ConeCircleSpatial at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: the convert step now closes the goal (the trailing funext/rfl removed). -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeRadial
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeOfFun
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaApprox

/-! Spatial continuity of cone circle averages away from circles through zero. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal

namespace MatedCRTHarmonic.GMS4c

open LQGMetric MatedCRTHarmonic.LQGCoord MatedCRTHarmonic.CellScaling

private theorem continuous_circleAverage_center (g : C(ℂ, ℝ)) (ρ : ℝ) :
    Continuous fun w : ℂ => Real.circleAverage g w ρ := by
  have h : Continuous (fun w : ℂ => ∫ θ in (0 : ℝ)..2 * π,
      g (circleMap w ρ θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun w : ℂ => fun θ : ℝ => g (circleMap w ρ θ))
    change Continuous fun p : ℂ × ℝ => g (circleMap p.1 ρ p.2)
    unfold circleMap
    fun_prop
  change Continuous fun w : ℂ => (2 * π)⁻¹ •
    ∫ θ in (0 : ℝ)..2 * π, g (circleMap w ρ θ)
  convert h.const_smul ((2 * π)⁻¹) using 1

/-- A function continuous away from zero has a circle average continuous
in the center whenever the circle avoids zero. -/
private theorem continuousAt_circleAverage_center_off_zero
    {g : ℂ → ℝ} (hg : ContinuousOn g {0}ᶜ)
    {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ‖w‖ ≠ ρ) :
    ContinuousAt (fun x : ℂ => Real.circleAverage g x ρ) w := by
  obtain ⟨δ, hδ, G, hG⟩ :=
    MoTPort.ConeArea3.exists_continuous_eqOn_thickening
      isOpen_compl_singleton hg (isCompact_sphere w ρ)
      (sphere_subset_compl_zero hw)
  have heq : (fun x : ℂ => Real.circleAverage g x ρ) =ᶠ[𝓝 w]
      fun x => Real.circleAverage G x ρ := by
    filter_upwards [Metric.ball_mem_nhds w hδ] with x hx
    apply Real.circleAverage_congr_sphere
    intro y hy
    have hmem : y + (w - x) ∈ sphere w ρ := by
      rw [mem_sphere, dist_eq_norm]
      have heq : y + (w - x) - w = y - x := by abel
      rw [heq]
      simpa [mem_sphere, dist_eq_norm, abs_of_pos hρ] using hy
    have hdist : dist y (y + (w - x)) < δ := by
      rw [dist_eq_norm]
      have heq : y - (y + (w - x)) = x - w := by abel
      rw [heq]
      simpa [mem_ball, dist_eq_norm] using hx
    exact (hG (mem_thickening_iff.2 ⟨y + (w - x), hmem, hdist⟩)).symm
  exact (continuous_circleAverage_center G ρ).continuousAt.congr_of_eventuallyEq heq

/-- The cone correction preserves spatial continuity of circle averages
away from the circle of centers whose averaging circle passes through zero. -/
theorem continuousAt_circleAvg_cone_off_resonance
    {X : DistC} {g₁ g₂ : ℂ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hl₁ : LocallyIntegrable g₁ volume) (hl₂ : LocallyIntegrable g₂ volume)
    (hc₁ : ContinuousOn g₁ {0}ᶜ) (hc₂ : ContinuousOn g₂ {0}ᶜ)
    (hXcont : ContinuousOn (fun p : ℝ × ℂ => circleAvg X p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hXscale : ∀ w : ℂ,
      Tendsto (fun s => mollAvgS X s w ρ) (𝓝[>] 0) (𝓝 (circleAvg X ρ w)))
    {z : ℂ} (hz : ‖z‖ ≠ ρ) :
    ContinuousAt (fun w => circleAvg (X - ofFunC g₁ + ofFunC g₂) ρ w) z := by
  have hmem : (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) ∈ 𝓝 ((ρ, z) : ℝ × ℂ) :=
    (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨mem_Ioi.mpr hρ, mem_univ _⟩
  have hbase : ContinuousAt (fun p : ℝ × ℂ => circleAvg X p.1 p.2) (ρ, z) :=
    hXcont.continuousAt hmem
  have hinput : ContinuousAt (fun w : ℂ => ((ρ, w) : ℝ × ℂ)) z :=
    continuousAt_const.prodMk continuousAt_id
  have hXc : ContinuousAt (fun w : ℂ => circleAvg X ρ w) z :=
    hbase.comp hinput
  have h₁ := continuousAt_circleAverage_center_off_zero hc₁ hρ hz
  have h₂ := continuousAt_circleAverage_center_off_zero hc₂ hρ hz
  have heq : (fun w => circleAvg (X - ofFunC g₁ + ofFunC g₂) ρ w) =ᶠ[𝓝 z]
      fun w => circleAvg X ρ w - Real.circleAverage g₁ w ρ +
        Real.circleAverage g₂ w ρ := by
    have ho : IsOpen {w : ℂ | ‖w‖ ≠ ρ} :=
      isOpen_ne_fun continuous_norm continuous_const
    filter_upwards [ho.mem_nhds hz] with w hw
    exact circleAvg_cone hl₁ hl₂ hc₁ hc₂ hρ hw (hXscale w)
  exact ((hXc.sub h₁).add h₂).congr_of_eventuallyEq heq

theorem continuousAt_circleAvg_coneField_off_resonance
    {γ α : ℝ} {X : DistC} {b b' : ℝ≥0 → ℝ}
    (hr : RadialGood γ α X b b')
    (hscale : ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
      Tendsto (fun s => mollAvgS X s w ρ) (𝓝[>] 0)
        (𝓝 (circleAvg X ρ w)))
    {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : ‖z‖ ≠ ρ) :
    ContinuousAt (fun w => circleAvg (coneField X (coneRadial γ α b b')) ρ w) z := by
  have hc₁ := continuousOn_radialAvg hr.good
  have hc₂ := continuousOn_coneProfile hr
  obtain ⟨C₁, hC₁⟩ := abs_radialAvg_le hr one_pos
  obtain ⟨C₂, hC₂⟩ := abs_coneProfile_le hr one_pos
  have hl₁ : LocallyIntegrable (radialAvg X) volume :=
    locallyIntegrable_of_logBound (measurable_radialAvg X) hc₁ hC₁
  have hl₂ : LocallyIntegrable (coneProfile γ α b b') volume :=
    locallyIntegrable_of_logBound (measurable_coneProfile hr) hc₂
      (fun w h0 h1 => (hC₂ w h0 h1).1)
  rw [coneField_eq_cone]
  exact continuousAt_circleAvg_cone_off_resonance hρ hl₁ hl₂ hc₁ hc₂
    hr.good (hscale ρ hρ) hz

theorem continuousAt_localCircleProcess_restrictTo
    (V : TopologicalSpace.Opens ℂ) {δ ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ρ < δ) (h : DistC) {z : ℂ} (hz : z ∈ V)
    (hc : ContinuousAt (fun w => circleAvg h ρ w) z) :
    ContinuousAt (fun w => localCircleProcess (thickOpen V δ)
      (restrictTo (thickOpen V δ) h) ρ w) z := by
  have heq : (fun w => localCircleProcess (thickOpen V δ)
      (restrictTo (thickOpen V δ) h) ρ w) =ᶠ[𝓝 z]
      fun w => circleAvg h ρ w := by
    filter_upwards [V.isOpen.mem_nhds hz] with w hw
    have hball := closedBall_subset_thickOpen hsmall hw
    have hvalue := congrFun (congrFun
      (localCircleProcess_restrictTo (thickOpen V δ) h) ρ) w
    simpa [MatedCRTHarmonic.MatedCRT.restrictCircles, hρ, hball] using hvalue
  exact hc.congr_of_eventuallyEq heq

end MatedCRTHarmonic.GMS4c

