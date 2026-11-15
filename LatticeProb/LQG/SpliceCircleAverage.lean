import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea

/-! # Circle averages of a radial replacement -/

/- The argument extends the proof of `ae_circleAvg_replField_one` in Leonardo
Bonanno's lean-formalizations, MatedCRTHarmonic.GMCFacts.ReplacedArea. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort
open MatedCRTHarmonic.GMCFacts

namespace LatticeProb.LQG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

/-- At a fixed positive radius, the circle average of a radial replacement
is the value of its radial path, provided that path defines a distribution. -/
theorem ae_circleAvg_replField (hX : IsWholePlaneGFF X P) (W : Ω → C(ℝ, ℝ))
    (hW : ∀ᵐ ω ∂P, LocallyIntegrable (radialW (W ω)) volume)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, circleAvg (replField X W ω) r 0 = W ω (-Real.log r) := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨H, hH, hR⟩ := ConeArea7.ae_radialFun_eq_version hX
  filter_upwards [hR, hH.ae_eq r hr 0, ae_tendsto_mollAvg hX 0 hr,
    ConeArea4.ae_radial_R2 hX, hW] with ω hR1 hH1 ⟨a, ha⟩ hR2 hWl
  set g : ℂ → ℝ := fun z => H ‖z‖ 0 ω
  obtain ⟨R, -, -, hRe, hRl⟩ := hR2
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  have hgl : LocallyIntegrable (fun z => -g z) volume := (hloc.congr hR1).neg
  have hgc : ContinuousOn (fun z => -g z) {z : ℂ | z ≠ 0} := by
    refine ((hH.cont ω).comp (f := fun z : ℂ => ((‖z‖, (0 : ℂ)) : ℝ × ℂ))
      (by fun_prop : Continuous fun z : ℂ => ((‖z‖, (0 : ℂ)) : ℝ × ℂ)).continuousOn
      fun z hz => ⟨norm_pos_iff.2 hz, mem_univ _⟩).neg
  have hca : circleAvg (X ω) r 0 = a := circleAvg_eq_of_tendsto ha
  have hcirc : Real.circleAverage (fun z => -g z) 0 r = -a := by
    refine Real.circleAverage_const_on_circle fun z hz => ?_
    rw [abs_of_pos hr, mem_sphere_zero_iff_norm] at hz
    simp only [g, hz]
    rw [hH1, hca]
  have hsphere : sphere (0 : ℂ) r ⊆ {z : ℂ | z ≠ 0} := fun z hz => by
    rw [mem_sphere_zero_iff_norm] at hz
    exact norm_ne_zero_iff.1 (by rw [hz]; exact hr.ne')
  have hlat : lateralPartC (X ω) = X ω + ofFunC (fun z => -g z) := by
    rw [lateralPartC, ConeArea3.ofFunC_congr_ae hR1, show (fun z => -g z) = -g from rfl,
      ofFunC, ofFunC, Distribution.ofFun_neg, sub_eq_add_neg]
  have hlatT : Tendsto (fun n => mollAvg (lateralPartC (X ω)) n 0 r) atTop (𝓝 0) := by
    rw [hlat]
    simp only [mollAvg_add]
    have := ha.add (ConeArea3.tendsto_mollAvg_ofFunC hgl isOpen_ne hgc hr hsphere)
    rwa [hcirc, add_neg_cancel] at this
  rw [replField, ConeArea3.circleAvg_add_ofFunC hWl isOpen_ne
    (continuousOn_radialW (W ω)) hr hsphere hlatT, circleAvg_eq_of_tendsto hlatT, zero_add]
  refine Real.circleAverage_const_on_circle fun z hz => ?_
  rw [abs_of_pos hr, mem_sphere_zero_iff_norm] at hz
  simp only [radialW, hz]

end LatticeProb.LQG
