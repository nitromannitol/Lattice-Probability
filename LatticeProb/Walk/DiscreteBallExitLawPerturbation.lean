import LatticeProb.Walk.DiscreteBallExitPerturbation
import LatticeProb.Walk.NestedStoppedCurveLaw
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicMeasureBridge
import LatticeProb.Prob.StoppedPathCoupling

/-! # Exit distributions under perturbations of vertex positions -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped ENNReal NNReal

namespace LatticeProb

/-- The exit-vertex law in a smaller set is obtained from the ambient walk. -/
theorem trajectoryLaw_map_exitPosition_of_subset {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (pos : V → Euc d) {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hA v).map (fun ω => pos (exitVertex B ω)) =
      (N.discreteHarmonicMeasure B hB v).map pos := by
  have h := congrArg (fun μ => μ.map CurveSpace.endPoint)
    (trajectoryLaw_map_stoppedPolygonalCurve_of_subset N pos hBA hA hB v)
  rw [N.stoppedPolygonalCurve_map_endPoint pos B hB v] at h
  rw [Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedPolygonalCurve pos B)] at h
  simpa only [Function.comp_def, stoppedPolygonalCurve_endPoint, exitVertex] using h

/-- The harmonic measures of two nearby embedded ball exits are close if the
reference walk has small oscillation between neighboring-radius exits except on
an event of controlled mass. -/
theorem levyProkhorovEDist_discrete_ball_exit_of_oscillation
    {d : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (p q : V → Euc d) (z : Euc d) (R δ η : ℝ)
    (hclose : ∀ v, dist (p v) (q v) ≤ δ) {A : Set V}
    (hpA : p ⁻¹' ball z R ⊆ A) (hqA : q ⁻¹' ball z R ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    (E : Set (ℕ → V)) (r : ℝ≥0) (hr : η + δ < (r : ℝ))
    (hbad : N.trajectoryLaw A hA v E ≤ (r : ℝ≥0∞))
    (hgood : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ω ∉ E →
      exitTime (p ⁻¹' ball z (R + δ)) ω ≠ ⊤ ∧
      ∀ i ∈ Icc ((exitTime (p ⁻¹' ball z (R - δ)) ω).untopD 0)
          ((exitTime (p ⁻¹' ball z (R + δ)) ω).untopD 0),
        ∀ j ∈ Icc ((exitTime (p ⁻¹' ball z (R - δ)) ω).untopD 0)
          ((exitTime (p ⁻¹' ball z (R + δ)) ω).untopD 0),
          dist (p (ω i)) (p (ω j)) ≤ η) :
    levyProkhorovEDist
      ((N.discreteHarmonicMeasure (p ⁻¹' ball z R) (fun w hw => hA w (hpA hw)) v).map p)
      ((N.discreteHarmonicMeasure (q ⁻¹' ball z R) (fun w hw => hA w (hqA hw)) v).map q) ≤
      (r : ℝ≥0∞) := by
  let P := N.trajectoryLaw A hA v
  let f : (ℕ → V) → Euc d := fun ω => p (exitVertex (p ⁻¹' ball z R) ω)
  let g : (ℕ → V) → Euc d := fun ω => q (exitVertex (q ⁻¹' ball z R) ω)
  have hf : Measurable f := (measurable_of_finite p).comp (measurable_exitVertex _)
  have hg : Measurable g := (measurable_of_finite q).comp (measurable_exitVertex _)
  have hmass : P {ω | (r : ℝ≥0∞) ≤ edist (f ω) (g ω)} ≤ (r : ℝ≥0∞) := by
    apply (measure_mono_ae ?_).trans hbad
    filter_upwards [hgood] with ω hω
    intro hfar
    by_contra hnot
    obtain ⟨hfinite, hosc⟩ := hω hnot
    have hdist := dist_discrete_ball_exit_le_of_oscillation p q ω z R δ η hclose hfinite hosc
    have hlt : dist (f ω) (g ω) < (r : ℝ) := lt_of_le_of_lt hdist hr
    have : edist (f ω) (g ω) < (r : ℝ≥0∞) := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_coe_iff dist_nonneg).2 hlt
    exact (not_lt_of_ge hfar) this
  have h := levyProkhorovEDist_map_le_of_bad P hf hg r hmass
  rw [trajectoryLaw_map_exitPosition_of_subset N p hpA hA (fun w hw => hA w (hpA hw)) v,
    trajectoryLaw_map_exitPosition_of_subset N q hqA hA (fun w hw => hA w (hqA hw)) v] at h
  exact h

end LatticeProb
end
