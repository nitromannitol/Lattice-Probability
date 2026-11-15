import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOFinal

/-! # Joint scaling for the cone field and its area-parametrized curve -/

set_option autoImplicit false

open MeasureTheory Set LQGMetric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped NNReal

namespace LatticeProb

/-- The cone field and the original area-parametrized curve have the same joint
law after scaling by a positive area factor. -/
theorem cone_actual_joint_scaling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {b : ℝ} (hb : 0 < b)
    (S : Set (DistC × C(ℝ, ℂ))) (hS : MeasurableSet S) :
    P {ω | (CellScaling.coneRescaleField γ
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω)) ∈ S} =
      P {ω | (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), η ω) ∈ S} := by
  have h := CellScaling.JointScalingO.coneJointScaling_holds D hstd hγ b hb S hS
  change P {ω | (CellScaling.coneRescaleField γ
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (MoTInput.bundleCurve D ω)) ∈ S} =
      P {ω | (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω),
        MoTInput.bundleCurve D ω) ∈ S} at h
  have heq := MoTInput.ae_bundleCurve_eq D
  have hleft : {ω | (CellScaling.coneRescaleField γ
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b (η ω)) ∈ S}
      =ᵐ[P] {ω | (CellScaling.coneRescaleField γ
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve
          (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (MoTInput.bundleCurve D ω)) ∈ S} := by
    filter_upwards [heq] with ω hω
    simp only [hω]
  have hright : {ω | (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω),
        MoTInput.bundleCurve D ω) ∈ S} =ᵐ[P]
      {ω | (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), η ω) ∈ S} := by
    filter_upwards [heq] with ω hω
    simp only [hω]
  exact (measure_congr hleft).trans (h.trans (measure_congr hright))

end LatticeProb
