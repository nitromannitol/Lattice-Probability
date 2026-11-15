import LatticeProb.LQG.ConeInnerWindowMass
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaScalingHolds
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.ConeRealization

/-! # Inner window containment and cone area scaling -/

set_option autoImplicit false

open MeasureTheory Set Metric MatedCRTHarmonic MatedCRTHarmonic.MatedCRT
open scoped ENNReal NNReal

namespace LatticeProb

/-- An inner half-window contained in the cone-scale ball is controlled by a
unit-ball mass tail under the same cone law. -/
theorem measure_cone_inner_window_containment_le_unit_mass_tail
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (μ : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsVagueLimitC (lqgAreaApprox γ
      (coneField (X ω) (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω)))) (μ ω))
    (b w : ℝ) (hb : 0 < b) (hw : 0 ≤ w) :
    P {ω | let L := CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b
      η ω '' Icc (0 - w / 2) 0 ⊆ ball 0 L ∨
        η ω '' Icc 0 (0 + w / 2) ⊆ ball 0 L} ≤
    P {ω | ENNReal.ofReal b⁻¹ * ENNReal.ofReal (w / 2) ≤
      CellScaling.lqgArea γ (CellScaling.coneFieldOf γ (X ω)
        (fun s => B s ω) (fun s => B' s ω)) (ball 0 1)} := by
  let R := MoTInput.coneRealizationOfCoupling D hstd hγ
  have hlaw := ConeScaling.areaScalingLaw_holds R b hb
    (Ici (ENNReal.ofReal b⁻¹ * ENNReal.ofReal (w / 2))) measurableSet_Ici
  change P {ω | ENNReal.ofReal b⁻¹ * CellScaling.lqgArea γ
      (CellScaling.coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))
      (ball 0 (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)) ∈
      Ici (ENNReal.ofReal b⁻¹ * ENNReal.ofReal (w / 2))} = _ at hlaw
  calc
    _ ≤ P {ω | ENNReal.ofReal (w / 2) ≤ μ ω (ball 0
        (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b))} :=
      measure_cone_inner_window_containment_le_mass_tail D μ hμ b w hw
    _ ≤ P {ω | ENNReal.ofReal b⁻¹ * CellScaling.lqgArea γ
        (CellScaling.coneFieldOf γ (X ω) (fun s => B s ω) (fun s => B' s ω))
        (ball 0 (CellScaling.coneScale γ γ (fun s => B s ω) (fun s => B' s ω) b)) ∈
        Ici (ENNReal.ofReal b⁻¹ * ENNReal.ofReal (w / 2))} := by
      apply measure_mono_ae
      filter_upwards [hμ] with ω hlim hmass
      have heq := LQGCoord.lqgArea_eq_of_isVagueLimitC hlim
      change CellScaling.lqgArea γ (CellScaling.coneFieldOf γ (X ω)
        (fun s => B s ω) (fun s => B' s ω)) = μ ω at heq
      change ENNReal.ofReal b⁻¹ * ENNReal.ofReal (w / 2) ≤ _
      rw [heq]
      gcongr
    _ = _ := hlaw

end LatticeProb
