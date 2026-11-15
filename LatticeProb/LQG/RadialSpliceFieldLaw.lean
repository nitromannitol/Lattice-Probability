import LatticeProb.LQG.RadialSpliceJointLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ReplacedArea
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldDecomp
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw

/-! # Law of the field obtained by replacing the interior radial path -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGMetric MatedCRTHarmonic.GMCFacts MatedCRTHarmonic.MoTPort

namespace LatticeProb.LQG

/-- Replacing the radial part by a centered continuous radial version preserves
all mean-zero pairings and yields a normalized whole-plane GFF. -/
theorem IsWholePlaneGFF.normalized_replField_radialVersion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}
    (hX : IsWholePlaneGFF X P) {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0) :
    IsNormalizedWPGFF (replField X (fun ω => R (X ω))) P := by
  have hρm : Measurable (fun ω => R (X ω)) := hRm.comp hX.measurable
  have he : ∀ φ : TestC0, (fun ω => replField X (fun ω => R (X ω)) ω φ.1) =ᵐ[P]
      fun ω => X ω φ.1 := by
    intro φ
    filter_upwards [ae_replField_apply hX (fun ω => R (X ω)) φ.1,
      ae_pairW_radialProcess hX hρm hR φ.2] with ω h1 h2
    rw [h1, h2, map_sub, sub_add_cancel]
  have hG : IsWholePlaneGFF (replField X (fun ω => R (X ω))) P := by
    refine ⟨measurable_replField hX.measurable hρm,
      hX.gaussian.congr (fun φ => (he φ).symm), ?_, ?_⟩
    · intro φ
      rw [integral_congr_ae (he φ), hX.centered]
    · intro φ ψ
      rw [LQGMetric.CircleAvg.covariance_congr_ae (he φ) (he ψ), hX.covariance_eq]
  let ρ₀ : Ω → C(ℝ, ℝ) := fun ω => R (X ω) - ContinuousMap.const ℝ (R (X ω) 0)
  have hzero : ∀ ω, ρ₀ ω 0 = 0 := by
    intro ω
    simp [ρ₀]
  have heq : ∀ᵐ ω ∂P, ρ₀ ω = R (X ω) := by
    filter_upwards [hR 0] with ω hω
    have h0 : R (X ω) 0 = 0 := by simpa using hω
    ext t
    simp [ρ₀, h0]
  refine ⟨hG, ?_⟩
  filter_upwards [ae_circleAvg_replField_one hX hzero, heq] with ω h1 h2
  simpa only [replField, h2] using h1

/-- The field reconstructed from the lateral part and an independent inner
Brownian splice has the law of any normalized whole-plane GFF. -/
theorem IsWholePlaneGFF.map_replField_twoSided_eq_normalized
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → DistC} {Y : Ω' → DistC}
    (hX : IsWholePlaneGFF X P) (hY : IsNormalizedWPGFF Y P')
    {R : DistC → C(ℝ, ℝ)} (hRm : Measurable R)
    (hR : ∀ t, (fun ω => R (X ω) t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {W : Ω → C(ℝ≥0, ℝ)} (hWm : Measurable W)
    (hW : IsPreBrownianReal (fun t ω => W ω t) P) (hXW : IndepFun X W P) :
    P.map (replField X (fun ω => twoSided (W ω)
      ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩)) =
      P'.map Y := by
  let V : Ω → C(ℝ≥0, ℝ) := fun ω =>
    ⟨fun t => R (X ω) (-(t : ℝ)), (R (X ω)).continuous.comp (by fun_prop)⟩
  have hVm : Measurable V := ContinuousMap.measurable_iff_eval.2 fun t =>
    (ContinuousMap.measurable_eval (-(t : ℝ))).comp (hRm.comp hX.measurable)
  have hSm : Measurable (fun ω => twoSided (W ω) (V ω)) :=
    measurable_twoSided.comp (hWm.prodMk hVm)
  have hLm : Measurable (fun ω => lateralPartC (X ω)) :=
    MatedCRTHarmonic.ConeScaling.measurable_lateralPart.comp hX.measurable
  have hRm' : Measurable (fun ω => R (X ω)) := hRm.comp hX.measurable
  let F : DistC × C(ℝ, ℝ) → DistC := fun p => p.1 + ofFunC (radialW p.2)
  have hF : Measurable F := MatedCRTHarmonic.ConeScaling.measurable_fieldOf
  have hlaw := IsWholePlaneGFF.map_lateralPart_twoSided_eq_radialVersion hX hRm hR hWm hW hXW
  have hmap : P.map (replField X (fun ω => twoSided (W ω) (V ω))) =
      P.map (replField X (fun ω => R (X ω))) := by
    change P.map (F ∘ fun ω => (lateralPartC (X ω), twoSided (W ω) (V ω))) =
      P.map (F ∘ fun ω => (lateralPartC (X ω), R (X ω)))
    rw [← Measure.map_map hF (hLm.prodMk hSm),
      ← Measure.map_map hF (hLm.prodMk hRm'), hlaw]
  exact hmap.trans (LQGMetric.CircleAvg.map_eq_of_isNormalizedWPGFF
    (IsWholePlaneGFF.normalized_replField_radialVersion hX hRm hR) hY)

end LatticeProb.LQG
