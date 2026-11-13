/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.Phase at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.CircleCover
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.GFFWP
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OBase

/-!
# the circle-average supremum bound for the full IG field `hIG₀ + U`

On the frozen bundle, on the frozen bundle the imaginary-geometry field driving `ηL` is `hIG₀ + U` (normalized
whole-plane GFF plus the independent uniform phase `U ∈ [0, 2πχ)`), so the IG circle averages in [18]'s
`F^ε(z)` / `E^ε` (condition 3, `[18]`) must be those of `hIG₀ + U`. The consumers of G4b's
`CircleAverageSupBound` (Prop 4.5: `GMS4b.prop45_holds`, the transfer's `l46t_zeroCone_prop45`, `l46t_wholePlane_prop45`) take
The bound as a hypothesis on the chosen process. This adapter supplies it for the phase-shifted process:

* `circleAverageSupBound_add_bounded` — adding an a.s. bounded random constant preserves `CircleAverageSupBound`
  (the constant is absorbed into the `δ′` margin for small radii and into the constant for the others);
* `exists_igCircleAvgVersion_withPhase` — the bundle's normalized IG field `hIG₀` has a jointly continuous
  circle-average version `H` (`LQGMetric.DFGPS.IsCircleAvgVersion hIG₀ P H`) such that both `H` and the full-IG process
  `H + U` satisfy `CircleAverageSupBound` (UMB's `circleAverageSupBoundModel_holds` + the phase bound `|U| ≤ 2πχ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **Adding an a.s. bounded random constant preserves the circle-average supremum bound.** -/
theorem circleAverageSupBound_add_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H : ℝ → ℂ → Ω → ℝ} {U : Ω → ℝ} {K : ℝ}
    (hU : ∀ᵐ ω ∂P, |U ω| ≤ K) (hH : GMS4b.CircleAverageSupBound P H) :
    GMS4b.CircleAverageSupBound P (fun r z ω => H r z ω + U ω) := by
  intro δ' hδ'
  obtain ⟨β, hβ, hρ⟩ := hH (δ' / 2) (by positivity)
  refine ⟨β, hβ, fun ρ hρ1 => ?_⟩
  obtain ⟨C, hC⟩ := hρ ρ hρ1
  -- the threshold radius below which the phase is absorbed into the margin
  set K' : ℝ := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set r₀ : ℝ := Real.exp (-(2 * K' / δ')) with hr₀
  have hr₀0 : 0 < r₀ := Real.exp_pos _
  have hr₀β : 0 < r₀ ^ β := Real.rpow_pos_of_pos hr₀0 β
  refine ⟨max C 0 + (r₀ ^ β)⁻¹, fun r hr => ?_⟩
  have hrβ0 : 0 ≤ r ^ β := Real.rpow_nonneg hr.1.le β
  have hnull : P {ω | ¬ |U ω| ≤ K} = 0 := ae_iff.mp hU
  by_cases hsmall : r ≤ r₀
  · -- small radii: `|H + U| > (2 + δ') log r⁻¹` forces `|H| > (2 + δ'/2) log r⁻¹` when `|U| ≤ K`
    have hlog : 2 * K' / δ' ≤ Real.log r⁻¹ := by
      have h1 : Real.log r ≤ -(2 * K' / δ') := by
        calc
          Real.log r ≤ Real.log r₀ := Real.log_le_log hr.1 hsmall
          _ = -(2 * K' / δ') := Real.log_exp _
      rw [Real.log_inv]
      linarith
    have hmargin : K' ≤ δ' / 2 * Real.log r⁻¹ := by
      have h2 : 2 * K' ≤ δ' * Real.log r⁻¹ := by
        have := mul_le_mul_of_nonneg_left hlog hδ'.le
        rwa [mul_div_cancel₀ _ hδ'.ne'] at this
      linarith
    have hsub : {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |H r z ω + U ω|} ⊆
        {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ' / 2) * Real.log r⁻¹ < |H r z ω|} ∪
          {ω | ¬ |U ω| ≤ K} := by
      intro ω ⟨z, hz, hbig⟩
      by_cases hUω : |U ω| ≤ K
      · left
        refine ⟨z, hz, ?_⟩
        have htri : |H r z ω + U ω| ≤ |H r z ω| + |U ω| := abs_add_le _ _
        have hUK : |U ω| ≤ K' := hUω.trans (le_max_left _ _)
        nlinarith
      · exact Or.inr hUω
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |H r z ω + U ω|} ≤
          P {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ' / 2) * Real.log r⁻¹ < |H r z ω|} +
            P {ω | ¬ |U ω| ≤ K} := (measure_mono hsub).trans (measure_union_le _ _)
      _ = P {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ' / 2) * Real.log r⁻¹ < |H r z ω|} := by
        rw [hnull, add_zero]
      _ ≤ ENNReal.ofReal (C * r ^ β) := hC r hr
      _ ≤ ENNReal.ofReal ((max C 0 + (r₀ ^ β)⁻¹) * r ^ β) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hrβ0
        have := inv_nonneg.mpr hr₀β.le
        linarith [le_max_left C 0]
  · -- large radii: the bound exceeds one
    rw [not_le] at hsmall
    have hone : (1 : ℝ) ≤ (max C 0 + (r₀ ^ β)⁻¹) * r ^ β := by
      have hpow : r₀ ^ β ≤ r ^ β := Real.rpow_le_rpow hr₀0.le hsmall.le hβ.le
      have h1 : 1 ≤ (r₀ ^ β)⁻¹ * r ^ β := by
        calc
          (1 : ℝ) = (r₀ ^ β)⁻¹ * r₀ ^ β := (inv_mul_cancel₀ hr₀β.ne').symm
          _ ≤ (r₀ ^ β)⁻¹ * r ^ β := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hr₀β.le)
      have h2 : 0 ≤ max C 0 * r ^ β := mul_nonneg (le_max_right _ _) hrβ0
      nlinarith
    calc
      P {ω | ∃ z ∈ ball (0 : ℂ) ρ, (2 + δ') * Real.log r⁻¹ < |H r z ω + U ω|} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hone

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The bundle's IG phase is a.s. in `[0, 2πχ)`; in particular `|U| ≤ 2πχ` a.s. -/
theorem ae_abs_phase_le
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, |U ω| ≤ 2 * Real.pi * MatedCRT.igChi γ := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  have hper := IGLaw.period_pos_of_uniform D.igField.2.1
  have hUm : AEMeasurable U P := MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif hper D.igField.2.1
  have hmap : ∀ᵐ x ∂(P.map U), x ∈ Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ) := by
    rw [D.igField.2.1, ae_iff]
    have hs : MeasurableSet (Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ)) := measurableSet_Ico
    have heq : {a : ℝ | ¬ a ∈ Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ)} =
        (Ico (0 : ℝ) (2 * Real.pi * MatedCRT.igChi γ))ᶜ := rfl
    rw [heq, cond_apply hs, inter_compl_self, measure_empty, mul_zero]
  filter_upwards [ae_of_ae_map hUm hmap] with ω hω
  rw [abs_of_nonneg hω.1]
  exact hω.2.le

/-- **The full IG field's circle averages satisfy the supremum bound.** The bundle's normalized IG field `hIG₀` has a
jointly continuous circle-average version `H` such that both `H` and `H + U` (the circle averages of the IG field
`hIG₀ + U` that drives `ηL`) satisfy `GMS4b.CircleAverageSupBound`. -/
theorem exists_igCircleAvgVersion_withPhase
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGMetric.DFGPS.IsCircleAvgVersion hIG₀ P H ∧
      GMS4b.CircleAverageSupBound P H ∧
      GMS4b.CircleAverageSupBound P (fun r z ω => H r z ω + U ω) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨H, hH, -⟩ := GMCUpper.exists_circleAvgVersion_normalized D.igField.1
  have hsup : GMS4b.CircleAverageSupBound P H :=
    GMCUpper.circleAverageSupBound_of_model D.igField.1 hH
      (GMCUpper.circleAverageSupBoundModel_holds D.igField.1 hH)
  exact ⟨H, hH, hsup, circleAverageSupBound_add_bounded (ae_abs_phase_le D) hsup⟩

end Bundle

end MatedCRTHarmonic.BundleSec4
