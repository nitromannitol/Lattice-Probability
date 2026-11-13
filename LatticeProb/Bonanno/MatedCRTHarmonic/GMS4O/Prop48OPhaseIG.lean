/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OPhaseIG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.ORotLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OPhaseRot

/-!
# The imaginary-geometry data under a rotation shifted in phase

For the frozen coupling, the curve `ηL = Φ(H)` is driven by the full IG input
`H = circleAvg hIG₀ + U`, with `U` uniform on `[0, 2πχ)` and independent of `hIG₀`
(`Frozen/IsMatingOfTreesCoupling.lean`, `igMap`, `igField`). Rotating the IG field by `θ` and
shifting the phase by `-χθ` (reduced modulo `2πχ`) is a symmetry of the law of `(hIG₀, U)`, and it
rotates the curve: `Φ(H_θ) = e^{-iθ} ηL` a.s. (`p48o_ig_rotation_package`).

This is the IG half of the phase-independence lemma used for [18] Lemma 4.9 and the far-pair step of
Proposition 4.8. The proof reuses
IGCO's rotation rule and integer-period invariance (`IGLaw/ORotLaw.lean`), CAROT's simultaneous
circle-average covariance (`IGLaw/CircleAvgCovariance.lean`) and the v4 clause that `Φ` ignores
non-positive radii.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace MatedCRTHarmonic.GMS4O

open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field}
  {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The IG period `2πχ` is positive for the frozen coupling. -/
theorem p48o_period_pos
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    0 < 2 * Real.pi * igChi γ :=
  have := D.isProbabilityMeasure
  period_pos_of_uniform D.igField.2.1

/-- `p48oRotCurve` is IGCO's `rotCurve`. -/
theorem p48oRotCurve_eq_rotCurve (θ : ℝ) (c : C(ℝ, ℂ)) : p48oRotCurve θ c = rotCurve θ c := by
  ext t
  rw [p48oRotCurve_apply]
  rfl

/-- The rotated normalized IG field is again a normalized whole-plane GFF. -/
theorem p48o_isNormalizedWPGFF_rotateField {h : Ω → Field} (hh : IsNormalizedWPGFF h P)
    (θ : ℝ) : IsNormalizedWPGFF (fun ω => MoTPort.rotateField θ (h ω)) P := by
  refine ⟨IsWholePlaneGFF.rotateField hh.1 θ, ?_⟩
  filter_upwards [rotCircleAvgCovariance_holds P h hh.1 θ 1 one_pos 0, hh.2] with ω h1 h2
  rw [h1, mul_zero, h2]

/-- **The law of `(hIG₀, U)` is invariant under rotation with phase shift `-χθ` (mod `2πχ`).** -/
theorem p48o_map_rotate_phase_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] (θ : ℝ) :
    P.map (fun ω => (MoTPort.rotateField θ (hIG₀ ω),
        modRep (2 * Real.pi * igChi γ) (-(igChi γ * θ) + U ω))) =
      P.map (fun ω => (hIG₀ ω, U ω)) := by
  have := D.isProbabilityMeasure
  set r : ℝ := 2 * Real.pi * igChi γ
  have hh : IsNormalizedWPGFF hIG₀ P := D.igField.1
  have hUlaw : P.map U = volume[|Ico (0 : ℝ) r] := D.igField.2.1
  have hind : IndepFun hIG₀ U P := D.igField.2.2
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (period_pos_of_uniform hUlaw) hUlaw
  set hθ : Ω → Field := fun ω => MoTPort.rotateField θ (hIG₀ ω) with hθdef
  have hθnorm : IsNormalizedWPGFF hθ P := p48o_isNormalizedWPGFF_rotateField hh θ
  have hlawθ : P.map hθ = P.map hIG₀ := CircleAvg.map_eq_of_isNormalizedWPGFF hθnorm hh
  have hindθ : IndepFun hθ U P := hind.comp (MoTPort.measurable_rotateField θ) measurable_id
  have hpair : P.map (fun ω => (hθ ω, U ω)) = P.map (fun ω => (hIG₀ ω, U ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hθnorm.1.measurable.aemeasurable hUm).1 hindθ,
      (indepFun_iff_map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hUm).1 hind, hlawθ]
  have hshift : P.map (fun ω => (hθ ω, modRep r ((fun _ : Field => -(igChi γ * θ)) (hθ ω) + U ω))) =
      P.map (fun ω => (hθ ω, U ω)) :=
    map_pair_shift_mod hθnorm.1.measurable hUlaw hindθ measurable_const
  exact hshift.trans hpair

/-- **The IG rotation package.** One measurable IG map `Φ` with `ηL = Φ(H)` a.s. and, for every
angle `θ`, `Φ(H_θ) = e^{-iθ} ηL` a.s., where `H_θ` is the input of the rotated field
`hIG₀(e^{iθ}·)` with the reduced phase `modRep (2πχ) (U − χθ)`. -/
theorem p48o_ig_rotation_package
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    [Fact (0 < 2 * Real.pi * igChi γ)] :
    ∃ Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ), Measurable Φ ∧
      (∀ᵐ ω ∂P, ηL ω = Φ (igCircleAvgInput (hIG₀ ω, U ω))) ∧
      ∀ θ : ℝ, ∀ᵐ ω ∂P,
        Φ (igCircleAvgInput (MoTPort.rotateField θ (hIG₀ ω),
          modRep (2 * Real.pi * igChi γ) (-(igChi γ * θ) + U ω))) = rotCurve (-θ) (ηL ω) := by
  have := D.isProbabilityMeasure
  set r : ℝ := 2 * Real.pi * igChi γ with hrdef
  obtain ⟨Φ, hΦ, hpos, hroot, hcc, -⟩ := D.igMap
  have hroot' : ∀ᵐ ω ∂P, ηL ω = Φ (igCircleAvgInput (hIG₀ ω, U ω)) := hroot
  have hcc' : ∀ (z₀ : ℂ) (s φ : ℝ), 0 < s → ∀ᵐ ω ∂P,
      Φ (igPullback γ z₀ s φ (igCircleAvgInput (hIG₀ ω, U ω))) = affineReroot z₀ s φ (ηL ω) :=
    hcc
  have hτ := IsMatingOfTreesCoupling.ae_rootTime_zero D
  refine ⟨Φ, hΦ, hroot', fun θ => ?_⟩
  have hh : IsNormalizedWPGFF hIG₀ P := D.igField.1
  have hUlaw : P.map U = volume[|Ico (0 : ℝ) r] := D.igField.2.1
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif (period_pos_of_uniform hUlaw) hUlaw
  -- the rotation rule at the actual input, rewritten through the rotated field
  have hrule := ae_rotation_rule_of_cc hcc' hτ θ
  have hcov := rotCircleAvgCovarianceAll_holds P hIG₀ hh.1 θ
  have hstep1 : ∀ᵐ ω ∂P, Φ (igCircleAvgInput (MoTPort.rotateField θ (hIG₀ ω),
      -(igChi γ * θ) + U ω)) = rotCurve (-θ) (ηL ω) := by
    filter_upwards [hrule, hcov] with ω hr hc
    rw [← hr]
    apply hpos
    intro ρ hρ
    funext w
    simp only [igCircleAvgInput, addIn, rotIn]
    rw [hc ρ hρ w]
    ring
  -- integer-period invariance at the transformed input
  have hper := ae_periodic_of_cc hroot' hcc' hτ
  have hlaw := p48o_map_rotate_phase_eq D θ
  have hp : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P := hh.1.measurable.aemeasurable.prodMk hUm
  have hU'm : AEMeasurable (fun ω => modRep r (-(igChi γ * θ) + U ω)) P :=
    (measurable_modRep r).comp_aemeasurable (aemeasurable_const.add hUm)
  have hp' : AEMeasurable (fun ω => (MoTPort.rotateField θ (hIG₀ ω),
      modRep r (-(igChi γ * θ) + U ω))) P :=
    ((MoTPort.measurable_rotateField θ).comp hh.1.measurable).aemeasurable.prodMk hU'm
  have hper' : ∀ᵐ ω ∂P, (MoTPort.rotateField θ (hIG₀ ω), modRep r (-(igChi γ * θ) + U ω)) ∈
      {x : Field × ℝ | ∀ k : ℤ,
        Φ (addIn (r * k) (igCircleAvgInput x)) = Φ (igCircleAvgInput x)} :=
    ae_of_map_eq hp hp' hlaw.symm (measurableSet_periodic hΦ r) hper
  filter_upwards [hstep1, hper'] with ω h1 h2
  obtain ⟨k, hk⟩ := exists_int_eq_modRep_add r (-(igChi γ * θ) + U ω)
  have e : igCircleAvgInput (MoTPort.rotateField θ (hIG₀ ω), -(igChi γ * θ) + U ω) =
      addIn (r * k) (igCircleAvgInput (MoTPort.rotateField θ (hIG₀ ω),
        modRep r (-(igChi γ * θ) + U ω))) := by
    rw [← igCircleAvgInput_add]
    congr 2
  rw [← h2 k, ← e]
  exact h1

end MatedCRTHarmonic.GMS4O
