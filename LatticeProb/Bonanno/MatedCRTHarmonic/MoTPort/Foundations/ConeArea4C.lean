/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4C at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4B
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea3B
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule

/-!
`ae_areaGood_U₀`: for **every** whole-plane GFF `X` (LM `IsWholePlaneGFF`, defined modulo an
additive constant) and `0 < γ < 2`, a.s. `areaApproxC γ X` has a vague limit on the window `U₀`
and is eventually finite on its compacts.

Proof (LM's law-transfer route, decision D85 of the LQG-metric project, as in
`GMCIdent3.ae_iff_wn`): normalize both `X` and the white-noise GFF `h₀` by `N g = ⟨g, ρ⟩`
(`∫ ρ = 1`); the normalized fields have the same law on `DistC` (LM
`GFFLaw.map_eq_of_normalized`); the measurable certificate `AreaCert U₀` (ConeArea4) holds a.s.
for the normalized `h₀` (`ae_areaGood_wn`, ConeArea4B), hence for the normalized `X`; finally
`AreaGood` is invariant under additive constants (`μ_{h+c} = e^{γc} μ_h`, ConeArea
`areaApproxC_addConst`). Own elementary glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric LQGMetric.GFFInv

/-- `AreaGood` is invariant under additive constants (`μ_{h+c} = e^{γc} μ_h`) -/
theorem areaGood_addConst {γ : ℝ} {x : Field} (hx : ConeArea.HasCircleAvgs x) {U : Set ℂ}
    (h : AreaGood U (areaApproxC γ x)) (c : ℝ) : AreaGood U (areaApproxC γ (addConst x c)) := by
  have e : areaApproxC γ (addConst x c) =
      fun k => ENNReal.ofReal (Real.exp (γ * c)) • areaApproxC γ x k :=
    funext (ConeArea.areaApproxC_addConst hx c)
  rw [e]
  obtain ⟨⟨μ, hμ⟩, hfin⟩ := h
  refine ⟨⟨_, LocalRule.IsVagueLimitOn.const_smul hμ ENNReal.ofReal_ne_top⟩, fun K hK hKU => ?_⟩
  filter_upwards [hfin K hK hKU] with k hk
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk

/-- the normalization `N g = ⟨g, ρ⟩` with `ρ` the standard mollifier (`∫ ρ = 1`) -/
def normC (g : Field) : ℝ := g (bumpTest 0 0)

lemma measurable_normC : Measurable normC := measurable_pair _

lemma normC_addConst (g : Field) (c : ℝ) : normC (addConst g c) = normC g + c := by
  simp only [normC, addConst_apply, GFFLaw.integral_bumpTest, one_mul]

/-- the normalized field `g − ⟨g, ρ⟩` -/
def normField (g : Field) : Field := addConst g (-normC g)

lemma normC_normField (g : Field) : normC (normField g) = 0 := by
  simp only [normField, normC_addConst, add_neg_cancel]

lemma addConst_normField (g : Field) : addConst (normField g) (normC g) = g := by
  simp only [normField, GFFLaw.addConst_addConst, neg_add_cancel, GFFLaw.addConst_zero']

lemma isWholePlaneGFF_normField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Field} (hX : IsWholePlaneGFF X P) :
    IsWholePlaneGFF (fun ω => normField (X ω)) P :=
  hX.addConst (measurable_normC.comp hX.measurable).neg

/-- the white-noise GFF gives the certificate a.s. after normalization -/
theorem map_normField_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Field} (hX : IsWholePlaneGFF X P) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {X' : Ω' → Field} (hX' : IsWholePlaneGFF X' P') :
    P.map (fun ω => normField (X ω)) = P'.map (fun ω => normField (X' ω)) :=
  GFFLaw.map_eq_of_normalized (GFFLaw.integral_bumpTest 0 0) measurable_normC normC_addConst
    (isWholePlaneGFF_normField hX) (isWholePlaneGFF_normField hX')
    (ae_of_all _ fun _ => normC_normField _) (ae_of_all _ fun _ => normC_normField _)

/-- **(R1) on the window `U₀`, for every whole-plane GFF** (DS Prop. 1.1) -/
theorem ae_areaGood_U₀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → Field} (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, AreaGood U₀ (areaApproxC γ (X ω)) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  have hS := measurableSet_areaCert γ U₀
  have hXn := isWholePlaneGFF_normField hX
  have hhn := isWholePlaneGFF_normField hh
  -- the certificate for the normalized white-noise field
  have h0 : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP,
      AreaCert U₀ (areaApproxC γ (normField (h₀ ω))) := by
    filter_upwards [ae_areaGood_wn hW hh hae hγ hγ2, ConeArea3.ae_hasCircleAvgs hh] with ω h1 h2
    exact cert_of_areaGood isBounded_U₀ (areaGood_addConst h2 h1 _)
  have h0' : ∀ᵐ x ∂(LQGDimension.ExistAsm.stdP.map fun ω => normField (h₀ ω)),
      AreaCert U₀ (areaApproxC γ x) :=
    (ae_map_iff hhn.measurable.aemeasurable hS).2 h0
  rw [← map_normField_eq hX hh] at h0'
  have h1 := (ae_map_iff hXn.measurable.aemeasurable hS).1 h0'
  filter_upwards [h1, ConeArea3.ae_hasCircleAvgs hXn] with ω hc hca
  have := areaGood_addConst hca (areaGood_of_cert isOpen_U₀ U₀_subset_H compl_U₀_nonempty hc)
    (normC (X ω))
  rwa [addConst_normField] at this

end ConeArea4
end MatedCRTHarmonic.MoTPort
