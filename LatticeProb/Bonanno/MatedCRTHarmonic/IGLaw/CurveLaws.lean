/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.CurveLaws at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.Rotation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Reusable curve-law consequences for the IGC bundle

This module records the measurable-factor and coordinate-change steps that consume the IGC
bundle. The normalization decomposition is stated at LQGMetric's circle-average convention and
the MoTPort `φ₀` convention.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Distributions

namespace MatedCRTHarmonic.IGLaw

open LQGMetric
open MatedCRTHarmonic.MoTPort

/-- The draft bundle's circle-average process `circleAvg h + U`, as a function of its field and
uniform scalar. -/
def igCircleAvgInput (p : Field × ℝ) : ℝ → ℂ → ℝ :=
  fun ρ w => circleAvg p.1 ρ w + p.2

theorem measurable_igCircleAvgInput : Measurable igCircleAvgInput := by
  apply measurable_pi_iff.2
  intro ρ
  apply measurable_pi_iff.2
  intro w
  have harg : Measurable fun p : Field × ℝ => (p.1, (ρ, w)) := by
    exact measurable_fst.prodMk (measurable_const.prodMk measurable_const)
  exact (LQGMetric.measurable_circleAvg.comp harg).add measurable_snd

/-- Uniform measure on one period pushes forward to normalized Haar measure on the additive
circle. -/
theorem map_uniform_period_to_addCircle {Ω : Type*} [MeasurableSpace Ω]
    {r : ℝ} [Fact (0 < r)] {P : Measure Ω} {U : Ω → ℝ}
    (hU : P.map U = volume[|Ico (0 : ℝ) r]) :
    P.map (fun ω => (U ω : AddCircle r)) = AddCircle.haarAddCircle := by
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hU
  change P.map ((fun x : ℝ => (x : AddCircle r)) ∘ U) = _
  rw [← AEMeasurable.map_map_of_aemeasurable AddCircle.measurable_mk'.aemeasurable hUm, hU]
  ext s hs
  rw [Measure.map_apply AddCircle.measurable_mk' hs,
    ProbabilityTheory.cond_apply measurableSet_Ico]
  have hset : Ico (0 : ℝ) r ∩ (fun x : ℝ => (x : AddCircle r)) ⁻¹' s =ᵐ[volume]
      Ioc (0 : ℝ) r ∩ (fun x : ℝ => (x : AddCircle r)) ⁻¹' s := by
    filter_upwards [Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := r) (μ := (volume : Measure ℝ))]
      with x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage, hx]
  rw [measure_congr hset, inter_comm]
  have hproj := AddCircle.add_projection_respects_measure r 0 hs
  rw [zero_add] at hproj
  rw [← hproj, AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply]
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr Fact.out)
  rw [Real.volume_Ico]
  simp only [sub_zero, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hr0 ENNReal.ofReal_ne_top, one_mul]

/-- Choose the representative of an additive-circle point in `[0,r)`. -/
def addCircleRepresentative {r : ℝ} [Fact (0 < r)] (x : AddCircle r) : ℝ :=
  (AddCircle.equivIco r 0 x).1

theorem measurable_addCircleRepresentative {r : ℝ} [Fact (0 < r)] :
    Measurable (addCircleRepresentative (r := r)) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco r 0).measurable

/-- Haar measure on the period circle, represented in `[0,r)`, is the usual uniform measure. -/
theorem map_addCircleRepresentative_haar {r : ℝ} [Fact (0 < r)] :
    AddCircle.haarAddCircle.map (addCircleRepresentative (r := r)) =
      volume[|Ico (0 : ℝ) r] := by
  let μ : Measure ℝ := volume[|Ico (0 : ℝ) r]
  let q : ℝ → AddCircle r := fun x => x
  have hq : μ.map q = AddCircle.haarAddCircle := by
    exact map_uniform_period_to_addCircle (r := r) (P := μ) (U := id) (by simp [μ])
  have hmem : ∀ᵐ x ∂μ, x ∈ Ico (0 : ℝ) r := by
    have hc : μ (Ico (0 : ℝ) r)ᶜ = 0 := by
      rw [show μ = volume[|Ico (0 : ℝ) r] from rfl,
        ProbabilityTheory.cond_apply measurableSet_Ico]
      rw [inter_compl_self, measure_empty, mul_zero]
    have hnot : ∀ᵐ x ∂μ, x ∉ (Ico (0 : ℝ) r)ᶜ :=
      measure_eq_zero_iff_ae_notMem.1 hc
    exact hnot.mono fun x hx => by simpa using hx
  have heq : (addCircleRepresentative (r := r) ∘ q) =ᵐ[μ] id := by
    filter_upwards [hmem] with x hx
    change (AddCircle.equivIco r 0 (x : AddCircle r)).1 = x
    have hx' : x ∈ Ico (0 : ℝ) (0 + r) := by simpa using hx
    rw [AddCircle.equivIco_coe_eq hx']
  calc
    AddCircle.haarAddCircle.map (addCircleRepresentative (r := r)) =
        (μ.map q).map (addCircleRepresentative (r := r)) := by rw [hq]
    _ = μ.map (addCircleRepresentative (r := r) ∘ q) :=
      Measure.map_map (measurable_addCircleRepresentative (r := r)) AddCircle.measurable_mk'
    _ = μ.map id := Measure.map_congr heq
    _ = μ := by simp

/-- Adding a field-measurable shift on the period circle to an independent Haar variable keeps
the result Haar and independent of the field variable. -/
theorem indepFun_addCircleShift {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {r : ℝ} [Fact (0 < r)] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → α} {U : Ω → AddCircle r} {V : α → AddCircle r}
    (hF : Measurable F) (hU : AEMeasurable U P) (hV : Measurable V)
    (hFU : IndepFun F U P) (hUlaw : P.map U = AddCircle.haarAddCircle) :
    IndepFun F (fun ω => V (F ω) + U ω) P ∧
      P.map (fun ω => V (F ω) + U ω) = AddCircle.haarAddCircle := by
  let μ := P.map F
  let sh : α × AddCircle r → α × AddCircle r := fun p => (p.1, V p.1 + p.2)
  let pr : Ω → α × AddCircle r := fun ω => (F ω, U ω)
  let ps : Ω → α × AddCircle r := fun ω => (F ω, V (F ω) + U ω)
  have hpr : AEMeasurable pr P := hF.aemeasurable.prodMk hU
  have hshift : AEMeasurable (fun ω => V (F ω) + U ω) P :=
    (hV.comp hF).aemeasurable.add hU
  have hps : AEMeasurable ps P := hF.aemeasurable.prodMk hshift
  have hsh : Measurable sh := measurable_fst.prodMk ((hV.comp measurable_fst).add measurable_snd)
  have hlaw : P.map pr = μ.prod AddCircle.haarAddCircle := by
    rw [← hUlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hU).mp hFU
  have hmp : MeasurePreserving sh (μ.prod AddCircle.haarAddCircle)
      (μ.prod AddCircle.haarAddCircle) := by
    refine MeasurePreserving.skew_product (μa := μ) (μb := μ)
      (μc := AddCircle.haarAddCircle) (μd := AddCircle.haarAddCircle)
      (f := id) (g := fun a u => V a + u) (MeasurePreserving.id μ) ?_ ?_
    · exact (hV.comp measurable_fst).add measurable_snd
    · exact ae_of_all _ fun a =>
        (MeasureTheory.measurePreserving_add_left AddCircle.haarAddCircle (V a)).map_eq
  have hpsLaw : P.map ps = μ.prod AddCircle.haarAddCircle := by
    calc
      P.map ps = P.map (sh ∘ pr) := by rfl
      _ = (P.map pr).map sh :=
        (AEMeasurable.map_map_of_aemeasurable hsh.aemeasurable hpr).symm
      _ = (μ.prod AddCircle.haarAddCircle).map sh := by rw [hlaw]
      _ = μ.prod AddCircle.haarAddCircle := hmp.map_eq
  have hUshift : P.map (fun ω => V (F ω) + U ω) = AddCircle.haarAddCircle := by
    calc
      P.map (fun ω => V (F ω) + U ω) = P.map (Prod.snd ∘ ps) := by rfl
      _ = (P.map ps).map Prod.snd :=
        (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hps).symm
      _ = (μ.prod AddCircle.haarAddCircle).map Prod.snd := by rw [hpsLaw]
      _ = (μ univ) • AddCircle.haarAddCircle := Measure.map_snd_prod
      _ = AddCircle.haarAddCircle := by rw [measure_univ, one_smul]
  have hind : IndepFun F (fun ω => V (F ω) + U ω) P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable
      hshift).2
    change P.map ps = (P.map F).prod (P.map (fun ω => V (F ω) + U ω))
    rw [hpsLaw, hUshift]
  exact ⟨hind, hUshift⟩

/-- Measurable functions of the IG field and its auxiliary scalar remain independent of the cone
data. This is the abstract `igMap` step for `indep_curve`. -/
theorem indepFun_of_ae_factor {Ω α β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω}
    {F : Ω → α} {G : Ω → β} {Y : Ω → γ} {f : α → γ}
    (hFG : IndepFun F G P) (hf : Measurable f)
    (hY : Y =ᵐ[P] fun ω => f (F ω)) : IndepFun Y G P := by
  have hcomp : IndepFun (fun ω => f (F ω)) G P := hFG.comp hf measurable_id
  exact hcomp.congr hY.symm (ae_of_all _ fun _ => rfl)

/-- The draft bundle's `igMap` factorization and `indep_curve` imply that `ηL` is independent of
the complete tuple of both cones. -/
theorem indepFun_igCurve_of_draft_factor {Ω β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] {P : Measure Ω} {h : Ω → Field} {U : Ω → ℝ}
    {C : Ω → β} {η : Ω → C(ℝ, ℂ)}
    {Φ : (ℝ → ℂ → ℝ) → C(ℝ, ℂ)} (hpair : IndepFun (fun ω => (h ω, U ω)) C P)
    (hΦ : Measurable Φ)
    (hη : η =ᵐ[P] fun ω => Φ (igCircleAvgInput (h ω, U ω))) : IndepFun η C P :=
  indepFun_of_ae_factor hpair (hΦ.comp measurable_igCircleAvgInput) hη

/-- A coordinate-change identity transports the law of the input field to the law of the
re-rooted curve, provided the transformed input has the original law. -/
theorem map_eq_of_coordinate_change {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω}
    {H : Ω → α} {η : Ω → β} {Φ : α → β} {T : α → α} {R : β → β}
    (hΦ : Measurable Φ) (hT : Measurable T) (hH : Measurable H)
    (hηΦ : η =ᵐ[P] fun ω => Φ (H ω))
    (hcoord : (fun ω => Φ (T (H ω))) =ᵐ[P] fun ω => R (η ω))
    (hinput : P.map (fun ω => T (H ω)) = P.map H) :
    P.map (fun ω => R (η ω)) = P.map η := by
  have hTcomp : Measurable (fun ω => T (H ω)) := hT.comp hH
  calc
    P.map (fun ω => R (η ω)) = P.map (fun ω => Φ (T (H ω))) := Measure.map_congr hcoord.symm
    _ = (P.map (fun ω => T (H ω))).map Φ := by
      exact (Measure.map_map hΦ hTcomp).symm
    _ = (P.map H).map Φ := by rw [hinput]
    _ = P.map (fun ω => Φ (H ω)) := Measure.map_map hΦ hH
    _ = P.map η := Measure.map_congr hηΦ.symm

end MatedCRTHarmonic.IGLaw
