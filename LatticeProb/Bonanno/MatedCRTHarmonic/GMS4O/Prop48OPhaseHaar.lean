/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OPhaseHaar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OProcLaw

/-!
# Shift invariance of a uniform phase forces independence

If shifting a Haar-distributed circle variable `V` by every constant leaves the joint law of
`(X, V)` unchanged, then `X` and `V` are independent: for each Borel `A`, the finite measure
`B ↦ P(X ∈ A, V ∈ B)` on the circle is translation invariant, hence a multiple of Haar measure
(uniqueness of Haar measure, Mathlib's `isAddLeftInvariant_eq_smul`).

`p48o_indepFun_real_of_shift` is the form used for the frozen coupling's uniform IG phase
`U ∈ [0, 2πχ)`, with shifts reduced modulo the period by IGCO's `modRep`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.IGLaw

/-- **Haar uniqueness ⇒ independence.** -/
theorem p48o_indepFun_of_map_add_eq {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ} [Fact (0 < r)]
    {X : Ω → β} {V : Ω → AddCircle r} (hX : Measurable X) (hV : Measurable V)
    (hVlaw : P.map V = AddCircle.haarAddCircle)
    (hshift : ∀ c : AddCircle r,
      P.map (fun ω => (X ω, V ω + c)) = P.map (fun ω => (X ω, V ω))) :
    IndepFun X V P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  set ν : Measure (AddCircle r) := (P.restrict (X ⁻¹' A)).map V with hν
  have hνapp : ∀ C, MeasurableSet C → ν C = P (X ⁻¹' A ∩ V ⁻¹' C) := by
    intro C hC
    rw [hν, Measure.map_apply hV hC, Measure.restrict_apply (hV hC), inter_comm]
  have : IsFiniteMeasure ν := by
    rw [hν]; infer_instance
  have : IsAddLeftInvariant ν := by
    refine ⟨fun c => ?_⟩
    ext C hC
    rw [Measure.map_apply (measurable_const_add c) hC, hνapp _ (measurable_const_add c hC),
      hνapp C hC]
    have hpair : Measurable fun ω => (X ω, V ω) := hX.prodMk hV
    have hpairc : Measurable fun ω => (X ω, V ω + c) := hX.prodMk (hV.add_const c)
    have h1 := congrArg (fun μ : Measure (β × AddCircle r) => μ (A ×ˢ C)) (hshift c)
    rw [Measure.map_apply hpairc (hA.prod hC), Measure.map_apply hpair (hA.prod hC)] at h1
    have e1 : (fun ω => (X ω, V ω + c)) ⁻¹' (A ×ˢ C) =
        X ⁻¹' A ∩ V ⁻¹' ((fun x => c + x) ⁻¹' C) := by
      ext ω; simp [add_comm]
    have e2 : (fun ω => (X ω, V ω)) ⁻¹' (A ×ˢ C) = X ⁻¹' A ∩ V ⁻¹' C := by
      ext ω; simp
    rw [e1, e2] at h1
    exact h1
  have hsmul := isAddLeftInvariant_eq_smul ν (AddCircle.haarAddCircle (T := r))
  have huniv : ν univ = P (X ⁻¹' A) := by
    rw [hνapp univ MeasurableSet.univ, preimage_univ, inter_univ]
  have hscalar : (addHaarScalarFactor ν (AddCircle.haarAddCircle (T := r)) : ENNReal) =
      P (X ⁻¹' A) := by
    have h := congrArg (fun μ : Measure (AddCircle r) => μ univ) hsmul
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    rw [← huniv, h]
  have hB' : (AddCircle.haarAddCircle (T := r)) B = P (V ⁻¹' B) := by
    rw [← hVlaw, Measure.map_apply hV hB]
  rw [← hνapp B hB, hsmul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hB', hscalar]

/-- The representative in `[0, r)` maps back to the same circle point. -/
lemma p48o_coe_addCircleRepresentative {r : ℝ} [Fact (0 < r)] (y : AddCircle r) :
    ((addCircleRepresentative y : ℝ) : AddCircle r) = y :=
  (AddCircle.equivIco r 0).symm_apply_apply y

lemma p48o_coe_modRep {r : ℝ} [Fact (0 < r)] (x : ℝ) :
    ((modRep r x : ℝ) : AddCircle r) = (x : AddCircle r) :=
  p48o_coe_addCircleRepresentative _

lemma p48o_addCircleRepresentative_coe {r : ℝ} [Fact (0 < r)] {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) r) : addCircleRepresentative ((x : AddCircle r)) = x := by
  have hx' : x ∈ Ico (0 : ℝ) (0 + r) := by simpa using hx
  change (AddCircle.equivIco r 0 (x : AddCircle r)).1 = x
  rw [AddCircle.equivIco_coe_eq hx']

/-- **Independence from a uniform phase.** If `U` is uniform on `[0, r)` and, for every real
`c`, replacing `U` by its shift reduced modulo `r` does not change the joint law with `X`, then `X`
and `U` are independent. -/
theorem p48o_indepFun_real_of_shift {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ} [Fact (0 < r)]
    {X : Ω → β} {U : Ω → ℝ} (hX : Measurable X)
    (hU : P.map U = volume[|Ico (0 : ℝ) r])
    (hshift : ∀ c : ℝ,
      P.map (fun ω => (X ω, modRep r (c + U ω))) = P.map (fun ω => (X ω, U ω))) :
    IndepFun X U P := by
  have hUm : AEMeasurable U P :=
    MoTPort.WPGFFMod.aemeasurable_of_map_eq_unif Fact.out hU
  set Um : Ω → ℝ := hUm.mk U
  have hUmm : Measurable Um := hUm.measurable_mk
  have hUeq : U =ᵐ[P] Um := hUm.ae_eq_mk
  set V : Ω → AddCircle r := fun ω => (Um ω : AddCircle r)
  have hVm : Measurable V := AddCircle.measurable_mk'.comp hUmm
  have hVlaw : P.map V = AddCircle.haarAddCircle := by
    rw [← map_uniform_period_to_addCircle hU]
    refine Measure.map_congr ?_
    filter_upwards [hUeq] with ω hω
    simp only [V, hω]
  have hcoe : Measurable fun p : β × ℝ => (p.1, (p.2 : AddCircle r)) :=
    measurable_fst.prodMk (AddCircle.measurable_mk'.comp measurable_snd)
  have hshiftV : ∀ c : AddCircle r,
      P.map (fun ω => (X ω, V ω + c)) = P.map (fun ω => (X ω, V ω)) := by
    intro c
    set c' : ℝ := addCircleRepresentative c
    have hc' : ((c' : ℝ) : AddCircle r) = c := p48o_coe_addCircleRepresentative c
    have hA : (fun ω => (X ω, V ω + c)) =ᵐ[P]
        (fun p : β × ℝ => (p.1, (p.2 : AddCircle r))) ∘
          fun ω => (X ω, modRep r (c' + U ω)) := by
      filter_upwards [hUeq] with ω hω
      simp only [Function.comp_apply, V, p48o_coe_modRep, ← hω, ← hc', AddCircle.coe_add,
        add_comm]
    have hB : (fun ω => (X ω, V ω)) =ᵐ[P]
        (fun p : β × ℝ => (p.1, (p.2 : AddCircle r))) ∘ fun ω => (X ω, U ω) := by
      filter_upwards [hUeq] with ω hω
      simp only [Function.comp_apply, V, hω]
    have hp1 : AEMeasurable (fun ω => (X ω, modRep r (c' + U ω))) P :=
      hX.aemeasurable.prodMk ((measurable_modRep r).comp_aemeasurable
        (aemeasurable_const.add hUm))
    have hp2 : AEMeasurable (fun ω => (X ω, U ω)) P := hX.aemeasurable.prodMk hUm
    rw [Measure.map_congr hA, Measure.map_congr hB,
      ← AEMeasurable.map_map_of_aemeasurable hcoe.aemeasurable hp1,
      ← AEMeasurable.map_map_of_aemeasurable hcoe.aemeasurable hp2, hshift c']
  have hindV := p48o_indepFun_of_map_add_eq hX hVm hVlaw hshiftV
  have hmem : ∀ᵐ ω ∂P, U ω ∈ Ico (0 : ℝ) r := by
    have hc : P.map U (Ico (0 : ℝ) r)ᶜ = 0 := by
      rw [hU, ProbabilityTheory.cond_apply measurableSet_Ico, inter_compl_self, measure_empty,
        mul_zero]
    rw [Measure.map_apply_of_aemeasurable hUm measurableSet_Ico.compl] at hc
    have hnot : ∀ᵐ ω ∂P, ω ∉ U ⁻¹' (Ico (0 : ℝ) r)ᶜ := measure_eq_zero_iff_ae_notMem.1 hc
    filter_upwards [hnot] with ω hω
    simpa using hω
  have hrep : (fun ω => addCircleRepresentative (V ω)) =ᵐ[P] U := by
    filter_upwards [hUeq, hmem] with ω hω hmω
    simp only [V, ← hω]
    exact p48o_addCircleRepresentative_coe hmω
  exact (hindV.comp measurable_id (measurable_addCircleRepresentative (r := r))).congr
    (ae_eq_refl _) hrep

end MatedCRTHarmonic.GMS4O
