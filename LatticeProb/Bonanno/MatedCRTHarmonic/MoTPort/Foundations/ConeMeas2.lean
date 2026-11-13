/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.ZoomRadialFinal
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4

/-!
# C.meas, input (a): the cone field is a.e.-measurable

`ConeMeas.coneRefMeas_of` (ConeMeasJoint.lean, MEAS-1) reduces node C.meas (`ConeRefMeas γ W`,
Cone.lean) to (a) a.e.-measurability of `ω ↦ coneField (lateralPartC (X ω)) (A · ω) Q` and (b) the
a.s. existence of the whole-plane area measure of the cone field (C.area-exist for the cone).
This file proves (a) unconditionally and records the reduction of C.meas to (b) alone
(`coneRefMeas_of_area`).

* `measurable_ofFunC_apply`: for a jointly measurable `F : Ω × ℂ → ℝ`, every pairing
  `ω ↦ ⟨ofFunC (F ω ·), φ⟩` is measurable. `ofFunC f` is mathlib's `Distribution.ofFun`, equal to
  `φ ↦ ∫ φ f` when `f` is locally integrable and to `0` otherwise (`ofFun_apply_eq_ite`); the set of
  `ω` where `F ω` is locally integrable is measurable (`measurableSet_locallyIntegrable`: local
  integrability on `ℂ` is finiteness of the lintegrals over the balls `B(0,n)`). In particular no
  a.s. local integrability of the radial profile of the GFF is needed for measurability.
* `exists_joint_version`: a process with a.e.-measurable, a.s. continuous paths has a version
  which is jointly measurable and continuous for every `ω`, equal to it a.s. as a path (the trick of
  QZ `WedgeMeasurable.measurable_wedgePath_joint`: mathlib
  `measurable_uncurry_of_continuous_of_measurable`).
* `aemeasurable_coneField`: input (a), with QZ `ZoomRadial.aemeasurable_wedgePath` and
  `WedgeCan4.ae_continuous_wedgeProcess` applied to the wedge process `t ↦ A (2t)`
  (`Cone.isWedgeProcess_of_isConeProcess`), and LM `measurable_circleAvg` for the radial part
  `radialFun (X ω) z = (X ω)_{|z|}(0)` of `lateralPartC`.

Own elementary measure-theoretic glue (no paper step: DMS treat the cone as a random distribution,
DMS Def. 4.10; measurability is implicit there).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort

namespace ConeMeas2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- local integrability on `ℂ` is finiteness of the lintegrals over the balls `B(0,n)` -/
theorem locallyIntegrable_iff_ball {f : ℂ → ℝ} (hf : Measurable f) :
    LocallyIntegrable f volume ↔ ∀ n : ℕ, ∫⁻ z in closedBall (0 : ℂ) n, ‖f z‖ₑ < ⊤ := by
  rw [locallyIntegrable_iff]
  constructor
  · intro h n
    exact (h _ (isCompact_closedBall 0 n)).2
  · intro h K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨n, hn⟩ := exists_nat_ge R
    have hsub : K ⊆ closedBall (0 : ℂ) n := hR.trans (closedBall_subset_closedBall hn)
    exact (show IntegrableOn f (closedBall (0 : ℂ) n) volume from
      ⟨hf.aestronglyMeasurable, h n⟩).mono_set hsub

/-- the set where a jointly measurable family is locally integrable is measurable -/
theorem measurableSet_locallyIntegrable {F : Ω → ℂ → ℝ}
    (hF : Measurable fun p : Ω × ℂ => F p.1 p.2) :
    MeasurableSet {ω | LocallyIntegrable (F ω) volume} := by
  have hFω : ∀ ω, Measurable (F ω) := fun ω =>
    hF.comp (measurable_const.prodMk measurable_id)
  have e : {ω | LocallyIntegrable (F ω) volume} =
      ⋂ n : ℕ, {ω | ∫⁻ z in closedBall (0 : ℂ) n, ‖F ω z‖ₑ < ⊤} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact locallyIntegrable_iff_ball (hFω ω)
  rw [e]
  refine MeasurableSet.iInter fun n => measurableSet_lt ?_ measurable_const
  exact hF.enorm.lintegral_prod_right'

/-- pairings of `ofFunC` of a jointly measurable family are measurable -/
theorem measurable_ofFunC_apply {F : Ω → ℂ → ℝ} (hF : Measurable fun p : Ω × ℂ => F p.1 p.2)
    (φ : LQGMetric.TestC) : Measurable fun ω => ofFunC (F ω) φ := by
  classical
  have e : (fun ω => ofFunC (F ω) φ) = fun ω =>
      if LocallyIntegrable (F ω) volume then ∫ x, φ x • F ω x else 0 := by
    funext ω
    rw [ofFunC, Distribution.ofFun_apply_eq_ite, TopologicalSpace.Opens.coe_top,
      locallyIntegrableOn_univ]
  rw [e]
  refine Measurable.ite (measurableSet_locallyIntegrable hF) ?_ measurable_const
  have hj : Measurable fun p : Ω × ℂ => φ p.2 • F p.1 p.2 :=
    (φ.continuous.measurable.comp measurable_snd).smul hF
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

variable {P : Measure Ω}

/-- a process with a.e.-measurable, a.s. continuous paths has a jointly measurable version with
continuous paths, equal to it a.s. as a path -/
theorem exists_joint_version {A : ℝ → Ω → ℝ} (hm : AEMeasurable (fun ω t => A t ω) P)
    (hc : ∀ᵐ ω ∂P, Continuous fun t => A t ω) :
    ∃ A' : ℝ → Ω → ℝ, Measurable (fun q : Ω × ℝ => A' q.2 q.1) ∧
      ∀ᵐ ω ∂P, ∀ t, A' t ω = A t ω := by
  classical
  set g := hm.mk _ with hg
  have hgm : Measurable g := hm.measurable_mk
  have hgood : ∀ᵐ ω ∂P, Continuous (g ω) ∧ g ω = fun t => A t ω := by
    filter_upwards [hm.ae_eq_mk, hc] with ω h1 h2
    refine ⟨?_, h1.symm⟩
    rw [show g ω = fun t => A t ω from h1.symm]
    exact h2
  set S := toMeasurable P {ω | ¬(Continuous (g ω) ∧ g ω = fun t => A t ω)} with hS
  have hS0 : P S = 0 := by
    rw [hS, measure_toMeasurable]
    exact ae_iff.1 hgood
  let A' : ℝ → Ω → ℝ := fun t ω => if ω ∈ S then 0 else g ω t
  have hcont : ∀ ω, Continuous fun t => A' t ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [A', hω, ite_true]; exact continuous_const
    · have : ω ∉ {ω | ¬(Continuous (g ω) ∧ g ω = fun t => A t ω)} :=
        fun h => hω (subset_toMeasurable _ _ h)
      simp only [mem_ofPred_eq, not_not] at this
      simp only [A', hω, ite_false]; exact this.1
  have hmeas : ∀ t, Measurable (A' t) := fun t =>
    Measurable.ite (measurableSet_toMeasurable _ _) measurable_const
      ((measurable_pi_apply t).comp hgm)
  refine ⟨A', (measurable_uncurry_of_continuous_of_measurable hcont hmeas).comp
    (measurable_snd.prodMk measurable_fst), ?_⟩
  have hnS : ∀ᵐ ω ∂P, ω ∉ S := measure_eq_zero_iff_ae_notMem.1 hS0
  filter_upwards [hnS, hgood] with ω h1 h2 t
  simp only [A', h1, ite_false]
  exact congrFun h2.2 t

/-- the cone field of a measurable field and a jointly measurable radial process is measurable -/
theorem measurable_coneField {X : Ω → Field} (hX : Measurable X) {A : ℝ → Ω → ℝ}
    (hA : Measurable fun q : Ω × ℝ => A q.2 q.1) (Q : ℝ) :
    Measurable fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) Q := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  have hR : Measurable fun p : Ω × ℂ => radialFun (X p.1) p.2 := by
    have h1 : Measurable fun p : Ω × ℂ => ((X p.1, ‖p.2‖, (0 : ℂ)) : Field × ℝ × ℂ) := by
      refine Measurable.prodMk (hX.comp measurable_fst) ?_
      exact Measurable.prodMk (measurable_norm.comp measurable_snd) measurable_const
    have h2 := LQGMetric.measurable_circleAvg.comp h1
    unfold radialFun
    exact h2
  have hG : Measurable fun p : Ω × ℂ =>
      Q * (-Real.log ‖p.2‖) + A (-Real.log ‖p.2‖) p.1 :=
    ((Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg.const_mul Q).add
      (hA.comp (measurable_fst.prodMk
        (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg))
  have e : (fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) Q φ) = fun ω =>
      X ω φ - ofFunC (radialFun (X ω)) φ +
        ofFunC (fun z => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖) ω) φ := by
    funext ω
    simp only [coneField, lateralPartC, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
  rw [e]
  exact (((LQGMetric.measurable_distOn_apply φ).comp hX).sub
    (measurable_ofFunC_apply (F := fun ω => radialFun (X ω)) hR φ)).add
    (measurable_ofFunC_apply (F := fun ω z => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖) ω) hG φ)

/-- the radial process of a cone has a.e.-measurable, a.s. continuous paths -/
theorem aemeasurable_conePath [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hA : IsConeProcess α Q A P) :
    AEMeasurable (fun ω t => A t ω) P ∧ ∀ᵐ ω ∂P, Continuous fun t => A t ω := by
  have hW := Cone.isWedgeProcess_of_isConeProcess hA
  have hm := QuantumZipper.ZoomRadial.aemeasurable_wedgePath hW
  have hc := QuantumZipper.WedgeCan4.ae_continuous_wedgeProcess hW
  have e : ∀ ω t, A t ω = A (2 * (t / 2)) ω := fun ω t => by
    rw [mul_div_cancel₀ t two_ne_zero]
  constructor
  · have hφ : Measurable fun p : ℝ → ℝ => fun t : ℝ => p (t / 2) :=
      measurable_pi_iff.2 fun t => measurable_pi_apply (t / 2)
    have := hφ.comp_aemeasurable hm
    convert this using 1
    funext ω t
    exact e ω t
  · filter_upwards [hc] with ω h
    have := h.comp (continuous_id.div_const (2 : ℝ))
    convert this using 1
    funext t
    exact e ω t

/-- **C.meas input (a)**: the cone field `coneField (lateralPartC X) A Q` of a whole-plane GFF and
a cone process is a.e.-measurable (no independence needed) -/
theorem aemeasurable_coneField [IsProbabilityMeasure P] {X : Ω → Field}
    (hX : LQGMetric.IsWholePlaneGFF X P) {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P) :
    AEMeasurable (fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) Q) P := by
  obtain ⟨hm, hc⟩ := aemeasurable_conePath hA
  obtain ⟨A', hA'm, hA'⟩ := exists_joint_version hm hc
  refine (measurable_coneField hX.measurable hA'm Q).aemeasurable.congr ?_
  filter_upwards [hA'] with ω h
  have : (fun t => A' t ω) = fun t => A t ω := funext h
  simp only [this]

end ConeMeas2

end MatedCRTHarmonic.MoTPort
