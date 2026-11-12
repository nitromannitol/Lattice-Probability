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

end ConeMeas2

end MatedCRTHarmonic.MoTPort
