/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeMeas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Cone
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample

/-!
# C.meas (part 1): a.e.-measurability of `qAreaC` and `scaleC` given the vague limit

For the measurability predicate `ConeRefMeas` from `Cone.lean`, consider an
a.e.-measurable random field `Y : Ω → Field` whose whole-plane area approximations a.s. converge
vaguely (the conclusion of node C.area-exist), the area of every open bounded set
(`aemeasurable_qAreaC_open`) and the plane-like scale `scaleC γ (Y ·)` (`aemeasurable_scaleC`) are
a.e.-measurable.

Proof: a.e. version of QuantumZipper's `LQGMeas.measurable_qAreaMeasure_open` /
`measurable_scaleParam_good` (QZ/Proofs/LQG/Measurability.lean): `μ(U) = sup_n ∫ bump_n dμ`
(`LQGMeas.measure_open_eq_iSup`), each `∫ bump_n dqAreaC` is the a.s. limit of
`∫ bump_n dareaApproxC_k`, measurable in the field (`ConeArea.measurable_areaApproxC`, mathlib
`Measure.measurable_lintegral`), and `scaleC` is an infimum over rationals
(`LQGMeas.measurable_sInf_upClosed`). Same scheme as `WedgeMeasC.aemeasurable_scaleParam`
(WedgeMeas.lean). Own bookkeeping only.

Still missing for C.meas: C.area-exist itself, measurability of the cone field
`ω ↦ coneField (lateralPartC (X ω)) (A · ω) Q`, and joint measurability of
`(s, h) ↦ affineComp s 0 h` and `(θ, h) ↦ rotateField θ h` (Carathéodory, LQGMetric
`continuous_testFamK` template).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric

namespace ConeMeas

variable {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `h ↦ ∫ f d(areaApproxC γ h k)` is measurable for continuous `f ≥ 0` -/
theorem measurable_integral_areaApproxC (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) : Measurable fun h : Field => ∫ z, f z ∂areaApproxC γ h k := by
  have e : (fun h : Field => ∫ z, f z ∂areaApproxC γ h k) =
      fun h => (∫⁻ z, ENNReal.ofReal (f z) ∂areaApproxC γ h k).toReal := by
    funext h
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf.aestronglyMeasurable
  rw [e]
  exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.measurable)).comp
    (ConeArea.measurable_areaApproxC γ k)).ennreal_toReal

/-- **the `qAreaC`-area of an open bounded set is a.e.-measurable**, given an a.e.-measurable
field with a.s. a vague area limit -/
theorem aemeasurable_qAreaC_open {Y : Ω → Field} (hY : AEMeasurable Y P)
    (hv : ∀ᵐ ω ∂P, ∃ μ, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Y ω)) μ)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    AEMeasurable (fun ω => qAreaC γ (Y ω) U) P := by
  have hUc : Uᶜ.Nonempty := by
    obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
    refine ⟨((|R| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have := hR h
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  have hv' : ∀ᵐ ω ∂P, QuantumZipper.IsVagueLimitOn univ (areaApproxC γ (Y ω)) (qAreaC γ (Y ω)) :=
    hv.mono fun ω h => ConeArea.isVagueLimitOn_qAreaC h
  have hn : ∀ n : ℕ, AEMeasurable
      (fun ω => ∫ z, LQGMeas.openBump U n z ∂qAreaC γ (Y ω)) P := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun k ω => ∫ z, LQGMeas.openBump U n z ∂areaApproxC γ (Y ω) k) (fun k => ?_) ?_
    · exact (measurable_integral_areaApproxC γ k (LQGMeas.continuous_openBump U n)
        (LQGMeas.openBump_nonneg U n)).comp_aemeasurable hY
    · filter_upwards [hv'] with ω h
      exact h.2.2 _ (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
        (subset_univ _)
  have key : ∀ ω, qAreaC γ (Y ω) U =
      ⨆ n : ℕ, ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂qAreaC γ (Y ω)) := by
    intro ω
    rw [LQGMeas.measure_open_eq_iSup _ hU hUc]
    congr 1
    funext n
    rw [ofReal_integral_eq_lintegral_ofReal (GoodSample.integrable_of_tsupport
      (U := univ) (fun K hK _ => ConeArea.qAreaC_compact_lt_top γ (Y ω) hK)
      (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
      (subset_univ _)) (ae_of_all _ fun z => LQGMeas.openBump_nonneg U n z)]
  simp_rw [key]
  exact AEMeasurable.iSup fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hn n)

end ConeMeas

end MatedCRTHarmonic.MoTPort
