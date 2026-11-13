/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.RootingCylinderObservable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.RootingMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin

/-!
# Bounded cylinder observables under logarithmic rooting

This file packages the measurability, uniform bound, and product-integral identity for the
finite mean-zero pairing observables used in the final DMS14 A.10 field-law argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric

/-- Mean-zero pairings do not see the additive constant used to renormalize a rooted field. -/
theorem pair0_addConst_eq (g : DistC) (c : ℝ) :
    pair0 (addConst g c) = pair0 g := by
  funext ψ
  simp [pair0, GFFInv.addConst_apply, ψ.property]

/-- The jointly measurable finite-cylinder observable of a field and a rooting point. -/
def rootingCylinderIntegrand {Ω : Type*} (I : Finset TestC0)
    (F : (I → ℝ) → ℝ) (h : Ω → DistC) (γ : ℝ) (p : Ω × ℂ) : ℝ :=
  F (I.restrict (pair0 (h p.1 + logRootingShift γ p.2)))

/-- The finite-cylinder observable averaged over the unrooted field. -/
def rootingCylinderObservable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset TestC0) (F : (I → ℝ) → ℝ) (h : Ω → DistC) (γ : ℝ) (z : ℂ) : ℝ :=
  ∫ ω, rootingCylinderIntegrand I F h γ (ω, z) ∂P

/-- The field-root finite-cylinder integrand is jointly measurable. -/
theorem measurable_rootingCylinderIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (γ : ℝ) :
    Measurable (rootingCylinderIntegrand I F h γ) := by
  apply hF.measurable.comp
  apply (Finset.measurable_restrict I).comp
  apply measurable_pair0.comp
  exact (measurable_add_logRootingShift γ).comp
    ((hh.1.measurable.comp measurable_fst).prodMk measurable_snd)

/-- Averaging a bounded continuous finite-cylinder observable over the field leaves a strongly
measurable function of the root point. -/
theorem stronglyMeasurable_rootingCylinderObservable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) (γ : ℝ) :
    StronglyMeasurable (rootingCylinderObservable P I F h γ) := by
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  exact (measurable_rootingCylinderIntegrand hh I F hF γ).stronglyMeasurable.integral_prod_left'

/-- A uniform bound on the cylinder function is preserved by averaging over the probability law
of the unrooted field. -/
theorem norm_rootingCylinderObservable_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    {B : ℝ} (hFbound : ∀ x, ‖F x‖ ≤ B) (γ : ℝ) (z : ℂ) :
    ‖rootingCylinderObservable P I F h γ z‖ ≤ B := by
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (ae_of_all P fun ω => hFbound _)).trans_eq (by simp)

/-- A bounded continuous rooting cylinder is integrable against the product of the field law and
any finite root measure. -/
theorem integrable_rootingCylinderIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hh : IsNormalizedWPGFF h P) (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) {B : ℝ} (hFbound : ∀ x, ‖F x‖ ≤ B) (γ : ℝ) :
    Integrable (rootingCylinderIntegrand I F h γ) (P.prod ν) := by
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  exact Integrable.mono' (integrable_const B)
    (measurable_rootingCylinderIntegrand hh I F hF γ).aestronglyMeasurable
    (ae_of_all _ fun p => hFbound _)

/-- Fubini's identity for the averaged rooting cylinder and an arbitrary finite root measure. -/
theorem integral_rootingCylinderObservable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hh : IsNormalizedWPGFF h P) (I : Finset TestC0) (F : (I → ℝ) → ℝ)
    (hF : Continuous F) {B : ℝ} (hFbound : ∀ x, ‖F x‖ ≤ B) (γ : ℝ) :
    ∫ z, rootingCylinderObservable P I F h γ z ∂ν =
      ∫ p : Ω × ℂ, rootingCylinderIntegrand I F h γ p ∂(P.prod ν) := by
  letI : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  exact (integral_prod_symm _
    (integrable_rootingCylinderIntegrand hh I F hF hFbound γ)).symm

end MatedCRTHarmonic.ConeLemmaA10

