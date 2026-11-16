import LatticeProb.LQG.CouplingRegularClosedSegments

/-! # Transfer of simultaneous disk-shaped curve segments -/

open MeasureTheory Set Metric
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace MatedCRTHarmonic.MoTInput

/-- An almost sure simultaneous disk event transfers to the Lebesgue-parametrized
curve of a coupling under equality of curve laws, provided that event is
null-measurable for the common law. -/
theorem ae_disk_segments_of_equal_curve_law
    {γ : ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2} {ξ : Ω' → C(ℝ, ℂ)}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hξ : Measurable ξ) (hlaw : P.map ηL = Q.map ξ)
    (hmeas : NullMeasurableSet {f : C(ℝ, ℂ) | ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b))} (Q.map ξ))
    (hdisk : ∀ᵐ ω ∂Q, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ξ ω '' Icc a b))) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b →
      Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (ηL ω '' Icc a b)) := by
  let S : Set C(ℝ, ℂ) := {f | ∀ a b : ℝ, a < b →
    Nonempty (closedBall (0 : ℂ) 1 ≃ₜ (f '' Icc a b))}
  have hmeasP : NullMeasurableSet S (P.map ηL) := by
    rw [hlaw]
    exact hmeas
  have hz : Q (ξ ⁻¹' Sᶜ) = 0 := by
    have h := hdisk
    rw [Filter.Eventually, mem_ae_iff] at h
    exact h
  have heq : P (ηL ⁻¹' Sᶜ) = Q (ξ ⁻¹' Sᶜ) := by
    rw [← Measure.map_apply₀ D.measurable_curves.1.aemeasurable hmeasP.compl,
      hlaw, Measure.map_apply₀ hξ.aemeasurable hmeas.compl]
  change ∀ᵐ ω ∂P, ηL ω ∈ S
  rw [Filter.Eventually, mem_ae_iff]
  exact heq.trans hz

end MatedCRTHarmonic.MoTInput
