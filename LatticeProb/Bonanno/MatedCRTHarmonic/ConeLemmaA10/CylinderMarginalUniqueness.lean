/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CylinderMarginalUniqueness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Uniqueness from bounded continuous cylinder observables

Equality of integrals against bounded continuous observables on every finite set of coordinates
implies equality of the finite-dimensional laws. The measures on the finite-dimensional Euclidean
spaces are regular, so Mathlib's compactly-supported-integral extensionality applies. The
existing projective-limit uniqueness theorem then identifies the full process laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric

/-- Equality of bounded-continuous-observable integrals identifies one fixed finite-coordinate
pushforward. -/
theorem map_restrict_eq_of_boundedContinuous_integrals
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : TestC0 → Ω → ℝ} {Y : TestC0 → Ω' → ℝ} (I : Finset TestC0)
    (hX : AEMeasurable (fun ω ψ => X ψ ω) μ)
    (hY : AEMeasurable (fun ω ψ => Y ψ ω) ν)
    (hobs : ∀ F : (I → ℝ) → ℝ,
      Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
        ∫ ω, F (I.restrict (X · ω)) ∂μ = ∫ ω, F (I.restrict (Y · ω)) ∂ν) :
    μ.map (fun ω => I.restrict (X · ω)) = ν.map (fun ω => I.restrict (Y · ω)) := by
  let rX : Ω → I → ℝ := fun ω => I.restrict (X · ω)
  let rY : Ω' → I → ℝ := fun ω => I.restrict (Y · ω)
  have hrX : AEMeasurable rX μ :=
    (Finset.measurable_restrict I).comp_aemeasurable hX
  have hrY : AEMeasurable rY ν :=
    (Finset.measurable_restrict I).comp_aemeasurable hY
  let μI : Measure (I → ℝ) := μ.map rX
  let νI : Measure (I → ℝ) := ν.map rY
  have : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have : IsFiniteMeasure νI := by
    dsimp [νI]
    infer_instance
  have htest : ∀ f : C_c(I → ℝ, ℝ),
      ∫ x, f x ∂μI = ∫ x, f x ∂νI := by
    intro f
    have hf_bound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
      have hrange : IsCompact (Set.range f) := f.hasCompactSupport.isCompact_range f.continuous
      obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hrange.isBounded
      refine ⟨C + ‖f 0‖, fun x => ?_⟩
      have hdist := hC ⟨x, rfl⟩ ⟨0, rfl⟩
      calc
        ‖f x‖ = ‖(f x - f 0) + f 0‖ := by congr 1; ring
        _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
        _ = dist (f x) (f 0) + ‖f 0‖ := by simp [Real.norm_eq_abs, Real.dist_eq]
        _ ≤ C + ‖f 0‖ := by linarith
    calc
      ∫ x, f x ∂μI = ∫ ω, f (rX ω) ∂μ := by
        dsimp [μI]
        exact integral_map hrX f.continuous.aestronglyMeasurable
      _ = ∫ ω, f (rY ω) ∂ν := by
        simpa only [rX, rY] using hobs f f.continuous hf_bound
      _ = ∫ x, f x ∂νI := by
        dsimp [νI]
        exact (integral_map hrY f.continuous.aestronglyMeasurable).symm
  have hmap : μI = νI :=
    Measure.ext_of_integral_eq_on_compactlySupported htest
  simpa only [μI, νI, rX, rY] using hmap

/-- The law of a real process is determined by integrals of bounded continuous observables of
each finite-coordinate restriction. -/
theorem map_process_eq_of_boundedContinuous_cylinder_integrals
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : TestC0 → Ω → ℝ} {Y : TestC0 → Ω' → ℝ}
    (hX : AEMeasurable (fun ω ψ => X ψ ω) μ)
    (hY : AEMeasurable (fun ω ψ => Y ψ ω) ν)
    (hobs : ∀ I : Finset TestC0, ∀ F : (I → ℝ) → ℝ,
      Continuous F → (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) →
        ∫ ω, F (I.restrict (X · ω)) ∂μ = ∫ ω, F (I.restrict (Y · ω)) ∂ν) :
    μ.map (fun ω ψ => X ψ ω) = ν.map (fun ω ψ => Y ψ ω) := by
  apply LQGMetric.WhiteNoise.map_eq_of_forall_finset' hX hY
  intro I
  exact map_restrict_eq_of_boundedContinuous_integrals I hX hY (hobs I)

end MatedCRTHarmonic.ConeLemmaA10

