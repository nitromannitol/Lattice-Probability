/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.FiniteProcessMixture at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.FiniteMixtureLaw
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# Process law of the finite rooting mixture

The finite-dimensional mixture identity upgrades to equality of the complete process laws on
`TestC0 → ℝ`. This is a direct application of the existing projective-limit uniqueness theorem
`LQGMetric.WhiteNoise.map_eq_of_forall_finset'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The finite covariance translation of the mean-zero pairing process at root `z`. -/
def finiteCircleCovShift (γ : ℝ) (n : ℕ) (ε : ℝ) (z : ℂ) : TestC0 → ℝ :=
  fun ψ ↦ γ * logCov ψ.1 (finiteCircleIndex n z ε).1

/-- **Full finite-stage process law for DMS14 Lemma A.10.** The product finite-circle Wick
tilt, mapped to the complete mean-zero pairing process, equals the product base law mapped to
the same process plus its finite covariance translation. -/
theorem map_finiteCircleTiltMixture_eq_covShift
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hh : IsNormalizedWPGFF h P) (γ : ℝ) (n : ℕ)
    (ε : ℝ) :
    ((P.prod ν).withDensity fun p : Ω × ℂ ↦
        finiteCircleDensity (h := h) γ n p.2 ε p.1).map
          (fun p ↦ pair0 (h p.1)) =
      (P.prod ν).map (fun p ↦
        pair0 (h p.1) + finiteCircleCovShift γ n ε p.2) := by
  letI := hh.1.gaussian.isProbabilityMeasure
  let μ : Measure (Ω × ℂ) :=
    (P.prod ν).withDensity fun p ↦ finiteCircleDensity (h := h) γ n p.2 ε p.1
  let X : TestC0 → Ω × ℂ → ℝ := fun ψ p ↦ pair0 (h p.1) ψ
  let X' : TestC0 → Ω × ℂ → ℝ := fun ψ p ↦
    pair0 (h p.1) ψ + finiteCircleCovShift γ n ε p.2 ψ
  have hX : Measurable (fun p ψ ↦ X ψ p) :=
    measurable_pi_iff.2 fun ψ ↦
      ((measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst
  have hX' : Measurable (fun p ψ ↦ X' ψ p) :=
    measurable_pi_iff.2 fun ψ ↦
      (((measurable_evalDist ψ.1).comp hh.1.measurable).comp measurable_fst).add
        ((measurable_finiteCircleCovShift hh γ n ε ψ).comp measurable_snd)
  have hrestrict : Measurable (fun p ↦ (∅ : Finset TestC0).restrict (X · p)) :=
    (Finset.measurable_restrict (∅ : Finset TestC0)).comp hX
  have hmap_univ :
      μ.map (fun p ↦ (∅ : Finset TestC0).restrict (X · p)) Set.univ = μ Set.univ := by
    rw [Measure.map_apply hrestrict MeasurableSet.univ]
    rfl
  have hμuniv : μ Set.univ =
      (P.prod ν).map (fun p ↦ (∅ : Finset TestC0).restrict (X' · p)) Set.univ := by
    calc
      μ Set.univ =
          μ.map (fun p ↦ (∅ : Finset TestC0).restrict (X · p)) Set.univ := hmap_univ.symm
      _ = (P.prod ν).map
          (fun p ↦ (∅ : Finset TestC0).restrict (X' · p)) Set.univ :=
        congrArg (fun m : Measure ((∅ : Finset TestC0) → ℝ) ↦ m Set.univ) <| by
          simpa only [μ, X, X', finiteCircleCovShift, Pi.add_apply] using
            map_finiteCircleTiltMixture_restrict_eq_covShift
              (ν := ν) hh γ n ε (∅ : Finset TestC0)
  letI : IsFiniteMeasure μ := ⟨by
    rw [hμuniv]
    exact measure_lt_top _ _⟩
  refine LQGMetric.WhiteNoise.map_eq_of_forall_finset'
    (P := μ) (P' := P.prod ν) (X := X) (X' := X')
    hX.aemeasurable hX'.aemeasurable fun I ↦ ?_
  simpa only [μ, X, X', finiteCircleCovShift, Pi.add_apply] using
    map_finiteCircleTiltMixture_restrict_eq_covShift (ν := ν) hh γ n ε I

end MatedCRTHarmonic.ConeLemmaA10

