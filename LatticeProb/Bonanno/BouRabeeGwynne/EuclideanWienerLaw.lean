/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.EuclideanWienerLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianContinuousLaw
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.Probability.Independence.Basic

/-!
# Actual Euclidean Wiener law

The finite product of the constructed real Wiener law is mapped by coordinate
assembly into continuous Euclidean paths. Its Gaussian coordinate laws and
independence are proved, yielding exactly `IsStandardBrownianLaw`.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace BouRabeeGwynne

/-- Assemble finitely many continuous real paths into the Euclidean path. -/
noncomputable def assembleBrownianPath {d : ℕ}
    (ω : Fin d → C(ℝ≥0, ℝ)) : BrownianPath d where
  toFun t := WithLp.toLp 2 (fun i ↦ ω i t)
  continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
    (continuous_pi fun i ↦ (ω i).continuous)

@[simp] lemma assembleBrownianPath_apply {d : ℕ}
    (ω : Fin d → C(ℝ≥0, ℝ)) (t : ℝ≥0) (i : Fin d) :
    assembleBrownianPath ω t i = ω i t := rfl

lemma measurable_assembleBrownianPath {d : ℕ} :
    Measurable (assembleBrownianPath (d := d)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp
    (Measurable.of_eval fun i ↦ (continuous_eval_const t).measurable.comp
      (measurable_pi_apply i))

/-- The Euclidean Wiener measure is the image of independent real Wiener paths. -/
noncomputable def euclideanWienerLaw (d : ℕ) : Measure (BrownianPath d) :=
  (Measure.pi (fun _ : Fin d ↦ realWienerLaw)).map assembleBrownianPath

instance euclideanWienerLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (euclideanWienerLaw d) :=
  (Measure.isProbabilityMeasure_map_iff
    measurable_assembleBrownianPath.aemeasurable).mpr inferInstance

private lemma measurable_euclideanWienerCoordinate {d : ℕ} (i : Fin d) :
    Measurable (fun (ω : BrownianPath d) (t : ℝ≥0) ↦ ω t i) := by
  apply Measurable.of_eval
  intro t
  exact (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω t i)).measurable

lemma isBrownianReal_euclideanWienerLaw {d : ℕ} (i : Fin d) :
    IsBrownianReal (fun t (ω : BrownianPath d) ↦ ω t i) (euclideanWienerLaw d) where
  toIsPreBrownianReal := by
    constructor
    intro I
    have hm : Measurable (fun ω : BrownianPath d ↦ I.restrict (fun s ↦ ω s i)) :=
      I.measurable_restrict.comp (measurable_euclideanWienerCoordinate i)
    refine ⟨hm.aemeasurable, ?_⟩
    rw [euclideanWienerLaw, Measure.map_map hm measurable_assembleBrownianPath]
    exact ((isBrownianReal_realWienerLaw.hasLaw I).comp
      (measurePreserving_eval (fun _ : Fin d ↦ realWienerLaw) i).hasLaw).map_eq
  cont := Filter.Eventually.of_forall fun ω ↦ by fun_prop

lemma iIndepFun_coordinates_euclideanWienerLaw (d : ℕ) :
    iIndepFun (fun (i : Fin d) (ω : BrownianPath d) ↦ fun t : ℝ≥0 ↦ ω t i)
      (euclideanWienerLaw d) := by
  have hmeas : Measurable (fun ω : C(ℝ≥0, ℝ) ↦ fun t : ℝ≥0 ↦ ω t) := by
    exact Measurable.of_eval fun t ↦ (continuous_eval_const t).measurable
  have hind := iIndepFun_pi (μ := fun _ : Fin d ↦ realWienerLaw)
    (X := fun _ : Fin d ↦ fun ω : C(ℝ≥0, ℝ) ↦ fun t : ℝ≥0 ↦ ω t)
    (fun _ ↦ hmeas.aemeasurable)
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (measurable_euclideanWienerCoordinate i).aemeasurable)]
  have hmcoords : Measurable (fun (ω : BrownianPath d) (i : Fin d) (t : ℝ≥0) ↦ ω t i) :=
    Measurable.of_eval measurable_euclideanWienerCoordinate
  simp only [euclideanWienerLaw]
  rw [Measure.map_map hmcoords measurable_assembleBrownianPath]
  simp_rw [Measure.map_map (measurable_euclideanWienerCoordinate _) measurable_assembleBrownianPath]
  exact hind.map_fun_eq_pi_map (fun i ↦ (hmeas.comp (measurable_pi_apply i)).aemeasurable)

theorem isStandardBrownianLaw_euclideanWienerLaw (d : ℕ) :
    IsStandardBrownianLaw (euclideanWienerLaw d) :=
  ⟨inferInstance, isBrownianReal_euclideanWienerLaw,
    iIndepFun_coordinates_euclideanWienerLaw d⟩

end BouRabeeGwynne
