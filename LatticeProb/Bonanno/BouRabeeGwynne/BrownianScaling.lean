/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianScaling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianLawUniqueness

/-! Positive parabolic scaling preserves the actual continuous Euclidean
Brownian path law. The coordinate scaling theorem is the pinned mathlib
Gaussian characterization, and the full path-law equality uses uniqueness. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Spatial scale `r⁻¹` and time scale `r²` on actual continuous paths. -/
noncomputable def scaledBrownianPath {d : ℕ} (r : ℝ≥0)
    (ω : BrownianPath d) : BrownianPath d where
  toFun t := (r : ℝ)⁻¹ • ω (r ^ 2 * t)
  continuous_toFun := by fun_prop

@[simp] lemma scaledBrownianPath_apply {d : ℕ} (r : ℝ≥0)
    (ω : BrownianPath d) (t : ℝ≥0) :
    scaledBrownianPath r ω t = (r : ℝ)⁻¹ • ω (r ^ 2 * t) := rfl

lemma measurable_scaledBrownianPath {d : ℕ} (r : ℝ≥0) :
    Measurable (scaledBrownianPath (d := d) r) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun ω : BrownianPath d => (r : ℝ)⁻¹ • ω (r ^ 2 * t))
  exact (by fun_prop : Continuous
    (fun ω : BrownianPath d => (r : ℝ)⁻¹ • ω (r ^ 2 * t))).measurable

/-- Positive scaling preserves the genuine Gaussian coordinate laws and
independence of the whole coordinate processes. -/
theorem standardBrownianLaw_scale {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {r : ℝ≥0} (hr : 0 < r) :
    IsStandardBrownianLaw (μ.map (scaledBrownianPath r)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hprob : IsProbabilityMeasure (μ.map (scaledBrownianPath r)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_scaledBrownianPath r).aemeasurable).mpr
      inferInstance
  letI := hprob
  refine ⟨hprob, fun i => ?_, ?_⟩
  · have hcoord : IsBrownianReal
        (fun t (ω : BrownianPath d) => (r : ℝ)⁻¹ * ω (r ^ 2 * t) i) μ := by
      have hscaled := (hμ.2.1 i).smul (c := r ^ 2) (pow_ne_zero 2 hr.ne')
      have hsqrt : Real.sqrt ((r ^ 2 : ℝ≥0) : ℝ) = (r : ℝ) := by
        rw [← Real.coe_sqrt, NNReal.sqrt_sq]
      simpa only [hsqrt] using hscaled
    refine { toIsPreBrownianReal := ?_, cont := ?_ }
    · constructor
      intro I
      have hm : Measurable (fun ω : BrownianPath d => I.restrict (fun t => ω t i)) :=
        I.measurable_restrict.comp (measurable_brownianCoordinatePath i)
      refine ⟨hm.aemeasurable, ?_⟩
      rw [Measure.map_map hm (measurable_scaledBrownianPath r)]
      exact (hcoord.hasLaw I).map_eq
    · exact Filter.Eventually.of_forall (fun ω => by fun_prop)
  · have hind := hμ.2.2.comp
      (fun (_ : Fin d) (b : ℝ≥0 → ℝ) => fun t : ℝ≥0 => (r : ℝ)⁻¹ * b (r ^ 2 * t))
      (by intro i; fun_prop)
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_brownianCoordinatePath i).aemeasurable)]
    rw [Measure.map_map measurable_brownianCoordinates (measurable_scaledBrownianPath r)]
    simp_rw [Measure.map_map (measurable_brownianCoordinatePath _) (measurable_scaledBrownianPath r)]
    exact hind.map_fun_eq_pi_map (fun i =>
      ((measurable_brownianCoordinatePath i).comp
        (measurable_scaledBrownianPath r)).aemeasurable)

/-- Brownian scaling as an equality of the actual probability measures on
continuous Euclidean paths, for every strictly positive spatial scale. -/
theorem standardBrownianLaw_map_scale {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {r : ℝ≥0} (hr : 0 < r) :
    μ.map (scaledBrownianPath r) = μ :=
  standardBrownianLaw_unique (standardBrownianLaw_scale hμ hr) hμ

end BouRabeeGwynne
