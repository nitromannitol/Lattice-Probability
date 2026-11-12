import LatticeProb.Prob.UpcrossLaplaceIdentity
import LatticeProb.Prob.ContinuousPathLaw

/-!
# Reflection of Brownian motion with drift on path space

If `B` is a Brownian motion with continuous paths on a probability space, the law on
`C(ℝ≥0, ℝ)` of `-B` is the law of `B` (both have the Brownian finite-dimensional distributions),
and `-(w + μ t) = (-w) + (-μ) t`.  Hence the image of the law of Brownian motion with drift `μ`
under `w ↦ -w` is the law of Brownian motion with drift `-μ`.

* `LatticeProb.map_neg_pathLaw`: the path law of a Brownian motion is invariant under `w ↦ -w`;
* `LatticeProb.driftLaw_map_neg`: reflection carries the drift `μ` law to the drift `-μ` law.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Reflection `w ↦ -w` is measurable on path space. -/
theorem measurable_neg_pathSpace : Measurable fun v : C(ℝ≥0, ℝ) => -v := by
  refine measurable_pathValued_of_eval fun s => ?_
  exact ((continuous_eval_const s).measurable).neg

/-- The path law of a Brownian motion with continuous paths is invariant under reflection. -/
theorem map_neg_pathLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    (P.map (pathMap B hcont)).map (fun v : C(ℝ≥0, ℝ) => -v) = P.map (pathMap B hcont) := by
  have hF : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
  refine ContinuousPathLaw.continuousPath_measure_ext_of_coordinate_law ?_
  have hneg := measurable_neg_pathSpace
  have hev : Measurable fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t :=
    Measurable.of_eval fun t => ContinuousMapBorel.ContinuousMap.measurable_eval t
  rw [Measure.map_map hev hneg, Measure.map_map hev hF, Measure.map_map (hev.comp hneg) hF]
  have hBm : Measurable fun (ω : Ω) (t : ℝ≥0) => B t ω := measurable_pi_iff.2 hm
  have hBm' : Measurable fun (ω : Ω) (t : ℝ≥0) => -B t ω := measurable_pi_iff.2 fun t => (hm t).neg
  have h1 : IsProjectiveLimit (P.map fun (ω : Ω) (t : ℝ≥0) => B t ω)
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hBm]
    exact (hB.hasLaw I).map_eq
  have h2 : IsProjectiveLimit (P.map fun (ω : Ω) (t : ℝ≥0) => -B t ω)
      BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict hBm']
    exact (hB.neg.hasLaw I).map_eq
  exact h2.unique h1

/-- **Reflection of Brownian motion with drift.** The image of the law of `B_t + μ t` on path
space under `w ↦ -w` is the law of `B_t + (-μ) t`. -/
theorem driftLaw_map_neg [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) :
    (driftLaw P B hcont mu).map (fun v : C(ℝ≥0, ℝ) => -v) = driftLaw P B hcont (-mu) := by
  have hneg := measurable_neg_pathSpace
  have hcomm : (fun v : C(ℝ≥0, ℝ) => -v) ∘ driftMap mu = driftMap (-mu) ∘ fun v => -v := by
    funext v
    ext s
    simp only [Function.comp_apply, ContinuousMap.neg_apply, driftMap_apply]
    ring
  calc (driftLaw P B hcont mu).map (fun v : C(ℝ≥0, ℝ) => -v)
      = (P.map (pathMap B hcont)).map ((fun v : C(ℝ≥0, ℝ) => -v) ∘ driftMap mu) :=
        Measure.map_map hneg (measurable_driftMap mu)
    _ = ((P.map (pathMap B hcont)).map fun v : C(ℝ≥0, ℝ) => -v).map (driftMap (-mu)) := by
        rw [hcomm, ← Measure.map_map (measurable_driftMap (-mu)) hneg]
    _ = driftLaw P B hcont (-mu) := by rw [map_neg_pathLaw hB hm hcont]

end LatticeProb

end
