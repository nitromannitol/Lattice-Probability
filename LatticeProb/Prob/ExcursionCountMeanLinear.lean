import LatticeProb.Prob.ExcursionCountMeanAdditive
import LatticeProb.Analysis.AdditiveENNRealHalfLine

/-!
# The mean excursion count of Brownian motion is linear in the level

For a real Brownian motion `B` with continuous paths and `ε > 0`, let `J(b)` be the number of excursions of `B` above
its running minimum, of length larger than `ε`, completed before the first passage below `B 0 - b`. The mean
`b ↦ E J(b)` is additive on `[0, ∞)` (`lintegral_pathExcursionCount_add`), hence

  `E J(b) = b * E J(1)` for every `b > 0`

(in `ℝ≥0∞`, with no finiteness assumption), and `b ↦ E J(b)` is monotone on `[0, ∞)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The mean excursion count is monotone in the level.** -/
theorem monotoneOn_lintegral_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) :
    MonotoneOn (fun b => ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) (Set.Ici 0) :=
  monotoneOn_of_add fun _ _ ha hb => lintegral_pathExcursionCount_add hB hm hcont ha hb hε

/-- **The mean excursion count is linear in the level.** For a real Brownian motion `B` with continuous paths,
`ε > 0` and `b > 0`, the mean number of excursions above the running minimum of length larger than `ε` completed
before the first passage below `B 0 - b` is `b` times the mean for the level `1`. -/
theorem lintegral_pathExcursionCount_eq_mul [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {ε : ℝ} (hε : 0 < ε) {b : ℝ}
    (hb : 0 < b) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P =
      ENNReal.ofReal b * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) 1 ε : ℝ≥0∞) ∂P :=
  eq_ofReal_mul_of_add (m := fun b => ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P)
    (fun _ _ ha hb => lintegral_pathExcursionCount_add hB hm hcont ha hb hε) hb

end LatticeProb.LadderSet
