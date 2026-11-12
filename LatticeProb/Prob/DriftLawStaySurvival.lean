/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.UpcrossStay
import LatticeProb.Prob.UpcrossLaplaceIdentity
import LatticeProb.Prob.BrownianDriftSurvival

/-!
# The drifted Brownian path stays above `-δ` forever with positive probability

For a Brownian motion with positive drift `μ`, the law `driftLaw P B hcont μ` on path space gives
the event `staySet δ` (the path stays strictly above `-δ` for all times) the probability
`1 - exp (-2 μ δ)`, which is positive for `δ > 0`.

* `LatticeProb.driftLaw_staySet_eq`: `driftLaw P B hcont μ (staySet δ) = ofReal (1 - exp (-(2 μ δ)))`.
* `LatticeProb.driftLaw_staySet_measure_pos`: this probability is positive.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Survival probability under the drifted Brownian law.**  For `μ > 0` and `δ > 0` the law of
Brownian motion with drift `μ` stays strictly above `-δ` for all times with probability
`1 - exp (-2 μ δ)`. -/
theorem driftLaw_staySet_eq (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {μ : ℝ} (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    driftLaw P B hcont μ (staySet δ) = ENNReal.ofReal (1 - Real.exp (-(2 * μ * δ))) := by
  have hpm : Measurable (pathMap B hcont) := measurable_pathMap B hm hcont
  rw [driftLaw, Measure.map_apply (measurable_driftMap μ) (measurableSet_staySet δ),
    Measure.map_apply hpm ((measurable_driftMap μ) (measurableSet_staySet δ))]
  exact measure_forall_drift_gt hB hm hcont hμ hδ

/-- **The drifted Brownian path stays above `-δ` forever with positive probability.** -/
theorem driftLaw_staySet_measure_pos (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {μ : ℝ} (hμ : 0 < μ) {δ : ℝ} (hδ : 0 < δ) :
    0 < driftLaw P B hcont μ (staySet δ) := by
  rw [driftLaw_staySet_eq hB hm hcont hμ hδ, ENNReal.ofReal_pos, sub_pos]
  have h : -(2 * μ * δ) < 0 := by
    have : 0 < 2 * μ * δ := by positivity
    linarith
  exact (Real.exp_lt_exp.2 h).trans_eq Real.exp_zero

end LatticeProb
