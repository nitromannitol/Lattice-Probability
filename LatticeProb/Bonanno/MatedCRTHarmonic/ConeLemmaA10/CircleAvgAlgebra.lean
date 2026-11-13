/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CircleAvgAlgebra at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss

/-!
# Circle averages of sums

This adapter records the linearity of the distributional circle average whenever the defining
mollified averages converge. It is used to verify that adding the DMS14 logarithmic rooting
shift preserves the unit-circle normalization.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.CircleAvg

/-- Mollified circle averages are additive in the distribution. -/
lemma mollAvg_add (g₁ g₂ : DistC) (n : ℕ) (z : ℂ) (r : ℝ) :
    mollAvg (g₁ + g₂) n z r = mollAvg g₁ n z r + mollAvg g₂ n z r := by
  rw [mollAvg_eq, mollAvg_eq, mollAvg_eq, add_apply]

/-- The circle average of a sum is the sum of its circle averages when both defining limits
exist. -/
theorem circleAvg_add_of_tendsto {g₁ g₂ : DistC} {r : ℝ} {z : ℂ} {a b : ℝ}
    (h₁ : Tendsto (fun n => mollAvg g₁ n z r) atTop (𝓝 a))
    (h₂ : Tendsto (fun n => mollAvg g₂ n z r) atTop (𝓝 b)) :
    circleAvg (g₁ + g₂) r z = a + b := by
  apply circleAvg_eq_of_tendsto
  simpa only [mollAvg_add] using h₁.add h₂

end MatedCRTHarmonic.ConeLemmaA10

