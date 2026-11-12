/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P2C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P2A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P0
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L1_3
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 2: convergence in probability of the truncated local metrics (P-2)

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
Step 2, (eqn-close-pts-conv) T:1368–1372: "by Lemma 2.1 we have `𝔞⁻¹ D̂^ε(u,v) → D(u,v)` and
`𝔞⁻¹ D̂^ε(u,∂O') → D(u,∂O')` in probability. Therefore
`𝔞⁻¹D̂^ε(u,v) 1{D̂^ε(u,v) < D̂^ε(u,∂O')} → D(u,v) 1{D(u,v) < D(u,∂O')}` in probability."
Here with the continuous truncation `truncW` (T12P2A) in place of the indicator, uniformly on
`W̄ × W̄`, and with the localized LFPP `locSqC` on `W̄`:

* `truncW_eq_of_goodLim` — for a limit `x` of Lemma 2.5 B, `truncW (d_W) = truncW (D|_{W̄²})`.
* `tendstoInMeasure_truncW_lfpp` — `truncW(𝔞⁻¹D^{ε_{ψ n}}_h(·,·;W̄)) → truncW(D_h|_{W̄²})` in
  probability (Lemma 1.3 with `X = J h`; `D_h` is determined by `h`, `hdet`).
* `tendstoInMeasure_truncW_loc` — the same for the localized LFPP `D̂^ε` (Lemma 2.1,
  `tendsto_measure_locSqC_sub`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.T12

open Blueprint MetricGeometry LFPP

/-- `D ↦ truncW (D|_{W̄²})` -/
def truncD (W : dyadicDomainsC) : C(C(ℂ × ℂ, ℝ), C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)) :=
  ⟨fun D => truncW W (restrSq (closure (W : Set ℂ)) D),
    (continuous_truncW W).comp (restrSq (closure (W : Set ℂ))).continuous⟩

end LQGMetric.DFGPS.T12
