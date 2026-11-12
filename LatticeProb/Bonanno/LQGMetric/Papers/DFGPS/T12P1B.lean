/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T12P1B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T12P1A
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import Mathlib.Topology.UniformSpace.Dini

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.2, Step 1 packaging (packet P-1a of D90): the glued metric `patchD`

Source: DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Theorem 1.2,
T:1343–1349 (the map `h ↦ D_h` is the a.s. limit of the LFPP along a subsequence, "Euclidean
otherwise", T:1385) and T:1376–1385 (patching `D_{h+φf}(·,·;V)` over bounded `V`); decision D90 (Q2).

* `locLim ξ εs hεs W g` — the limit in `C(W̄ × W̄, ℝ)` of the localized LFPP
  `𝔞_ε⁻¹ D̂^ε_g(·,·;W̄)` (`L217.locSqC`) along `εs` (junk if it does not converge).
* `measurable_locLim` — measurable in `g` for every `g` (limits of measurable maps into a Polish
  space, mathlib `StronglyMeasurable.limUnder`).
* `patchD ξ εs hεs g` — the locally uniform limit of `locLim (sqW n) g ∘ (clamp × clamp)`,
  made a continuous metric by `toContMetric`; `measurable_patchD`.
* `intExt D W` — the continuous extension to `W̄ × W̄` of `D(·,·;W)` from `W × W` (junk `0` if there
  is none); `intExt_eq` (uniqueness).
* `patchD_eq` — if `D` is a length metric and each `locLim (sqW n) g` agrees with `D(·,·;sqW n)` on
  `sqW n × sqW n`, then `patchD g = D` (Dini: `D(·,·;sqW n) ↓ D` locally uniformly).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS.T12

open MetricGeometry LFPP

theorem compactSpace_closure_dy (W : dyadicDomainsC) : CompactSpace (closure (W : Set ℂ)) :=
  isCompact_iff_compactSpace.1 W.2.1.isBounded.isCompact_closure

variable {ξ : ℝ} {εs : ℕ → ℝ} {hεs : ∀ k, 0 < εs k}

end LQGMetric.DFGPS.T12
