/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8Couple
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSInputs
import LatticeProb.Bonanno.LQGMetric.Metric.LengthLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8 (`lem-lfpp-tight-square`, T:872–875): statement

"Let `S ⊂ ℂ` be a closed square and let `h` be a whole-plane GFF plus a bounded continuous
function. The laws of the internal metrics `𝔞_ε⁻¹ D_h^ε(·,·;S)` for `ε ∈ (0,1)` are tight w.r.t.
the uniform topology on `S × S` and any subsequential limit of these laws is supported on length
metrics which induce the Euclidean topology on `S`."

Readings (BP-DF-1): tightness = continuity of each metric on `S × S` plus `IsTightMeasureSet` of
the laws on `C(S × S, ℝ)`; subsequential limits are taken along `ε_n → 0`. Since `S` is compact,
a metric `d ∈ C(S × S, ℝ)` (continuous for the Euclidean topology) induces the Euclidean topology
(a continuous bijection from a compact space onto a Hausdorff space is a homeomorphism), so
"length metric inducing the Euclidean topology" is `IsSqLengthMetric`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry

/-- the closed square `a + [0,s]²` -/
def closedSq (a : ℂ) (s : ℝ) : Set ℂ :=
  {x | a.re ≤ x.re ∧ x.re ≤ a.re + s ∧ a.im ≤ x.im ∧ x.im ≤ a.im + s}

/-- `(x, y) ↦ 𝔞_ε⁻¹ D_h^ε(x, y; S)` on `S × S` as a continuous map (junk `0` if discontinuous) -/
def lfppSqC (ξ ε : ℝ) (h : DistC) (S : Set ℂ) : C(S × S, ℝ) :=
  toCMap fun p : S × S => (aEpsDF ξ ε)⁻¹ * (LFPP.lfppDOn ξ (heatMollify ε h) S p.1 p.2).toReal

/-- `d` is a length metric on `S` (continuous on `S × S`, hence inducing the Euclidean topology
for compact `S`) -/
def IsSqLengthMetric {S : Set ℂ} (d : C(S × S, ℝ)) : Prop :=
  ∃ hd : IsMetricFun (⇑d), IsLengthMetricFun (⇑d) hd

/-- **DFGPS Lemma 2.8** (`lem-lfpp-tight-square`, T:872–875), exact statement. -/
def Lem2_8 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (a : ℂ) (s : ℝ), 0 < s →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P →
      (∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous fun p : closedSq a s × closedSq a s =>
        (aEpsDF (xiGamma γ) ε)⁻¹ *
          (LFPP.lfppDOn (xiGamma γ) (heatMollify ε (h ω)) (closedSq a s) p.1 p.2).toReal) ∧
      IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map fun ω => lfppSqC (xiGamma γ) ε (h ω) (closedSq a s)} ∧
      ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
        (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ)),
        (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
          (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closedSq a s)) →
        Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsSqLengthMetric d

end LQGMetric.DFGPS
