/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8
import LatticeProb.Bonanno.LQGMetric.LFPP.Dyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9 (`lem-lfpp-tight-dyadic`, T:903–906): statement

"Let `W ⊂ ℂ` be a dyadic domain. The laws of the internal metrics `𝔞_ε⁻¹ D_h^ε(·,·;W̄)` for
`ε ∈ (0,1)` are tight w.r.t. the uniform topology on `W̄ × W̄` and any subsequential limit of
these laws is supported on length metrics which induce the Euclidean topology on `W̄`."

Readings: as `Lem2_8` (BP-DF-1), with `closedSq a s` replaced by `closure W`. The proof
(T:908) first reduces to connected `W̄` ("By considering each connected component separately, we
can assume without loss of generality that `W̄` is connected"); since metrics here are real valued
(`toReal`, junk `0` for `D = ∞` between components), the statement is made for dyadic domains with
connected closure, which is the case the proof treats (proposed DEVIATIONS entry DF-L29-CONN).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint

/-- **DFGPS Lemma 2.9** (`lem-lfpp-tight-dyadic`, T:903–906), for `W̄` connected. -/
def Lem2_9 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ W : Set ℂ, LFPP.IsDyadicDomain W → IsConnected (closure W) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P →
      (∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous fun p : closure W × closure W =>
        (aEpsDF (xiGamma γ) ε)⁻¹ *
          (LFPP.lfppDOn (xiGamma γ) (heatMollify ε (h ω)) (closure W) p.1 p.2).toReal) ∧
      IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
        μ = P.map fun ω => lfppSqC (xiGamma γ) ε (h ω) (closure W)} ∧
      ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closure W × closure W, ℝ))
        (μ : ProbabilityMeasure C(closure W × closure W, ℝ)),
        (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
          (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closure W)) →
        Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closure W × closure W, ℝ)), IsSqLengthMetric d

end LQGMetric.DFGPS
