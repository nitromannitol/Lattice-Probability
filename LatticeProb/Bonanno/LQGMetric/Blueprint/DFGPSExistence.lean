/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSExistence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP

/-!
# Blueprint: DFGPS Theorem 1.2 (subsequential limits of LFPP are weak LQG metrics)

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
percolation*, arXiv:1905.00380 (DFGPS), `literature/src/1905.00380/lqg-metric-estimates-final.tex`,
l. 345–348:

> **Theorem 1.2.** Let γ ∈ (0,2). For every sequence of ε's tending to zero, there is a weak
> γ-LQG metric D and a subsequence {ε_n}_{n∈ℕ} for which the following is true. Let h be a
> whole-plane GFF, or more generally a whole-plane GFF plus a bounded continuous function. Then the
> re-scaled LFPP metrics 𝔞_{ε_n}⁻¹ D_h^{ε_n} from (1.4) converge in probability to D_h.

DFGPS's normalization (l. 285): "For ε > 0, let 𝔞_ε be the median of the D_h^ε-distance between
the left and right boundaries of the unit square along paths which stay in the unit square." This
differs from GM's 𝔞_ε (GM l. 223, `aEps`, no constraint on the paths), so it is defined here as
`aEpsDF`; `aEps` is unchanged (DEC-A D-A2: Theorem 1.1 keeps GM's 𝔞_ε, the bridge is GM.S1.16′).
Readings (blueprint/M1.md §1, proposed DEVIATIONS entry BP-M1-2):
* "the unit square" is the closed square `[0,1]²` (the paths start and end on its boundary);
* the field is the whole-plane GFF normalized by `h_1(0) = 0` (left implicit at l. 285; DFGPS
  l. 1061 and l. 1336 use this normalization, as GM l. 223 does), i.e. the law `normGFFLaw`;
* "the median" is the lower median `lowerMedian`, as for `aEps` (decision D7);
* "D_h^ε-distance along paths which stay in the unit square" is the infimum of the LFPP length
  `∫₀¹ e^{ξ h*_ε(P(t))} |P'(t)| dt` over piecewise C¹ paths `P` in `[0,1]²` (DFGPS (1.4) with the
  constraint on `P`), as `lfppCross` does without the constraint;
* "a weak γ-LQG metric" is `∃ c, IsWeakLQGMetric γ D c`; "converge in probability" is w.r.t. the
  local uniform topology on `ℂ × ℂ` (DFGPS l. 286, 314–316), i.e. `TendstoInProbLU`; "a sequence
  of ε's tending to zero" is a sequence of positive reals tending to `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- the closed unit square `[0,1]²` -/
def closedUnitSquare : Set ℂ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}

/-- the LFPP distance `D^ε_h(left side, right side; [0,1]²)` along piecewise C¹ paths staying in
the closed unit square (DFGPS l. 285), as a real number (`toReal`; junk `0` if infinite) -/
def lfppCrossIn (ξ ε : ℝ) (h : DistC) : ℝ :=
  (⨅ z ∈ leftSide, ⨅ w ∈ rightSide,
    ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w ∧ ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ closedUnitSquare},
      lfppLen ξ (heatMollify ε h) P.1).toReal

/-- DFGPS's `𝔞_ε` (DFGPS l. 285): the (lower) median of the internal LFPP crossing distance of
`[0,1]²` for the whole-plane GFF normalized by `h_1(0) = 0`. Mirrors `aEps` (GM l. 223). -/
def aEpsDF (ξ ε : ℝ) : ℝ := lowerMedian normGFFLaw (lfppCrossIn ξ ε)

/-- **DFGPS Theorem 1.2** (DFGPS l. 345–348): for `γ ∈ (0,2)` and every sequence `ε_k → 0` of
positive reals there are a weak γ-LQG metric `D` (with some scaling constants `c`) and a
subsequence `ε_{φ n}` such that for every whole-plane GFF plus a bounded continuous function `h`,
`(𝔞^{DF}_{ε_{φ n}})⁻¹ D_h^{ε_{φ n}} → D_h` in probability (local uniform topology). -/
def DFGPSExistence : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ ε : ℕ → ℝ, (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
    ∃ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          TendstoInProbLU P
            (fun n ω => (aEpsDF (xiGamma γ) (ε (φ n)))⁻¹ • lfppDist (xiGamma γ) (ε (φ n)) (h ω))
            atTop (fun ω => (D (h ω)).1)

end LQGMetric.Blueprint
