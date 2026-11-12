/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Blueprint at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGDimension.Statement.Defs
import LatticeProb.Bonanno.LQGMetric.Basic
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension

/-!
# Ding–Gwynne: LFPP distances and DG Theorem 1.5 (cited result, explicit hypothesis)

Source: J. Ding, E. Gwynne, *The fractal dimension of Liouville quantum gravity: universality,
monotonicity, and bounds*, arXiv:1807.01072, `literature/src/1807.01072/metric-comparison-final.tex`
(cited `DG:`).

* LFPP (DG:305): "the infimum over all piecewise continuously differentiable paths
  `P : [0,T] → D̄` of `∫_0^T e^{ξ h_δ(P(t))} |P'(t)| dt`, where `h_δ(z)` denotes the circle
  average of `h` over `∂B_δ(z)`".
* Restricted LFPP (DG:322–328, Def. 1.3 `def-restricted-lgd`): paths `P : [0,T] → Ū`.
* DG Thm 1.5 (`thm-lfpp-compare`, DG:336–356): for `γ ∈ (0,2)`, `ξ = γ/d_γ`, `h` a whole-plane
  GFF normalized so that its circle average over `∂𝔻` is zero, (1.5a) for `z ≠ w`, w.p. → 1 as
  `δ → 0`, `D^δ(z,w) = δ^{1 − 2/d_γ − γ²/(2d_γ) + o(1)}`; (1.5b) for each open `U` and compact
  `K ⊂ U`, w.p. → 1, `max_{z,w∈K} D^δ(z,w;U) = δ^{1 − 2/d_γ − γ²/(2d_γ) + o(1)}` (and the same
  for `D^δ(K,∂U)`).

Modelling (proposed deviations DG-B1…B3, see the P2-ROUTEB report):
* Field: `h_δ(z)` is a process `hc δ z ω` with `LQGDimension.IsGFFCircleAverage hc P` (centred
  Gaussian, covariance of the circle averages of the whole-plane GFF normalized by `h_1(0) = 0`,
  continuous in `z` for every `ω`), i.e. the continuous version of DS Prop 3.1. Every normalized
  whole-plane GFF has such a version (`LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized`).
* Paths are parametrized by `[0,1]` (a linear reparametrization of `[0,T]` changes no LFPP length)
  and are piecewise `C¹` exactly as in `LQGDimension.IsAdmissiblePath`; the LFPP length is
  `LQGDimension.lfppLength`.
* "w.p. → 1, `X = δ^{λ+o(1)}`" is read as: for every `η > 0`, the (outer) probability that
  `δ^{λ+η} ≤ X ≤ δ^{λ−η}` fails tends to `0` as `δ ↓ 0`.
* (1.5b) is used only for bounded connected open `U` and compact `K ⊂ U` with two distinct points
  (for a one-point `K` the maximum is `0`, and for `K` meeting two components of `U` it is `∞`, so
  DG's sentence needs these readings); its second half (`D(K,∂U)`) is not used and is omitted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- A piecewise `C¹` path `p : [0,1] → S` from `z` to `w` (DG:305, DG:326), with the same
piecewise-`C¹` clause as `LQGDimension.IsAdmissiblePath`. -/
structure IsDGPath (S : Set ℂ) (z w : ℂ) (p : ℝ → ℂ) : Prop where
  source : p 0 = z
  target : p 1 = w
  mapsTo : MapsTo p (Icc 0 1) S
  continuousOn : ContinuousOn p (Icc 0 1)
  piecewise_contDiff : ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
    t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 p (Icc (t i.castSucc) (t i.succ))

/-- LFPP distance `inf_P ∫_P e^{ξ φ} |dz|` over piecewise `C¹` paths in `S` from `z` to `w`.
DG's `D^{ξ,δ}_{h,LFPP}(z,w)` is `dgLFPP ξ h_δ univ z w`, and the restricted distance
`D^{ξ,δ}_{h,LFPP}(z,w;U)` (paths in `Ū`, DG:326) is `dgLFPP ξ h_δ (closure U) z w`. -/
def dgLFPP (ξ : ℝ) (φ : ℂ → ℝ) (S : Set ℂ) (z w : ℂ) : ℝ :=
  ⨅ p : {p : ℝ → ℂ // IsDGPath S z w p}, LQGDimension.lfppLength ξ φ p.1

/-- `max_{z,w ∈ K} D(z,w;U)` (DG (1.5b)), valued in `[0,∞]`. -/
def dgDiam (ξ : ℝ) (φ : ℂ → ℝ) (U K : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ K, ⨆ w ∈ K, ENNReal.ofReal (dgLFPP ξ φ (closure U) z w)

/-- DG's LFPP exponent `1 − 2/d_γ − γ²/(2d_γ)` (DG (1.5)). -/
def dgLambda (γ : ℝ) : ℝ := 1 - 2 / dGamma γ - γ ^ 2 / (2 * dGamma γ)

end DG
end LQGMetric
