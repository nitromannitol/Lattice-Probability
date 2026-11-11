import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure

/-!
# Three literature inputs used as hypotheses

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795]:
the literature inputs `WholePlaneLQGBallMassBounds`, `LQGMeasureCoordChange` and `LQGMeasureExistence` of that
paper, with the same binders and conclusions, stated with the predicates of this library (`IsWholePlaneGFF`,
`IsLQGMeasureOfField`, `IsLQGLimit`, `fieldCircleAverage`, `PolyHighProb`).

These are definitions of propositions from the literature, used ONLY as hypotheses by the statements that need them.
They are assumed, not proved, here; no theorem about them is proved here, and no value of them is asserted. The
published source of each input is given in its docstring.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

/-- Literature input `WholePlaneLQGBallMassBounds`, used only as a hypothesis (assumed, not proved here).
Source: Ding and Gwynne, *The fractal dimension of Liouville quantum gravity:
universality, monotonicity, and bounds*, Comm. Math. Phys. 374 (2020), arXiv:1807.01072, Lemma 3.8 (p. 25), whole-plane
case used. -/
def WholePlaneLQGBallMassBoundsLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ βlower βupper : ℝ, 0 < βlower → βlower < 2 / (2 + γ) ^ 2 → 2 / (2 - γ) ^ 2 < βupper →
      PolyHighProb P fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ μ ω (Metric.ball z (ε ^ βlower))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, μ ω (Metric.ball z (ε ^ βupper)) ≤ ENNReal.ofReal ε}

/-- Literature input `LQGMeasureCoordChange`, used only as a hypothesis (assumed, not proved here), at `α₀ = 0` in the
square positivity. Source: Duplantier-Sheffield 2011, Proposition 2.1 (p. 13; a.s. for a
fixed conformal map); Sheffield-Wang 2016 (*Field-measure correspondence in Liouville quantum gravity almost surely commutes
with all conformal maps simultaneously*, arXiv:1605.06171v2), Theorem 1.1 (a.s. convergence as `ε → 0`) and Theorem 1.4
(p. 3; all conformal maps simultaneously). Scope: only complex affine maps. -/
def LQGMeasureCoordChangeLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ μ : Ω → Measure ℂ,
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ᵐ ω ∂P, ∀ a : ℂ, a ≠ 0 → ∀ b : ℂ,
      IsLQGLimit γ (fun ε z => fieldCircleAverage α₀ (hcirc ω) (‖a‖ * ε) (a * z + b) + lqgQ γ * Real.log ‖a‖)
        ((μ ω).map fun x => (x - b) / a)

/-- Literature input `LQGMeasureExistence`, used only as a hypothesis (assumed, not proved here). Source: Bou-Rabee and
Gwynne (arXiv:2208.11795v3), Section 2.2, p. 9, states existence for this singular
whole-plane field. Duplantier-Sheffield (arXiv:0808.1560v2), Proposition 1.1, p. 5, and Berestycki-Powell
(arXiv:2404.16642v2), Theorem 2.1, p. 62, treat bounded-domain Dirichlet fields; transfer near the pole requires more
than the domain Markov property. Local finiteness near the singularity uses `α₀ < Q`. -/
def LQGMeasureExistenceLP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ μ : Ω → Measure ℂ, IsLQGMeasureOfField P γ α₀ hcirc μ

end LatticeProb.LQG
