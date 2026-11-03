/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.LQGMetric at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Basic
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Statement layer, part 5: strong and weak γ-LQG metrics

`FOUNDATIONS.md` §6 (blocks copied verbatim). Source: GM (arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex`):
* strong γ-LQG metric, l. 293–307: "a measurable function h ↦ D_h from 𝒟'(ℂ) to the space of
  continuous metrics on ℂ such that the following is true whenever h is a whole-plane GFF plus a
  continuous function": I. Length space, II. Locality, III. Weyl scaling, IV. Coordinate change
  for translation and scaling;
* weak γ-LQG metric, l. 431–452: Axioms I–III, IV′. Translation invariance, V. Tightness across
  scales (used in the proof, not in the targets).
`Q γ = 2/γ + γ/2` (GM (1.3), `LQGMetric.Basic`), `ξ = xiGamma γ` (GM (1.1)). Decisions D4, D11;
deviations F9, F12, F13.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- A **(strong) γ-LQG metric** (GM l. 293–307): a measurable map `h ↦ D_h` from `𝒟'(ℂ)` to the
continuous metrics on `ℂ` satisfying Axioms I–IV whenever `h` is a whole-plane GFF plus a
continuous function. -/
structure IsStrongLQGMetric (γ : ℝ) (D : DistC → ContMetric) : Prop where
  measurable : Measurable D
  /-- I. Length space: a.s. `(ℂ, D_h)` is a length space. -/
  length : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength
  /-- II. Locality: for deterministic open `U`, `D_h(·,·;U)` is a.s. determined by `h|_U`. -/
  locality : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (h ω)).internal U z w = F (restrictTo U (h ω)) z w
  /-- III. Weyl scaling: a.s. `e^{ξ f}·D_h = D_{h+f}` for every continuous `f`. -/
  weyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
      weylScale (xiGamma γ) f (D (h ω)) z w = ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w))
  /-- IV. Coordinate change: for fixed `r > 0`, `z`, a.s.
  `D_h(ru + z, rv + z) = D_{h(r·+z) + Q log r}(u, v)` for all `u, v`. -/
  coord : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (h ω)).1 (r * u + z, r * v + z) =
        (D (addConst (affineComp r z (h ω)) (Q γ * Real.log r))).1 (u, v)

/-- `(u, v) ↦ (r u, r v)` -/
def scaleArgs (r : ℝ) : C(ℂ × ℂ, ℂ × ℂ) :=
  ⟨fun p => ((r : ℂ) * p.1, (r : ℂ) * p.2), by fun_prop⟩

/-- Axiom V for the scaling constants `c` (GM l. 440–447; GM_A D-3: a weak metric is a predicate
on `(D, 𝔠)`) -/
def TightAcrossScales (ξ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) : Prop :=
  (∀ r, 0 < r → 0 < c r) ∧
  (∃ Λ : ℝ, 1 < Λ ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ r : ℝ, 0 < r →
      Λ⁻¹ * δ ^ Λ ≤ c (δ * r) / c r ∧ c (δ * r) / c r ≤ Λ * δ ^ (-Λ)) ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsWholePlaneGFF h P →
    let X : ℝ → Ω → C(ℂ × ℂ, ℝ) := fun r ω =>
      ((c r)⁻¹ * Real.exp (-ξ * circleAvg (h ω) r 0)) • (D (h ω)).1.comp (scaleArgs r)
    IsTightMeasureSet {μ | ∃ r : ℝ, 0 < r ∧ μ = P.map (X r)} ∧
    ∀ μ : ProbabilityMeasure C(ℂ × ℂ, ℝ),
      μ ∈ closure {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
        ∃ r : ℝ, 0 < r ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)} →
      ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d

/-- A **weak γ-LQG metric** with scaling constants `c` (GM l. 431–452): Axioms I–III as for a
strong metric, IV′ translation invariance, V tightness across scales. "D is a weak γ-LQG metric"
is `∃ c, IsWeakLQGMetric γ D c`. -/
structure IsWeakLQGMetric (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) : Prop where
  measurable : Measurable D
  length : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLength
  locality : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (ℂ → ℂ → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (h ω)).internal U z w = F (restrictTo U (h ω)) z w
  weyl : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), ∀ z w : ℂ,
      weylScale (xiGamma γ) f (D (h ω)) z w = ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w))
  /-- IV′. Translation invariance: for fixed `z`, a.s. `D_{h(·+z)} = D_h(·+z, ·+z)`. -/
  translation : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)
  /-- V. Tightness across scales. -/
  tightness : TightAcrossScales (xiGamma γ) D c

end LQGMetric
