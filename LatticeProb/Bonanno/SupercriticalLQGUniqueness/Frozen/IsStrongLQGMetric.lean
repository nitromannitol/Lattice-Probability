/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `IsStrongLQGMetric`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- `D` is a **(strong) LQG metric with parameter `ξ`** and distance exponent `Q` (DG Definition 1.7,
`def-metric0`, l. 440–460): a measurable map `h ↦ D_h` from `𝒟'(ℂ)` to the lower semicontinuous
metrics on `ℂ` such that, whenever `h` is a whole-plane GFF plus a continuous function (l. 443),
* I (l. 445): a.s. `(ℂ, D_h)` is a length space;
* II (l. 446–447): for each deterministic open `U`, a.s. the internal metric `D_h(·, ·; U)` is a
  measurable function of `h|_U`;
* III (l. 448–453): a.s. `e^{ξ f} · D_h = D_{h + f}` for every continuous `f`;
* IV (l. 454–457): for each fixed deterministic `r > 0` and `z`, a.s.
  `D_h(r u + z, r v + z) = D_{h(r · + z) + Q log r}(u, v)` for all `u, v`;
* V (l. 458): for each deterministic connected open `U` and disjoint deterministic compact
  connected non-singleton `K₁, K₂ ⊆ U`, a.s. `D_h(K₁, K₂; U) < ∞`.
Conjuncts 1–4 are byte-identical to the first four conjuncts of `IsWeakLQGMetric` (same readings
G1, E1, D1, D2, C1, C2, K1/K2, H1/H2/A1); `IsWeakLQGMetric` is not used as a field. -/
def IsStrongLQGMetric (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  Measurable D ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
      ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
        ∀ᵐ ω ∂P, (D (h ω)).internal (U : Set ℂ) = F (restrictTo U (h ω))) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), weylScale (ξ : ℝ) f (D (h ω)) = (D (addFun (h ω) f)).1) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ (r : Set.Ioi (0 : ℝ)) (z : ℂ), ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (h ω)).1 ((r : ℝ) • u + z, (r : ℝ) • v + z) =
        (D (addConst (scaleTranslateDist r z (h ω)) (Q * Real.log (r : ℝ)))).1 (u, v)) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ, IsConnected (U : Set ℂ) →
      ∀ K₁ K₂ : Set ℂ, IsCompact K₁ → IsCompact K₂ → IsConnected K₁ → IsConnected K₂ →
        K₁.Nontrivial → K₂.Nontrivial → K₁ ⊆ U → K₂ ⊆ U → Disjoint K₁ K₂ →
        ∀ᵐ ω ∂P, (D (h ω)).internalSetDist (U : Set ℂ)
          (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞)

end SupercriticalLQGUniqueness
