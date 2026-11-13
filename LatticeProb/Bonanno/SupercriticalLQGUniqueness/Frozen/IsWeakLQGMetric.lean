/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsTwoSidedTight

/-! Scratch freeze split of SLUField.lean:143. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- `D` is a **weak LQG metric with parameter `ξ`** and distance exponent `Q` (DG Definition 1.12,
l. 565–581): a measurable map `h ↦ D_h` from `𝒟'(ℂ)` to the lower semicontinuous metrics on `ℂ`
satisfying Axioms I–III of DG Definition 1.7 (l. 443–453) whenever `h` is a whole-plane GFF plus
a continuous function, Axiom IV′ for the same `h`, and Axiom V′ for the whole-plane GFF. -/
def IsWeakLQGMetric (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
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
    (h : Ω → DistC), IsGFFPlusCont h P → ∀ z : ℂ, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (translateDist z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)) ∧
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ a : Set.Ioi (0 : ℝ) → Ω → ℝ,
      (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω)) →
      ∀ A : EuclideanAnnulus,
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
            acrossDist (D (h ω)) (A.dilate r r.2)) ∧
        IsTwoSidedTight P (fun (r : Set.Ioi (0 : ℝ)) ω =>
          ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * a r ω))) *
            aroundDist (D (h ω)) (A.dilate r r.2)))
end SupercriticalLQGUniqueness
