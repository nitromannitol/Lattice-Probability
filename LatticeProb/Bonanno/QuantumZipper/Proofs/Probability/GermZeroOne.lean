/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.GermZeroOne at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: eLpNorm_one_eq_lintegral_enorm takes the measurability argument and eLpNorm_le_eLpNorm_of_exponent_le no longer does (three proof lines).
   Declarations, examples and checks that the copied results do not use are omitted. -/
/-
Blueprint node A8: germ 0-1 toolkit.

(a) Blumenthal 0-1 law for Brownian motion.
(b) Independent-join lemma for decreasing σ-algebras with trivial intersections.
(c) Brownian scaling mixing.

The key analytic tool is the `L²` (hence `L¹`) convergence of conditional expectations onto a
decreasing sequence of σ-algebras with trivial intersection, proved through monotone orthogonal
projections (on the orthogonal complements), avoiding backward martingale convergence.
-/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GermZeroOne

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-! ### Decreasing orthogonal projections converge -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

end Hilbert

/-! ### Conditional expectations onto decreasing σ-algebras with trivial intersection -/

section Mixing

variable {P : Measure Ω} [IsProbabilityMeasure P]

end Mixing

/-! ### (b) The independent-join lemma -/

section Join

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Rectangles `a ∩ b` with `a ∈ m₁`, `b ∈ m₂`. -/
def rectSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m₁] a ∧ MeasurableSet[m₂] b ∧ s = a ∩ b}

lemma isPiSystem_rectSets (m₁ m₂ : MeasurableSpace Ω) : IsPiSystem (rectSets m₁ m₂) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
  refine ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', ?_⟩
  ext x; simp only [Set.mem_inter_iff]; tauto

lemma sup_eq_generateFrom_rectSets (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom (rectSets m₁ m₂) := by
  apply le_antisymm
  · refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨a, Set.univ, ha, MeasurableSet.univ, (Set.inter_univ a).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, b, MeasurableSet.univ, hb, (Set.univ_inter b).symm⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact @MeasurableSet.inter Ω (m₁ ⊔ m₂) a b ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) a ha)
      ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) b hb)

end Join

/-! ### (a) Blumenthal 0-1 law -/

section Brownian

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
lemma measurable_pi_of {α δ : Type*} {mα : MeasurableSpace α} {g : α → δ → ℝ}
    (hg : ∀ a, Measurable[mα] fun x => g x a) : Measurable[mα] g :=
  measurable_pi_iff.2 hg

/-! ### (c) Brownian scaling mixing -/

/-- Two pre-Brownian motions with measurable coordinates have the same path law. -/
lemma map_path_eq_of_isPreBrownianReal {B B' : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hB' : IsPreBrownianReal B' P) (hBm : ∀ t, Measurable (B t))
    (hBm' : ∀ t, Measurable (B' t)) :
    P.map (fun ω t => B t ω) = P.map (fun ω t => B' t ω) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hproj : ∀ {C : ℝ≥0 → Ω → ℝ}, IsPreBrownianReal C P → (∀ t, Measurable (C t)) →
      IsProjectiveLimit (P.map (fun ω t => C t ω)) BrownianReal.projectiveFamily := by
    intro C hC hCm I
    rw [Measure.map_map (Finset.measurable_restrict I) (measurable_pi_of hCm)]
    exact (hC.hasLaw I).map_eq
  haveI : ∀ I, IsFiniteMeasure (BrownianReal.projectiveFamily I) := fun I => by
    rw [← (hB.hasLaw I).map_eq]; infer_instance
  exact (hproj hB hBm).unique (hproj hB' hBm')

end Brownian

end GermZeroOne
end QuantumZipper
