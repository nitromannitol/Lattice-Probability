/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Iface.Limit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 








set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn restrictTo addFun IsGFFPlusCont IsGFFPlusBddCont)

namespace SupercriticalLQGUniqueness.B2.Iface

 
def PLThm19Limit : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∀ D : DistC → LSCMetric,
          SubseqLimit ξ m ε D →
          ∀ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            IsPfeWeakMetric ξ D c →
            (∃ C : ℝ, 0 < C ∧ ∀ r : Set.Ioi (0 : ℝ),
              C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) ≤ c r ∧
              (c r : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q)) ∧
            IsWeakLQGMetric ξ Q D

 
end SupercriticalLQGUniqueness.B2.Iface
