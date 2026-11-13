/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.InputsFullPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsJoint
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointRadiusGap

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos.Inputs

 




def DGFFWhiteNoiseFullPathComparison : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ),
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∃ J : ∀ n : ℕ, Measure (EuclideanSpace ℝ (DGFFSite n) × Ω),
        (∀ n, IsProbabilityMeasure (J n)) ∧
        (∀ n, (J n).map Prod.fst = boxDGFF n) ∧
        (∀ n, (J n).map Prod.snd = P) ∧
        ∀ δ : ℝ, 0 < δ →
          Tendsto (fun n => J n {v |
            ∃ (N : ℕ) (p : ℕ → DGFFSite n),
              latticeRadius (p 0).1 ≤ dgffInnerRadius n ∧
              dgffOuterRadius n ≤ latticeRadius (p N).1 ∧
              (∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1) ∧
              dgffPathCost n (ξ : ℝ) v.1
                (List.ofFn fun i : Fin (N + 1) => p i) ≤
                (2 : ℝ) ^ ((1 + δ) * (n : ℝ)) *
                  (crossLenIn (ξ : ℝ) (fun x => phiMN W P 0 n x v.2)
                    upperAnnulus upperAnnulusInner upperAnnulusOuter).toReal})
            atTop (𝓝 1)

end SupercriticalLQGUniqueness.B2.QPos.Inputs
