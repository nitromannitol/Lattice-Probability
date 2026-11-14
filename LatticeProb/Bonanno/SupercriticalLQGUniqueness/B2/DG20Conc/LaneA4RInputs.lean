/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3Defs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.HitExponent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4Exponent

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 
def laneCNormalizedAroundProductStar
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ q : ℝ) (n K : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
      ((lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) x)⁻¹) ^ q *
    laneA3Around P W hW Qψ ξ n K b x ^ q
    ∂(condExpKernel P (laneFineStar Qψ W P K n) ω)

 
def LaneC2StarAt.{u} : Prop :=
  ∀ (Qψ : PsiParams), Qψ.ε₀ < 1 / 100 → ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ),
  IsLFPPExponent ξ Q → ∀ p₀ : ℝ, 0 < p₀ → p₀ < 2⁻¹ →
  J1FixedPAt.{u} Qψ (ξ : ℝ) p₀ → LaneB3Defs.B3FixedPSubaddTails.{u} Qψ ξ Q p₀ →
  ∀ C q η : ℝ, 0 < C → 0 < q → 0 < η →
  ∃ K₀ : ℕ,
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ),
      K₀ ≤ K → K ≤ n →
      LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p₀) ≤
        Real.exp (C * Real.sqrt (K : ℝ)) →
      (∫⁻ ω, ((laneSourceIdx Qψ K).sup (fun b =>
          laneCNormalizedAroundProductStar P W hW Qψ (ξ : ℝ) q n K b ω)) ^
            (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((2 : ℝ) ^
          ((q ^ 2 * (ξ : ℝ) ^ 2 / 2 - q * (ξ : ℝ) * Q + η) * K))

 
def LaneFineStarIndepCoarse.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
    IsWhiteNoise P W → ∀ (Q : PsiParams) (K n : ℕ), K ≤ n →
    Indep (MeasurableSpace.comap (fun ω x => phiMN W P 0 K x ω)
              (inferInstance : MeasurableSpace (ℂ → ℝ)) ⊔
            MeasurableSpace.comap (fun ω x => psiMN Q W P 0 K x ω)
              (inferInstance : MeasurableSpace (ℂ → ℝ)))
      (laneFineStar Q W P K n) P

end SupercriticalLQGUniqueness.B2.DG20Conc
