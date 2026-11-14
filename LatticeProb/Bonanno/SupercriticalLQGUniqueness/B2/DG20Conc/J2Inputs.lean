/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2Inputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep2
import Mathlib.Probability.Kernel.Condexp

 

























set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace J2Defs

variable {Ω : Type*} [MeasurableSpace Ω]

 
def fineBlocks (Qψ : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ)
    (ω : Ω) : T20B.nearIdx K → T20B.dyD → ℝ :=
  fun b => T20B.restrD (fun x => T20B.blkKn Qψ W P K n b.1 x ω)

 

def condLogLen (ξ : ℝ) (Qψ : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K : ℕ)
    (v : T20B.nearIdx K → T20B.dyD → ℝ) : ℝ :=
  ∫ ω', T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
    o.elim (T20B.restrD (fun x => psiMN Qψ W P 0 K x ω')) v) ∂P

 
def efronDiff (ξ : ℝ) (Qψ : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ)
    (b : T20B.nearIdx K) (z : Ω × Ω) : ℝ :=
  condLogLen ξ Qψ W P K
      (Function.update (fineBlocks Qψ W P K n z.1) b (fineBlocks Qψ W P K n z.2 b)) -
    condLogLen ξ Qψ W P K (fineBlocks Qψ W P K n z.1)

theorem nearIdx_nonempty (K : ℕ) : (T20B.nearIdx K).Nonempty :=
  ⟨(0, 0), by simp [T20B.nearIdx]⟩

end J2Defs

namespace J2Inputs

open J2Defs

 

def fineKernel {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (Qψ : PsiParams)
    (W : WNSpace → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P] (K n : ℕ) :
    @ProbabilityTheory.Kernel Ω Ω (MeasurableSpace.comap (fun ω z => psiMN Qψ W P K n z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ))) _ :=
  condExpKernel P (MeasurableSpace.comap (fun ω z => psiMN Qψ W P K n z ω)
    (inferInstance : MeasurableSpace (ℂ → ℝ)))

 
def EfronFactorsAt (ξ : ℝ) (Qψ : PsiParams) {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (K n : ℕ) (A B : ℝ) : Prop :=
  ∃ Y : ℤ × ℤ → Ω → ℝ≥0∞, (∀ b, Measurable (Y b)) ∧
    (∀ b : T20B.nearIdx K, ∀ᵐ z ∂(P.prod P),
      ENNReal.ofReal (efronDiff ξ Qψ W P K n b z) ≤
        ∫⁻ x, Y b.1 x ∂(fineKernel Qψ W P K n z.1)) ∧
    (∫⁻ ω, (∑ b ∈ T20B.nearIdx K, ∫⁻ x, Y b x ∂(fineKernel Qψ W P K n ω)) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal A) ∧
    (∫⁻ ω, ((T20B.nearIdx K).sup' (nearIdx_nonempty K)
        (fun b => ∫⁻ x, Y b x ∂(fineKernel Qψ W P K n ω))) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal B)

 


def EfronFactors (ξ : Ioi (0 : ℝ)) (Qψ : PsiParams) (p : ℝ) : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ N₁ N₂ a : ℝ, ∃ K₀ : ℕ, 0 < a ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
    ∀ K n : ℕ, K₀ ≤ K → K ≤ n →
      LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤ Real.exp (C * Real.sqrt (K : ℝ)) →
      EfronFactorsAt (ξ : ℝ) Qψ P W K n
        ((N₁ * K * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3))) ^ 2)
        ((N₂ * (2 : ℝ) ^ (-(a * K))) ^ 2)

end J2Inputs

end SupercriticalLQGUniqueness.B2.DG20Conc
