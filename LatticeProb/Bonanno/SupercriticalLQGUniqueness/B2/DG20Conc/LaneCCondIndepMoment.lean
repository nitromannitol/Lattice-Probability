/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondIndepMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCoarseGaussianMoment
import Mathlib.Probability.ConditionalExpectation

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_conditional_lintegral_eq_of_indep
    {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m₁] f)
    (hInd : Indep m₁ m₂ P) (hInt : Integrable f P)
    (hpos : ∀ ω, 0 ≤ f ω) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, ENNReal.ofReal (f x) ∂(condExpKernel P m₂ ω)) =
        ∫⁻ x, ENNReal.ofReal (f x) ∂P := by
  have hconst : P[f | m₂] =ᵐ[P] fun _ => ∫ x, f x ∂P :=
    condExp_indep_eq hm₁ hm₂ hf hInd
  have hkernel : P[f | m₂] =ᵐ[P]
      fun ω => ∫ x, f x ∂(condExpKernel P m₂ ω) :=
    condExp_ae_eq_integral_condExpKernel hm₂ hInt
  filter_upwards [hconst, hkernel, hInt.condExpKernel_ae] with ω hc hk hi
  have heq : (∫ x, f x ∂(condExpKernel P m₂ ω)) = ∫ x, f x ∂P :=
    hk.symm.trans hc
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂(condExpKernel P m₂ ω)) =
        ENNReal.ofReal (∫ x, f x ∂(condExpKernel P m₂ ω)) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hpos)).symm
    _ = ENNReal.ofReal (∫ x, f x ∂P) := congrArg _ heq
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hpos)

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 



theorem laneC_conditional_coarse_phi_exp_moment_of_indep
    {Ω : Type*} {m₂ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hm₂ : m₂ ≤ mΩ) (K : ℕ) (b : ℤ × ℤ) (a : ℝ)
    (hInd : Indep (MeasurableSpace.comap
      (phiMN W P 0 K (T20.dyCenter K b)) (inferInstance : MeasurableSpace ℝ))
      m₂ P) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, ENNReal.ofReal
        (Real.exp (a * phiMN W P 0 K (T20.dyCenter K b) x))
        ∂(condExpKernel P m₂ ω)) ≤
      ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) * a ^ 2 / 2)) := by
  let X : Ω → ℝ := phiMN W P 0 K (T20.dyCenter K b)
  have hXm : @Measurable Ω ℝ mΩ _ X :=
    (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  obtain ⟨v, _, hLaw⟩ := hasLaw_phiMN hW K (T20.dyCenter K b)
  have hInt : Integrable (fun ω => Real.exp (a * X ω)) P :=
    hLaw.integrable_comp (f := fun x => Real.exp (a * x))
      (integrable_exp_mul_gaussianReal a)
  let mφ : MeasurableSpace Ω :=
    MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)
  have hmφ : mφ ≤ mΩ := hXm.comap_le
  have hXφ : @Measurable Ω ℝ mφ _ X := comap_measurable X
  have hf : StronglyMeasurable[mφ] (fun ω => Real.exp (a * X ω)) :=
    (hXφ.const_mul a).exp.stronglyMeasurable
  have hcond := laneC_conditional_lintegral_eq_of_indep (mΩ := mΩ) P hmφ hm₂ hf
    hInd hInt (fun _ => (Real.exp_pos _).le)
  filter_upwards [hcond] with ω hω
  exact hω.le.trans (@laneC_coarse_phi_exp_moment Ω mΩ P W hW K b a)

end SupercriticalLQGUniqueness.B2.DG20Conc
