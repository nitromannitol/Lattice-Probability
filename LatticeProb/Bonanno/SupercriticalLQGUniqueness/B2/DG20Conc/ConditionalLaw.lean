/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.ConditionalLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.BlockReconstruction
import Mathlib.Probability.Kernel.CondDistrib

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 



theorem condDistrib_eq_const_of_indepFun
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → β} {Y : α → γ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hX hY
  rw [Measure.compProd_const]
  exact hXY.map_prod_eq_prod_map_map hX hY

 


theorem condExp_eq_integral_of_indepFun
    {α β γ : Type*} [MeasurableSpace α] [mβ : MeasurableSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → β} {Y : α → γ} (hX : Measurable X)
    (hY : AEMeasurable Y μ) (hXY : IndepFun X Y μ)
    {f : β × γ → ℝ} (hf : StronglyMeasurable f)
    (hint : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ∂(μ.map Y) := by
  have hdist : ∀ᵐ a ∂μ, condDistrib Y X μ (X a) = μ.map Y := by
    have h := condDistrib_eq_const_of_indepFun hX.aemeasurable hY hXY
    simpa only [Kernel.const_apply] using
      (MeasureTheory.ae_of_ae_map hX.aemeasurable h)
  filter_upwards [condExp_prod_ae_eq_integral_condDistrib hX hY hf hint,
    hdist] with a ha hd
  simpa only [hd] using ha

 


theorem condVar_le_of_indepFun
    {α β γ : Type*} [MeasurableSpace α] [mβ : MeasurableSpace β]
    [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {X : α → β} {Y : α → γ} (hX : Measurable X)
    (hY : AEMeasurable Y μ) (hXY : IndepFun X Y μ)
    {f : β × γ → ℝ} (hf : StronglyMeasurable f)
    (hL2 : MemLp (fun a => f (X a, Y a)) 2 μ)
    {C : ℝ} (hvar : ∀ᵐ a ∂μ, MemLp (fun y => f (X a, y)) 2 (μ.map Y) ∧
      Var[fun y => f (X a, y); μ.map Y] ≤ C) :
    Var[fun a => f (X a, Y a); μ | mβ.comap X] ≤ᵐ[μ]
      fun _ => C := by
  have hdist : ∀ᵐ a ∂μ,
      condDistrib Y X μ (X a) = μ.map Y := by
    have h := condDistrib_eq_const_of_indepFun hX.aemeasurable hY hXY
    have h' := MeasureTheory.ae_of_ae_map hX.aemeasurable h
    simpa only [Kernel.const_apply] using h'
  have hE : μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ∂(μ.map Y) := by
    filter_upwards [condExp_prod_ae_eq_integral_condDistrib hX hY hf
      (hL2.integrable one_le_two), hdist] with a ha hd
    simpa only [hd] using ha
  have hE2 : μ[(fun a => f (X a, Y a)) ^ 2 | mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ^ 2 ∂(μ.map Y) := by
    filter_upwards [condExp_prod_ae_eq_integral_condDistrib hX hY (hf.pow 2)
      hL2.integrable_sq, hdist] with a ha hd
    change μ[fun a => f (X a, Y a) ^ 2 | mβ.comap X] a =
      ∫ y, f (X a, y) ^ 2 ∂(μ.map Y)
    simpa only [hd, Pi.pow_apply] using ha
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hX.comap_le hL2,
    hE, hE2, hvar] with a ha ha1 ha2 hv
  rw [ha]
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [ha1, ha2]
  rw [variance_eq_sub hv.1] at hv
  exact hv.2

end SupercriticalLQGUniqueness.B2.DG20Conc

