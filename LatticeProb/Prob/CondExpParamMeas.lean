import Mathlib

noncomputable section
open MeasureTheory ProbabilityTheory

/-- The kernel integral of a jointly measurable integrand against the
conditional-expectation kernel is jointly measurable in the parameter. -/
theorem LatticeProb.measurable_integral_condExpKernel_param
    {Ω ΩB : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (r : Ω × ΩB → ℝ)
    (hr : @Measurable (Ω × ΩB) ℝ (@Prod.instMeasurableSpace Ω ΩB mΩ mB) _ r) :
    @Measurable (Ω × ΩB) ℝ (@Prod.instMeasurableSpace Ω ΩB mΩ mB) _
      (fun p => ∫ β, r (p.1, β) ∂(condExpKernel (mΩ := mB) PB 𝒢 p.2)) := by
  let K0 : @Kernel ΩB ΩB 𝒢 mB := condExpKernel (mΩ := mB) PB 𝒢
  have h2 : @Measurable (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) 𝒢 Prod.snd :=
    (measurable_snd : @Measurable (Ω × ΩB) ΩB
      (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB Prod.snd).mono le_rfl h𝒢
  let K : @Kernel (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB :=
    (Kernel.comap K0 Prod.snd h2 : @Kernel (Ω × ΩB) ΩB
      (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
  have hpair : @Measurable ((Ω × ΩB) × ΩB) (Ω × ΩB)
      (@Prod.instMeasurableSpace (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
      (@Prod.instMeasurableSpace Ω ΩB mΩ mB) (fun q => (q.1.1, q.2)) :=
    (measurable_fst.fst).prodMk measurable_snd
  have hsm : @StronglyMeasurable ((Ω × ΩB) × ΩB) ℝ _
      (@Prod.instMeasurableSpace (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
      (fun q => r (q.1.1, q.2)) :=
    hr.stronglyMeasurable.comp_measurable hpair
  exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := K) hsm).measurable
