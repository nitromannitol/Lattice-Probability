import Mathlib

noncomputable section
open MeasureTheory ProbabilityTheory

/-- **Joint measurability of a conditional expectation in a parameter.**

For a probability measure `PB` on a standard Borel space `ΩB`, a sub-σ-algebra
`𝒢 ≤ mB`, and a function `r : Ω × ΩB → ℝ` that is jointly measurable and whose
sections `β ↦ r (ω, β)` are `PB`-integrable, there is a jointly measurable
version `g` of the conditional expectation: for every parameter `ω` the section
`β ↦ g (ω, β)` agrees `PB`-almost everywhere with `PB[fun β => r (ω, β) | 𝒢]`.

The version is the kernel integral against the conditional-expectation kernel,
`g p = ∫ β, r (p.1, β) ∂(condExpKernel PB 𝒢 p.2)`, which is jointly measurable
because the kernel integral of a jointly measurable integrand is measurable in
the parameter.  The ambient σ-algebra of `ΩB` is named explicitly (`mB`) since
`𝒢` is itself a local instance of `MeasurableSpace ΩB`. -/
theorem LatticeProb.exists_measurable_condExp_param
    {Ω ΩB : Type*} [mΩ : MeasurableSpace Ω] [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (r : Ω × ΩB → ℝ)
    (hr : @Measurable (Ω × ΩB) ℝ (@Prod.instMeasurableSpace Ω ΩB mΩ mB) _ r)
    (hint : ∀ ω, Integrable (fun β => r (ω, β)) PB) :
    ∃ g : Ω × ΩB → ℝ,
      @Measurable (Ω × ΩB) ℝ (@Prod.instMeasurableSpace Ω ΩB mΩ mB) _ g ∧
      ∀ ω, (fun β => g (ω, β)) =ᵐ[PB] PB[fun β => r (ω, β) | 𝒢] := by
  let K0 : @Kernel ΩB ΩB 𝒢 mB := condExpKernel (mΩ := mB) PB 𝒢
  have h2 : @Measurable (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) 𝒢 Prod.snd :=
    (measurable_snd : @Measurable (Ω × ΩB) ΩB
      (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB Prod.snd).mono le_rfl h𝒢
  let K : @Kernel (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB :=
    (Kernel.comap K0 Prod.snd h2 : @Kernel (Ω × ΩB) ΩB
      (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
  refine ⟨fun p => ∫ β, r (p.1, β) ∂(K p), ?_, ?_⟩
  · have hpair : @Measurable ((Ω × ΩB) × ΩB) (Ω × ΩB)
        (@Prod.instMeasurableSpace (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
        (@Prod.instMeasurableSpace Ω ΩB mΩ mB) (fun q => (q.1.1, q.2)) :=
      (measurable_fst.fst).prodMk measurable_snd
    have hsm : @StronglyMeasurable ((Ω × ΩB) × ΩB) ℝ _
        (@Prod.instMeasurableSpace (Ω × ΩB) ΩB (@Prod.instMeasurableSpace Ω ΩB mΩ mB) mB)
        (fun q => r (q.1.1, q.2)) :=
      hr.stronglyMeasurable.comp_measurable hpair
    exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := K) hsm).measurable
  · intro ω
    have h := condExp_ae_eq_integral_condExpKernel (μ := PB) (m := 𝒢) (mΩ := mB) h𝒢 (hint ω)
    simpa [K, K0, Kernel.comap_apply] using h.symm
