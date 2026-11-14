import LatticeProb.Prob.CondIndepEvChain

/-!
# Markov form of conditional independence from a kernel

Let `X ≤ P` be sub-σ-algebras and let `Φ` be a random variable.  Suppose that the law of `Φ`
given `P` is described by a probability kernel `κ` evaluated at an `X`-measurable random variable
`ξ`: for every `a ∈ P` and every measurable `β`,
`∫_a 1_{Φ ∈ β} = ∫_a κ(ξ, β)`.  Then `σ(Φ)` and `P` are conditionally independent given `X`
(`LatticeProb.condIndepEv_of_kernel_markov`).  This is the form in which the Markov property at a
stopping time (the future given the stopped past depends only on the state at the stopping time)
enters the conditional independence criteria of `Prob/CondIndepEvChain.lean`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory MeasurableSpace Set

namespace LatticeProb

variable {Ω : Type*} {X P : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Conditional independence from a Markov kernel.**  If, for every event `a` of `P` and every
measurable `β`, `∫_a 1_{Φ ∈ β} dμ = ∫_a κ(ξ, β) dμ` with `ξ` measurable for `X ≤ P` and `κ` a
probability kernel, then `σ(Φ) ⟂ P | X`. -/
theorem condIndepEv_of_kernel_markov [IsProbabilityMeasure μ] (hXP : X ≤ P) (hP : P ≤ mΩ)
    {Y W : Type*} [MeasurableSpace Y] [MeasurableSpace W] {ξ : Ω → Y} (hξ : Measurable[X] ξ)
    {Φ : Ω → W} (hΦ : Measurable Φ) (κ : Kernel Y W) [IsMarkovKernel κ]
    (h : ∀ a, MeasurableSet[P] a → ∀ β : Set W, MeasurableSet β →
      ∫ x in a, (Φ ⁻¹' β).indicator (fun _ => (1 : ℝ)) x ∂μ = ∫ x in a, (κ (ξ x) β).toReal ∂μ) :
    CondIndepEv X (MeasurableSpace.comap Φ inferInstance) P μ := by
  have hXm : X ≤ mΩ := hXP.trans hP
  refine condIndepEv_of_condExp_sup_eq hXm hΦ.comap_le hP fun a ha => ?_
  obtain ⟨β, hβ, rfl⟩ := ha
  have hgX : Measurable[X] (fun x => (κ (ξ x) β).toReal) :=
    ENNReal.measurable_toReal.comp ((Kernel.measurable_coe κ hβ).comp hξ)
  have hgm : Measurable (fun x => (κ (ξ x) β).toReal) := hgX.mono hXm le_rfl
  have hgb : ∀ x, ‖(κ (ξ x) β).toReal‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : κ (ξ x) β ≤ 1)
  have hgi : Integrable (fun x => (κ (ξ x) β).toReal) μ :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ hgb)
  have e1 : (fun x => (κ (ξ x) β).toReal) =ᵐ[μ] μ⟦Φ ⁻¹' β | P⟧ :=
    ae_eq_condExp_of_forall_setIntegral_eq hP (integrable_indOne (hΦ hβ))
      (fun s _ _ => hgi.integrableOn) (fun s hs _ => (h s hs β hβ).symm)
      (hgX.stronglyMeasurable.mono hXP).aestronglyMeasurable
  have e2 : μ⟦Φ ⁻¹' β | X⟧ =ᵐ[μ] fun x => (κ (ξ x) β).toReal := by
    have t1 : μ[μ⟦Φ ⁻¹' β | P⟧ | X] =ᵐ[μ] μ⟦Φ ⁻¹' β | X⟧ := condExp_condExp_of_le hXP hP
    have t2 : μ[μ⟦Φ ⁻¹' β | P⟧ | X] =ᵐ[μ] μ[fun x => (κ (ξ x) β).toReal | X] :=
      condExp_congr_ae e1.symm
    have t3 : μ[fun x => (κ (ξ x) β).toReal | X] = fun x => (κ (ξ x) β).toReal :=
      condExp_of_stronglyMeasurable hXm hgX.stronglyMeasurable hgi
    rw [t3] at t2
    exact t1.symm.trans t2
  rw [sup_eq_left.2 hXP]
  exact e1.symm.trans e2.symm

end LatticeProb
