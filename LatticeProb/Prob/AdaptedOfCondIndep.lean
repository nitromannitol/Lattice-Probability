/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.AELeSigma

/-!
# Variables determined by the past and by a smaller σ-algebra with an independent complement

Let `G ≤ U ≤ P` be σ-algebras and `V` a σ-algebra that is conditionally independent of the past
`P` given `G`.  A variable that is, up to null sets, both `P`-measurable and `U ⊔ V`-measurable is
`U`-measurable up to null sets (`AELeSigma.of_condIndepEv_past`).  Indeed, the conditional
expectation of an event of `P` given `V ⊔ U` is its conditional expectation given `U`, by the
Markov form of conditional independence; an event of `P` that is also in `U ⊔ V` is therefore
equal to a conditional expectation given `U`, which is `U`-measurable.

For `ℝ≥0∞`- and `ℝ≥0`-valued variables the conclusion is turned into an almost sure equality with a
`U`-measurable function (`AELeSigma.exists_measurable_ae_eq`,
`exists_measurable_ae_eq_of_condIndepEv_past`), by the monotone-class induction principle for
measurable `ℝ≥0∞`-valued functions applied to the σ-algebra `aeClosure U μ`.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace Filter Set
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {G U V P C : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **A variable of the past that is determined by `U ⊔ V` is determined by `U`.**  Let
`G ≤ U ≤ P ≤ mΩ` and let `V ≤ mΩ` be conditionally independent of `P` given `G`.  If every event of
`C` agrees almost surely with an event of `P` and with an event of `U ⊔ V`, then every event of `C`
agrees almost surely with an event of `U`. -/
theorem AELeSigma.of_condIndepEv_past [IsProbabilityMeasure μ]
    (hGU : G ≤ U) (hUP : U ≤ P) (hP : P ≤ mΩ) (hV : V ≤ mΩ) (h : CondIndepEv G V P μ)
    (hCP : AELeSigma C P μ) (hCUV : AELeSigma C (U ⊔ V) μ) : AELeSigma C U μ := by
  have hU : U ≤ mΩ := hUP.trans hP
  have hG : G ≤ mΩ := hGU.trans hU
  have h1 : CondIndepEv G V (P ⊔ U) μ := by rwa [sup_eq_left.2 hUP]
  have h2 : CondIndepEv (U ⊔ G) V P μ := CondIndepEv.weak_union hG hV hP hU h1
  rw [sup_eq_left.2 hGU] at h2
  intro a ha
  obtain ⟨a₁, ha₁, h₁⟩ := hCP a ha
  obtain ⟨a₂, ha₂, h₂⟩ := hCUV a ha
  have hVU : V ⊔ U ≤ mΩ := sup_le hV hU
  have ha₂' : MeasurableSet[V ⊔ U] a₂ := by
    rw [sup_comm]
    exact ha₂
  have e1 : μ⟦a₁ | V ⊔ U⟧ =ᵐ[μ] μ⟦a₁ | U⟧ := condExp_sup_eq_of_condIndepEv hU hV hP h2 ha₁
  have e2 : μ⟦a₁ | V ⊔ U⟧ =ᵐ[μ] μ⟦a₂ | V ⊔ U⟧ :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (h₁.symm.trans h₂))
  have e3 : μ⟦a₂ | V ⊔ U⟧ = a₂.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable hVU (stronglyMeasurable_const.indicator ha₂')
      ((integrable_const (1 : ℝ)).indicator (hVU _ ha₂'))
  have hmeas : Measurable[U] (μ⟦a₁ | U⟧) := stronglyMeasurable_condExp.measurable
  have e : a₂.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] μ⟦a₁ | U⟧ := by
    rw [← e3]
    exact e2.symm.trans e1
  refine ⟨(μ⟦a₁ | U⟧) ⁻¹' {1}, hmeas (measurableSet_singleton 1), h₂.trans ?_⟩
  filter_upwards [e] with x hx
  show (x ∈ a₂) = (x ∈ (μ⟦a₁ | U⟧) ⁻¹' {1})
  by_cases hxa : x ∈ a₂
  · rw [indicator_of_mem hxa] at hx
    exact propext ⟨fun _ => hx.symm, fun _ => hxa⟩
  · rw [indicator_of_notMem hxa] at hx
    refine propext ⟨fun h' => absurd h' hxa, fun h' => ?_⟩
    have h1' : (μ⟦a₁ | U⟧) x = 1 := h'
    rw [← hx] at h1'
    exact absurd h1' zero_ne_one

/-- A function that is measurable for the σ-algebra of events agreeing almost surely with events of
`U` agrees almost surely with a `U`-measurable function (`ℝ≥0∞`-valued case). -/
theorem exists_measurable_ae_eq_of_measurable_aeClosure {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeClosure U μ] f) :
    ∃ g : Ω → ℝ≥0∞, Measurable[U] g ∧ f =ᵐ[μ] g := by
  refine @Measurable.ennreal_induction Ω (aeClosure U μ)
    (fun f => ∃ g : Ω → ℝ≥0∞, Measurable[U] g ∧ f =ᵐ[μ] g) ?_ ?_ ?_ f hf
  · intro c s hs
    obtain ⟨s', hs', hss'⟩ := hs
    refine ⟨s'.indicator fun _ => c, measurable_const.indicator hs', ?_⟩
    exact indicator_ae_eq_of_ae_eq_set hss'
  · rintro f₁ f₂ - - - ⟨g₁, hg₁, e₁⟩ ⟨g₂, hg₂, e₂⟩
    exact ⟨g₁ + g₂, hg₁.add hg₂, e₁.add e₂⟩
  · intro f' _ _ hP
    choose g hg he using hP
    refine ⟨fun x => ⨆ n, g n x, Measurable.iSup hg, ?_⟩
    have : ∀ᵐ x ∂μ, ∀ n, f' n x = g n x := ae_all_iff.2 he
    filter_upwards [this] with x hx
    simp only [hx]

/-- If `comap f` is contained in `U` up to null sets, the `ℝ≥0∞`-valued variable `f` agrees almost
surely with a `U`-measurable function. -/
theorem AELeSigma.exists_measurable_ae_eq {f : Ω → ℝ≥0∞}
    (h : AELeSigma (MeasurableSpace.comap f inferInstance) U μ) :
    ∃ g : Ω → ℝ≥0∞, Measurable[U] g ∧ f =ᵐ[μ] g :=
  exists_measurable_ae_eq_of_measurable_aeClosure
    (Measurable.of_comap_le (aeLeSigma_iff_le.1 h))

/-- If `comap f` is contained in `U` up to null sets, the `ℝ≥0`-valued variable `f` agrees almost
surely with a `U`-measurable function. -/
theorem AELeSigma.exists_measurable_ae_eq_nnreal {f : Ω → ℝ≥0}
    (h : AELeSigma (MeasurableSpace.comap f inferInstance) U μ) :
    ∃ g : Ω → ℝ≥0, Measurable[U] g ∧ f =ᵐ[μ] g := by
  have hle : MeasurableSpace.comap (fun x => (f x : ℝ≥0∞)) inferInstance ≤
      MeasurableSpace.comap f inferInstance := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨(fun r : ℝ≥0 => (r : ℝ≥0∞)) ⁻¹' t, (by fun_prop : Measurable fun r : ℝ≥0 => (r : ℝ≥0∞)) ht, rfl⟩
  obtain ⟨g, hg, e⟩ := AELeSigma.exists_measurable_ae_eq
    ((aeLeSigma_iff_le (μ := μ)).2 (le_trans hle (aeLeSigma_iff_le.1 h)))
  refine ⟨fun x => (g x).toNNReal, hg.ennreal_toNNReal, ?_⟩
  filter_upwards [e] with x hx
  simp [hx.symm]

/-- **Adaptedness from conditional independence.**  Let `G ≤ U ≤ P`, and let `V` be conditionally
independent of `P` given `G`.  An `ℝ≥0`-valued variable whose events agree almost surely with events
of `P` and with events of `U ⊔ V` agrees almost surely with a `U`-measurable function. -/
theorem exists_measurable_ae_eq_of_condIndepEv_past [IsProbabilityMeasure μ]
    {Y : Ω → ℝ≥0}
    (hGU : G ≤ U) (hUP : U ≤ P) (hP : P ≤ mΩ) (hV : V ≤ mΩ) (h : CondIndepEv G V P μ)
    (hYP : AELeSigma (MeasurableSpace.comap Y inferInstance) P μ)
    (hYUV : AELeSigma (MeasurableSpace.comap Y inferInstance) (U ⊔ V) μ) :
    ∃ g : Ω → ℝ≥0, Measurable[U] g ∧ Y =ᵐ[μ] g :=
  AELeSigma.exists_measurable_ae_eq_nnreal
    (AELeSigma.of_condIndepEv_past hGU hUP hP hV h hYP hYUV)

end LatticeProb
