import LatticeProb.Prob.AdaptedStandardBorel

/-! # Determination under conditional independence -/

open MeasureTheory ProbabilityTheory MeasurableSpace Filter Set

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {G V C : MeasurableSpace Ω}

/-- If `C` is determined by `G ⊔ V` and is conditionally independent of `V` given `G`,
then `C` is determined by `G`, in the sense of almost-sure event equality. -/
theorem AELeSigma.of_condIndepEv_sup [IsProbabilityMeasure μ]
    (hG : G ≤ mΩ) (hV : V ≤ mΩ) (hC : C ≤ mΩ)
    (h : CondIndepEv G V C μ) (hdet : AELeSigma C (G ⊔ V) μ) :
    AELeSigma C G μ := by
  let : MeasurableSpace Ω := mΩ
  intro a ha
  obtain ⟨d, hd, had⟩ := hdet a ha
  have hd' : MeasurableSet[V ⊔ G] d := by rwa [sup_comm]
  have hmarkov := condExp_sup_eq_of_condIndepEv hG hV hC h ha
  have heq : μ⟦a | V ⊔ G⟧ =ᵐ[μ] μ⟦d | V ⊔ G⟧ :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (μ := μ) had)
  have hself : μ⟦d | V ⊔ G⟧ = d.indicator (fun _ => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable (sup_le hV hG)
      (stronglyMeasurable_const.indicator hd')
      ((integrable_const (1 : ℝ)).indicator ((sup_le hV hG) _ hd'))
  have hmeas : Measurable[G] (μ⟦a | G⟧) := stronglyMeasurable_condExp.measurable
  have he : d.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] μ⟦a | G⟧ := by
    rw [← hself]
    exact heq.symm.trans hmarkov
  refine ⟨(μ⟦a | G⟧) ⁻¹' {1}, hmeas (measurableSet_singleton 1), had.trans ?_⟩
  filter_upwards [he] with x hx
  show (x ∈ d) = (x ∈ (μ⟦a | G⟧) ⁻¹' {1})
  by_cases hxd : x ∈ d
  · rw [indicator_of_mem hxd] at hx
    exact propext ⟨fun _ => hx.symm, fun _ => hxd⟩
  · rw [indicator_of_notMem hxd] at hx
    refine propext ⟨fun h' => absurd h' hxd, fun h' => ?_⟩
    have h1 : (μ⟦a | G⟧) x = 1 := h'
    rw [← hx] at h1
    exact absurd h1 zero_ne_one

/-- A standard Borel random variable determined jointly by `X` and `Z` and conditionally
independent of `Z` given `X` is almost surely a measurable function of `X`. -/
theorem aeDeterminedBy_of_condIndepEv_of_joint [IsProbabilityMeasure μ]
    {α β γ : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {X : Ω → α} {Z : Ω → β} {Y : Ω → γ}
    (hX : Measurable[mΩ] X) (hZ : Measurable[mΩ] Z) (hY : Measurable[mΩ] Y)
    (h : CondIndepEv (mα.comap X) (mβ.comap Z) (mγ.comap Y) μ)
    (hdet : AELeSigma (mγ.comap Y) (mα.comap X ⊔ mβ.comap Z) μ) :
    @AEDeterminedBy Ω mΩ α γ mα mγ Y X μ :=
  aeDeterminedBy_of_aeDeterminedSigma
    (AELeSigma.of_condIndepEv_sup hX.comap_le hZ.comap_le hY.comap_le h hdet)

end LatticeProb
