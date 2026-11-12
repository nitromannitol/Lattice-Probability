/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3E

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: conditional independence through laws and monotone limits (R3)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 4 (T:1268–1278: "letting `W` increase to `V` and `W'` increase to `ℂ ∖ V̄`"). Each stage
`k` of the proof lives on its own limit coupling `ρ_k`; the conditional independence obtained
there only involves the field and the first limit metric, whose joint law does not depend on `k`
(`map_coupling_fst_eq`). Tools (standard measure theory, own elementary proofs):

* `condExp_comp_map` — `ρ[f ∘ π | π⁻¹G] = (π_*ρ)[f | G] ∘ π` a.s.;
* `condIndepEv_map` — conditional independence of pulled-back σ-algebras passes to the law;
* `condIndepEv_iSup_of_monotone` — monotone limits of conditionally independent pairs on a
  standard Borel space (mathlib's `condIndep_iSup_of_monotone`, through
  `condIndep_iff_condIndepEv`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L217

/-- conditional expectations given a pulled-back σ-algebra are computed on the law -/
theorem condExp_comp_map {Ω T : Type*} {G : MeasurableSpace T} [mΩ : MeasurableSpace Ω]
    [mT : MeasurableSpace T] {ρ : Measure Ω} [IsFiniteMeasure ρ] {π : Ω → T} (hπ : Measurable π)
    (hG : G ≤ mT) {f : T → ℝ} (hf : Integrable f (ρ.map π)) :
    ρ[f ∘ π | G.comap π] =ᵐ[ρ] (ρ.map π)[f | G] ∘ π := by
  have hm : G.comap π ≤ mΩ := (MeasurableSpace.comap_mono hG).trans hπ.comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hf.comp_measurable hπ)
    (fun s _ _ => (integrable_condExp.comp_measurable hπ).integrableOn) ?_
    (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable π)).aestronglyMeasurable).symm
  rintro _ ⟨t, ht, rfl⟩ _
  have ht' : MeasurableSet t := hG t ht
  calc ∫ x in π ⁻¹' t, ((ρ.map π)[f | G] ∘ π) x ∂ρ
      = ∫ y in t, (ρ.map π)[f | G] y ∂(ρ.map π) :=
        (setIntegral_map ht' integrable_condExp.aestronglyMeasurable hπ.aemeasurable).symm
    _ = ∫ y in t, f y ∂(ρ.map π) := setIntegral_condExp hG hf ht
    _ = ∫ x in π ⁻¹' t, (f ∘ π) x ∂ρ :=
        setIntegral_map ht' hf.aestronglyMeasurable hπ.aemeasurable

/-- **conditional independence passes to the law** -/
theorem condIndepEv_map {Ω T : Type*} {G A B : MeasurableSpace T} [mΩ : MeasurableSpace Ω]
    [mT : MeasurableSpace T] {ρ : Measure Ω} [IsProbabilityMeasure ρ] {π : Ω → T}
    (hπ : Measurable π) (hG : G ≤ mT) (hA : A ≤ mT) (hB : B ≤ mT)
    (h : CondIndepEv (G.comap π) (A.comap π) (B.comap π) ρ) : CondIndepEv G A B (ρ.map π) := by
  have : IsProbabilityMeasure (ρ.map π) :=
    (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
  intro a b ha hb
  have ha' := hA a ha
  have hb' := hB b hb
  have ind : ∀ s : Set T, (s.indicator fun _ => (1 : ℝ)) ∘ π =
      (π ⁻¹' s).indicator fun _ => (1 : ℝ) := fun s => by
    funext x; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  have e : ∀ s : Set T, MeasurableSet s → ρ⟦π ⁻¹' s | G.comap π⟧ =ᵐ[ρ]
      (ρ.map π)⟦s | G⟧ ∘ π := fun s hs => by
    rw [← ind s]
    exact condExp_comp_map hπ hG (integrable_indOne hs)
  have H := h _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have H' : ∀ᵐ x ∂ρ, ((ρ.map π)⟦a ∩ b | G⟧ ∘ π) x =
      (((ρ.map π)⟦a | G⟧ * (ρ.map π)⟦b | G⟧) ∘ π) x := by
    filter_upwards [H, e _ (ha'.inter hb'), e _ ha', e _ hb'] with x hx e1 e2 e3
    simp only [Function.comp, Pi.mul_apply, Set.preimage_inter] at hx e1 e2 e3 ⊢
    rw [← e1, ← e2, ← e3, hx]
  have hm1 : Measurable ((ρ.map π)⟦a ∩ b | G⟧) :=
    (stronglyMeasurable_condExp.measurable).mono hG le_rfl
  have hm2 : Measurable ((ρ.map π)⟦a | G⟧ * (ρ.map π)⟦b | G⟧) :=
    ((stronglyMeasurable_condExp.measurable).mono hG le_rfl).mul
      ((stronglyMeasurable_condExp.measurable).mono hG le_rfl)
  exact (ae_map_iff hπ.aemeasurable (measurableSet_eq_fun hm1 hm2)).2 H'

/-- **monotone limits of conditionally independent pairs** (standard Borel space) -/
theorem condIndepEv_iSup_of_monotone {Ω : Type*} {G : MeasurableSpace Ω}
    {A B : ℕ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hG : G ≤ mΩ) (hAm : ∀ k, A k ≤ mΩ) (hBm : ∀ k, B k ≤ mΩ) (hA : Monotone A)
    (hB : Monotone B) (h : ∀ k, CondIndepEv G (A k) (B k) μ) :
    CondIndepEv G (⨆ k, A k) (⨆ k, B k) μ := by
  have hAB : ∀ j k, CondIndepEv G (A k) (B j) μ := fun j k => by
    rcases le_total k j with hkj | hjk
    · exact (h j).mono (hA hkj) le_rfl
    · exact (h k).mono le_rfl (hB hjk)
  have h1 : ∀ j, CondIndep G (⨆ k, A k) (B j) hG μ := fun j =>
    condIndep_iSup_of_monotone (fun k => (condIndep_iff_condIndepEv hG (hAm k) (hBm j)).2
      (hAB j k)) hAm (hBm j) hA
  have h2 : CondIndep G (⨆ j, B j) (⨆ k, A k) hG μ :=
    condIndep_iSup_of_monotone (fun j => (h1 j).symm) hBm (iSup_le hAm) hB
  exact (condIndep_iff_condIndepEv hG (iSup_le hAm) (iSup_le hBm)).1 h2.symm

end L217

end LQGMetric.DFGPS
