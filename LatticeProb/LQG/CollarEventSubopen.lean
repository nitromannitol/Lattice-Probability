import LatticeProb.LQG.CollarSubopenCenteredPhase

/-! # Event-local observations inside a random collar -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace LQGMetric SmallGammaGeodesics

namespace LatticeProb.LQG

/-- On a measurable event, a centered supported pairing is an observation of
    the collar code when the open set is contained in the collar on that event. -/
theorem measurable_indicator_centered_pairing_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ) (E : Set Ω)
    (hE : MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] E)
    (hO : ∀ ω ∈ E, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (φ : TestC) (hφ : tsupport (φ : ℂ → ℝ) ⊆ O) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (E.indicator (fun ω => h ω φ - (∫ z, φ z) * h ω (ψ k))) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hm := measurable_centered_pairing_of_collarFieldCode
    (fun ω : E => h ω) (fun ω : E => K ω) ψ hp k O
    (fun ω => hO ω ω.property) φ hφ
  have hcode : collarFieldCode (fun ω : E => h ω) (fun ω : E => K ω)
      localDenseTest ψ hp k = (collarFieldCode h K localDenseTest ψ hp k) ∘ Subtype.val := by
    funext ω
    simp only [collarFieldCode, Function.comp_apply]
    apply Prod.ext rfl
    apply Prod.ext ?_ rfl
    funext i
    simp only [Set.indicator]
  rw [hcode, ← MeasurableSpace.comap_comp] at hm
  have hm' : Measurable (fun ω : E => h ω φ - (∫ z, φ z) * h ω (ψ k)) := hm
  apply measurable_of_restrict_of_restrict_compl hE
  · convert hm' using 1
    funext ω
    exact Set.indicator_of_mem ω.property _
  · convert (measurable_const : Measurable (fun _ : (Eᶜ : Set Ω) => (0 : ℝ))) using 1
    funext ω
    exact Set.indicator_of_notMem ω.property _

/-- The phase of a supported unit-integral test is observable on a measurable
    event where its open support region lies inside the collar. -/
theorem measurable_indicator_phase_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (O : Opens ℂ) (E : Set Ω)
    (hE : MeasurableSet[MeasurableSpace.comap
      (collarFieldCode h K localDenseTest ψ hp k) inferInstance] E)
    (hO : ∀ ω ∈ E, (O : Set ℂ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    (ρ : TestC) (hρ : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ z, ρ z = 1) :
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (E.indicator (fun ω => toIcoMod hp 0 (h ω ρ))) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  have hm := measurable_phase_of_collarFieldCode
    (fun ω : E => h ω) (fun ω : E => K ω) ψ hp k O
    (fun ω => hO ω ω.property) ρ hρ hρ1
  have hcode : collarFieldCode (fun ω : E => h ω) (fun ω : E => K ω)
      localDenseTest ψ hp k = (collarFieldCode h K localDenseTest ψ hp k) ∘ Subtype.val := by
    funext ω
    simp only [collarFieldCode, Function.comp_apply]
    apply Prod.ext rfl
    apply Prod.ext ?_ rfl
    funext i
    simp only [Set.indicator]
  rw [hcode, ← MeasurableSpace.comap_comp] at hm
  have hm' : Measurable (fun ω : E => toIcoMod hp 0 (h ω ρ)) := hm
  apply measurable_of_restrict_of_restrict_compl hE
  · convert hm' using 1
    funext ω
    exact Set.indicator_of_mem ω.property _
  · convert (measurable_const : Measurable (fun _ : (Eᶜ : Set Ω) => (0 : ℝ))) using 1
    funext ω
    exact Set.indicator_of_notMem ω.property _

end LatticeProb.LQG
