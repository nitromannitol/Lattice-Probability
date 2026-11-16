import LatticeProb.LQG.CollarOpenContainment
import LatticeProb.Topology.CompactOpenCofinal

/-! # Support-gated collar field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric

namespace LatticeProb.LQG

/-- The centered pairing of any test is observable on the event that its
support lies in the collar. The pairing is set to zero outside this event. -/
theorem measurable_support_indicator_centered_pairing_of_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (ψ : ℕ → TestC)
    {p : ℝ} (hp : 0 < p) (k : ℕ) (φ : TestC) :
    let E := {ω | tsupport (φ : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
    Measurable[MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k)
      inferInstance] (E.indicator (fun ω => h ω φ - (∫ z, φ z) * h ω (ψ k))) := by
  classical
  let : MeasurableSpace Ω := MeasurableSpace.comap
    (collarFieldCode h K localDenseTest ψ hp k) inferInstance
  obtain ⟨V, hVo, hV⟩ := LatticeProb.Topology.exists_sequence_open_compact_enclosures ℂ
  let E : Set Ω := {ω | tsupport (φ : ℂ → ℝ) ⊆
    thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  let F : ℕ → Set Ω := fun n => {ω | tsupport (φ : ℂ → ℝ) ⊆ V n ∧
    V n ⊆ thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)}
  let f : Ω → ℝ := fun ω => h ω φ - (∫ z, φ z) * h ω (ψ k)
  have hF : ∀ n, MeasurableSet (F n) := by
    intro n
    by_cases hn : tsupport (φ : ℂ → ℝ) ⊆ V n
    · have heq : F n = {ω | V n ⊆
          thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ)} := by
        ext ω
        simp [F, hn]
      rw [heq]
      exact measurableSet_open_subset_collar_of_collarFieldCode h K ψ hp k ⟨V n, hVo n⟩
    · have heq : F n = ∅ := by ext ω; simp [F, hn]
      rw [heq]
      exact MeasurableSet.empty
  have hFU : E = ⋃ n, F n := by
    ext ω
    simp only [mem_iUnion, F, E, mem_ofPred_eq]
    constructor
    · intro hs
      obtain ⟨n, hn, hn'⟩ := hV _ φ.hasCompactSupport.isCompact _ isOpen_thickening hs
      exact ⟨n, hn, hn'⟩
    · rintro ⟨n, hn, hn'⟩
      exact hn.trans hn'
  have hpiece : ∀ n, Measurable ((F n).indicator f) := by
    intro n
    by_cases hn : tsupport (φ : ℂ → ℝ) ⊆ V n
    · exact measurable_indicator_centered_pairing_of_collarFieldCode h K ψ hp k
        ⟨V n, hVo n⟩ (F n) (hF n) (fun ω hω => hω.2) φ hn
    · have heq : F n = ∅ := by ext ω; simp [F, hn]
      simp [heq, f]
  have hE : MeasurableSet E := hFU ▸ MeasurableSet.iUnion hF
  change Measurable (E.indicator f)
  intro B hB
  have hpre : E ∩ f ⁻¹' B = ⋃ n, (F n ∩ ((F n).indicator f) ⁻¹' B) := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_iUnion]
    rw [hFU]
    simp only [mem_iUnion]
    constructor
    · rintro ⟨⟨n, hn⟩, hf⟩
      exact ⟨n, hn, by simpa only [indicator_of_mem hn] using hf⟩
    · rintro ⟨n, hn, hf⟩
      exact ⟨⟨n, hn⟩, by simpa only [indicator_of_mem hn] using hf⟩
  have hmeas : MeasurableSet (E ∩ f ⁻¹' B) := by
    rw [hpre]
    exact MeasurableSet.iUnion fun n => (hF n).inter (hpiece n hB)
  by_cases h0 : (0 : ℝ) ∈ B
  · have heq : E.indicator f ⁻¹' B = (E ∩ f ⁻¹' B) ∪ Eᶜ := by
      ext ω
      by_cases hw : ω ∈ E <;> simp [hw, h0]
    rw [heq]
    exact hmeas.union hE.compl
  · have heq : E.indicator f ⁻¹' B = E ∩ f ⁻¹' B := by
      ext ω
      by_cases hw : ω ∈ E <;> simp [hw, h0]
    rw [heq]
    exact hmeas

end LatticeProb.LQG
