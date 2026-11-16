import LatticeProb.LQG.LocalCountablePathEvent

/-! # Gluing local field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace LQGMetric
open SupercriticalConformalCovariance.TV

namespace LatticeProb.LQG

/-- A supported mean-zero pairing can be read on a countable union of events
from the local countable field coordinates available on each event. -/
theorem measurable_indicator_pairing_of_localCountablePaths {Ω : Type}
    [MeasurableSpace Ω] (h : Ω → DistC) (O : ℕ → Opens ℂ)
    (ρ : ℕ → TestC) (hρO : ∀ n, tsupport (ρ n : ℂ → ℝ) ⊆ O n)
    (hρ1 : ∀ n, ∫ z, ρ n z = 1) (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n))
    (hpath : ∀ n j, Measurable ((E n).indicator
      (fun ω => localCountablePath (O n) (ρ n) (hρO n) (hρ1 n) (h ω) j)))
    (φ : TestC) (hφO : ∀ n, E n ≠ ∅ → tsupport (φ : ℂ → ℝ) ⊆ O n)
    (hφ0 : ∫ z, φ z = 0) :
    Measurable ((⋃ n, E n).indicator (fun ω => h ω φ)) := by
  classical
  let f : Ω → ℝ := fun ω => h ω φ
  have hpiece : ∀ n, Measurable ((E n).indicator f) := by
    intro n
    by_cases hn : E n = ∅
    · simp [hn]
    · exact measurable_indicator_pairing_of_localCountablePath h (O n) (ρ n)
        (hρO n) (hρ1 n) (E n) (hE n) (hpath n) φ (hφO n hn) hφ0
  let U : Set Ω := ⋃ n, E n
  have hU : MeasurableSet U := MeasurableSet.iUnion hE
  change Measurable (U.indicator f)
  intro B hB
  have heq : U ∩ f ⁻¹' B =
      ⋃ n, (E n ∩ ((E n).indicator f) ⁻¹' B) := by
    ext ω
    simp only [U, mem_inter_iff, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨⟨n, hn⟩, hf⟩
      exact ⟨n, hn, by simpa only [indicator_of_mem hn] using hf⟩
    · rintro ⟨n, hn, hf⟩
      exact ⟨⟨n, hn⟩, by simpa only [indicator_of_mem hn] using hf⟩
  have hm : MeasurableSet (U ∩ f ⁻¹' B) := by
    rw [heq]
    exact MeasurableSet.iUnion fun n => (hE n).inter (hpiece n hB)
  by_cases h0 : (0 : ℝ) ∈ B
  · have heq' : U.indicator f ⁻¹' B =
        (U ∩ f ⁻¹' B) ∪ Uᶜ := by
      ext ω
      by_cases hw : ω ∈ U <;> simp [hw, h0]
    rw [heq']
    exact hm.union hU.compl
  · have heq' : U.indicator f ⁻¹' B =
        U ∩ f ⁻¹' B := by
      ext ω
      by_cases hw : ω ∈ U <;> simp [hw, h0]
    rw [heq']
    exact hm

end LatticeProb.LQG
