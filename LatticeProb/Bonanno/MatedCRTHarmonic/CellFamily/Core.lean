/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.Core at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects

/-!
# Reusable deterministic and finite-union lemmas for the scaled-grid estimate

This module isolates two formal steps in the corrected scaled-grid estimate proof: a graph-disconnection witness remains
valid when the forbidden vertex set is enlarged, and a finite intersection of environment events has probability at
least one minus the sum of their failure probabilities.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellFamily

/-- Enlarging a forbidden vertex set preserves graph disconnection. -/
theorem disconnects_mono {V E : Type*} {G : LFMultigraph V E} {U U' S T : Set V}
    (hUU' : U ⊆ U') (h : G.Disconnects U S T) : G.Disconnects U' S T := by
  intro a ha b hb w
  obtain ⟨y, hyw, hyU⟩ := h a ha b hb w
  exact ⟨y, hyw, hUU' hyU⟩

/-- Finite union bound, expressed as a lower bound for the probability that all events hold. -/
theorem measure_finset_iInter_ge_one_sub_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    μ (⋂ i ∈ s, E i) ≥ 1 - ∑ i ∈ s, μ (E i)ᶜ := by
  let good : Set Ω := ⋂ i ∈ s, E i
  let bad : Set Ω := ⋃ i ∈ s, (E i)ᶜ
  have hgood : MeasurableSet good := s.measurableSet_biInter hE
  have hbad : MeasurableSet bad := s.measurableSet_biUnion fun i hi => (hE i hi).compl
  have hcompl : goodᶜ = bad := by
    ext ω
    simp [good, bad]
  have hbad_le : μ bad ≤ ∑ i ∈ s, μ (E i)ᶜ := measure_biUnion_finset_le s _
  have hsum : μ good + μ bad = 1 := by
    rw [← hcompl]
    simpa using measure_add_measure_compl (μ := μ) hgood
  have hle : 1 ≤ (∑ i ∈ s, μ (E i)ᶜ) + μ good := by
    calc
      1 = μ good + μ bad := hsum.symm
      _ = μ bad + μ good := add_comm _ _
      _ ≤ (∑ i ∈ s, μ (E i)ᶜ) + μ good := add_le_add_left hbad_le _
      _ = _ := by rw [add_comm (∑ i ∈ s, μ (E i)ᶜ)]
  have hsub : 1 - (∑ i ∈ s, μ (E i)ᶜ) ≤ μ good :=
    (tsub_le_iff_left).2 (by simpa [add_comm] using hle)
  simpa [good] using hsub

/-- Finite union bound when each failure event has the same upper probability bound. -/
theorem measure_finset_iInter_ge_one_sub_card_mul {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (E : ι → Set Ω) {δ : ℝ≥0∞}
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hbad : ∀ i ∈ s, μ (E i)ᶜ ≤ δ) :
    μ (⋂ i ∈ s, E i) ≥ 1 - (s.card : ℝ≥0∞) * δ := by
  have h := measure_finset_iInter_ge_one_sub_sum μ s E hE
  have hs : ∑ i ∈ s, μ (E i)ᶜ ≤ (s.card : ℝ≥0∞) * δ := by
    calc
      ∑ i ∈ s, μ (E i)ᶜ ≤ ∑ i ∈ s, δ := Finset.sum_le_sum hbad
      _ = (s.card : ℝ≥0∞) * δ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hsub : 1 - (s.card : ℝ≥0∞) * δ ≤ 1 - ∑ i ∈ s, μ (E i)ᶜ := by
    exact tsub_le_tsub_left hs 1
  exact le_trans hsub h

end MatedCRTHarmonic.CellFamily
