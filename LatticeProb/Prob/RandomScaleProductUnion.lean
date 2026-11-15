import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Probability
import Mathlib.MeasureTheory.Measure.Prod

/-! # Finite random unions under product laws -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- Under a product law, the probability of a bad event at a field-dependent
finite index is bounded by a cardinality tail and a finite union bound. -/
theorem prod_measure_exists_mem_finset_le {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : α → Finset ι) (B : ι → Set β) (p : ℝ≥0∞) (N : ℕ)
    (hB : ∀ i, ν (B i) ≤ p)
    (hE : MeasurableSet {z : α × β | ∃ i ∈ K z.1, z.2 ∈ B i})
    (hgood : MeasurableSet {x | (K x).card ≤ N}) :
    (μ.prod ν) {z : α × β | ∃ i ∈ K z.1, z.2 ∈ B i} ≤
      μ {x | N < (K x).card} + (N : ℝ≥0∞) * p := by
  classical
  let E : Set (α × β) := {z | ∃ i ∈ K z.1, z.2 ∈ B i}
  let G : Set α := {x | (K x).card ≤ N}
  have hsub : E ⊆ (Gᶜ ×ˢ univ) ∪ (E ∩ (G ×ˢ univ)) := by
    intro z hz
    by_cases hzG : z.1 ∈ G
    · exact Or.inr ⟨hz, hzG, mem_univ _⟩
    · exact Or.inl ⟨hzG, mem_univ _⟩
  have hsection (x : α) :
      ν (Prod.mk x ⁻¹' (E ∩ (G ×ˢ univ))) ≤ (N : ℝ≥0∞) * p := by
    by_cases hx : x ∈ G
    · have hle := MatedCRTHarmonic.GMS4.finite_union_measure_le_card_mul ν (K x) B p
        (fun i _ => hB i)
      have hsub' : Prod.mk x ⁻¹' (E ∩ (G ×ˢ univ)) ⊆ ⋃ i ∈ K x, B i := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := hy.1
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hyi⟩⟩
      calc
        ν (Prod.mk x ⁻¹' (E ∩ (G ×ˢ univ))) ≤ ν (⋃ i ∈ K x, B i) := measure_mono hsub'
        _ ≤ ((K x).card : ℝ≥0∞) * p := hle
        _ ≤ (N : ℝ≥0∞) * p := by
          gcongr
          exact_mod_cast hx
    · have : Prod.mk x ⁻¹' (E ∩ (G ×ˢ univ)) = ∅ := by
        ext y
        simp [G, hx]
      simp [this]
  have hbound : (μ.prod ν) (E ∩ (G ×ˢ univ)) ≤ (N : ℝ≥0∞) * p := by
    rw [Measure.prod_apply (hE.inter (hgood.prod MeasurableSet.univ))]
    calc
      (∫⁻ x, ν (Prod.mk x ⁻¹' (E ∩ (G ×ˢ univ))) ∂μ) ≤
          ∫⁻ _, (N : ℝ≥0∞) * p ∂μ := lintegral_mono hsection
      _ = (N : ℝ≥0∞) * p := by simp
  calc
    (μ.prod ν) E ≤ (μ.prod ν) ((Gᶜ ×ˢ univ) ∪ (E ∩ (G ×ˢ univ))) := measure_mono hsub
    _ ≤ (μ.prod ν) (Gᶜ ×ˢ univ) + (μ.prod ν) (E ∩ (G ×ˢ univ)) := measure_union_le _ _
    _ ≤ μ {x | N < (K x).card} + (N : ℝ≥0∞) * p := by
      have hfirst : (μ.prod ν) (Gᶜ ×ˢ univ) = μ {x | N < (K x).card} := by
        rw [Measure.prod_prod, measure_univ, mul_one]
        congr 1
        ext x
        simp only [G, mem_compl_iff, mem_ofPred_eq, not_le]
      rw [hfirst]
      exact add_le_add le_rfl hbound

end LatticeProb
