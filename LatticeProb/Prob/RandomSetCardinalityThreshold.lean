import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Data.ENat.SuccOrder

/-! # Cardinalities of random sets from threshold events -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- If every finite lower threshold of an extended-natural-valued function is
null measurable, then the function is almost everywhere measurable. -/
theorem aemeasurable_enat_of_nullMeasurable_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℕ∞)
    (h : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℕ∞) ≤ f ω} μ) :
    AEMeasurable f μ := by
  have hm : @Measurable (NullMeasurableSpace Ω μ) ℕ∞ _ _ f := by
    apply ENat.measurable_iff.mpr
    intro n
    have heq : f ⁻¹' {(n : ℕ∞)} =
        {ω | (n : ℕ∞) ≤ f ω} \ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ f ω} := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_sdiff, mem_ofPred_eq]
      simp only [not_le, Nat.cast_add, Nat.cast_one, ENat.lt_natCast_add_one_iff]
      exact ⟨fun he => ⟨he.ge, he.le⟩, fun he => le_antisymm he.2 he.1⟩
    change NullMeasurableSet (f ⁻¹' {(n : ℕ∞)}) μ
    rw [heq]
    exact (h n).diff (h (n + 1))
  exact (show NullMeasurable f μ from hm).aemeasurable

/-- Null-measurable finite cardinality thresholds give a measurable version of
the exact cardinality, with infinite sets assigned the value zero. -/
theorem aemeasurable_ncard_of_nullMeasurable_encard_thresholds
    {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Ω → Set α)
    (h : ∀ n : ℕ, NullMeasurableSet {ω | (n : ℕ∞) ≤ (S ω).encard} μ) :
    AEMeasurable (fun ω => (S ω).ncard) μ := by
  have hf := aemeasurable_enat_of_nullMeasurable_thresholds μ (fun ω => (S ω).encard) h
  exact Measurable.comp_aemeasurable (Measurable.of_discrete : Measurable ENat.toNat) hf

end LatticeProb
