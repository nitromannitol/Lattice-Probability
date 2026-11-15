import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! # Rational subsegments of a continuous curve -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A nondegenerate continuous curve segment is the closure of the union of
its subsegments with rational endpoints strictly inside the original interval. -/
theorem closure_iUnion_rational_subsegment_image
    {X : Type*} [TopologicalSpace X] [T2Space X] (f : ℝ → X)
    (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    closure (⋃ (p : ℚ) (q : ℚ) (_ : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b),
      f '' Icc (p : ℝ) (q : ℝ)) = f '' Icc a b := by
  let D : Set X := ⋃ (p : ℚ) (q : ℚ)
    (_ : a < (p : ℝ) ∧ (p : ℝ) < (q : ℝ) ∧ (q : ℝ) < b),
      f '' Icc (p : ℝ) (q : ℝ)
  have hsub : D ⊆ f '' Icc a b := by
    rintro x hx
    simp only [D, mem_iUnion] at hx
    obtain ⟨p, q, ⟨hap, hpq, hqb⟩, t, ⟨hpt, htq⟩, rfl⟩ := hx
    exact ⟨t, ⟨hap.le.trans hpt, htq.trans hqb.le⟩, rfl⟩
  have hopen : f '' Ioo a b ⊆ D := by
    rintro x ⟨t, ⟨hat, htb⟩, rfl⟩
    obtain ⟨p, hap, hpt⟩ := exists_rat_btwn hat
    obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
    have hpq : (p : ℝ) < (q : ℝ) := hpt.trans htq
    simp only [D, mem_iUnion]
    exact ⟨p, q, ⟨hap, hpq, hqb⟩, t, ⟨hpt.le, htq.le⟩, rfl⟩
  change closure D = f '' Icc a b
  apply Subset.antisymm
  · exact closure_minimal hsub (isCompact_Icc.image hf).isClosed
  · calc
      f '' Icc a b = f '' closure (Ioo a b) := by rw [closure_Ioo hab.ne]
      _ ⊆ closure (f '' Ioo a b) := image_closure_subset_closure_image hf
      _ ⊆ closure D := closure_mono hopen

end LatticeProb
