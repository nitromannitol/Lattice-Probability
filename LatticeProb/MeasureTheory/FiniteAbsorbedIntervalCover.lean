import LatticeProb.MeasureTheory.FiniteLongIntervals
import LatticeProb.MeasureTheory.FiniteIntervalCoverage

/-! # Finite covers of absorbed intervals -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A bounded interval absorbing all intersecting intervals of one positive length
has a finite closed cover by those intervals. -/
theorem finite_cover_of_absorbed_intervals
    {ι : Type*} (a b l r ℓ : ℝ) (A B : ι → ℝ)
    (hal : a ≤ l) (hlr : l < r) (hrb : r ≤ b) (hℓ : 0 < ℓ)
    (hpos : ∀ i, A i < B i)
    (hdis : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hcover : volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0)
    (habsorb : ∀ i, (Ioo l r ∩ Ioo (A i) (B i)).Nonempty →
      Ioo (A i) (B i) ⊆ Ioo l r ∧ B i - A i = ℓ) :
    let S := {i | (Ioo l r ∩ Ioo (A i) (B i)).Nonempty}
    S.Finite ∧
      (∀ i ∈ S, l ≤ A i ∧ B i ≤ r ∧ B i - A i = ℓ) ∧
      volume (Ioo l r \ ⋃ i : S, Ioo (A i) (B i)) = 0 ∧
      Icc l r ⊆ ⋃ i : S, Icc (A i) (B i) := by
  let S : Set ι := {i | (Ioo l r ∩ Ioo (A i) (B i)).Nonempty}
  have hS : ∀ i ∈ S, l ≤ A i ∧ B i ≤ r ∧ B i - A i = ℓ := by
    intro i hi
    obtain ⟨hsub, hlen⟩ := habsorb i hi
    obtain ⟨hleft, hright⟩ := (Ioo_subset_Ioo_iff (hpos i)).mp hsub
    exact ⟨hleft, hright, hlen⟩
  have hfin : S.Finite := by
    have hf := finite_long_disjoint_intervals l r ℓ A B S hℓ
      (fun i hi => ⟨(hS i hi).1, (hS i hi).2.1⟩)
      (fun i _ j _ hij => hdis hij)
    apply hf.subset
    intro i hi
    exact ⟨hi, le_of_eq (hS i hi).2.2.symm⟩
  let : Finite S := hfin.to_subtype
  have hnull : volume (Ioo l r \ ⋃ i : S, Ioo (A i) (B i)) = 0 := by
    apply measure_mono_null _ hcover
    intro x hx
    refine ⟨⟨lt_of_le_of_lt hal hx.1.1, lt_of_lt_of_le hx.1.2 hrb⟩, ?_⟩
    intro hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    have hiS : i ∈ S := ⟨x, hx.1, hi⟩
    exact hx.2 (mem_iUnion.mpr ⟨⟨i, hiS⟩, hi⟩)
  exact ⟨hfin, hS, hnull, closed_interval_subset_of_ae_finite_interval_cover l r
    (fun i : S => A i) (fun i : S => B i) hlr hnull⟩

end LatticeProb
