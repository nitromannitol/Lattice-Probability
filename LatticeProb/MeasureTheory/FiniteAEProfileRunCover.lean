import LatticeProb.MeasureTheory.BoundedAEProfileRun
import LatticeProb.MeasureTheory.FiniteLongIntervals
import LatticeProb.MeasureTheory.FiniteIntervalCoverage

/-! # Finite interval covers of almost-everywhere constant runs -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Intervals carrying their lengths as an almost-everywhere profile induce a finite
cover of the maximal constant run containing any strictly interior anchor. -/
theorem exists_finite_ae_profile_run_cover
    {ι : Type*} (a b u : ℝ) (A B : ι → ℝ) (f : ℝ → ℝ)
    (hbounds : ∀ i, a ≤ A i ∧ A i < B i ∧ B i ≤ b)
    (hdis : Pairwise fun i j => Disjoint (Ioo (A i) (B i)) (Ioo (A j) (B j)))
    (hcover : volume (Ioo a b \ ⋃ i, Ioo (A i) (B i)) = 0)
    (hprofile : ∀ i, ∀ᵐ t ∂(volume.restrict (Ioo (A i) (B i))),
      f t = B i - A i)
    (i₀ : ι) (hu : u ∈ Ioo (A i₀) (B i₀)) :
    ∃ l r : ℝ, a ≤ l ∧ l < u ∧ u < r ∧ r ≤ b ∧
      let S := {i | (Ioo l r ∩ Ioo (A i) (B i)).Nonempty}
      S.Finite ∧ i₀ ∈ S ∧
      (∀ i ∈ S, l ≤ A i ∧ B i ≤ r ∧ B i - A i = B i₀ - A i₀) ∧
      volume (Ioo l r \ ⋃ i : S, Ioo (A i) (B i)) = 0 ∧
      Icc l r ⊆ ⋃ i : S, Icc (A i) (B i) := by
  have hsub : ∀ i, Ioo (A i) (B i) ⊆ Ioo a b := fun i =>
    Ioo_subset_Ioo (hbounds i).1 (hbounds i).2.2
  obtain ⟨l, r, hal, hlu, hur, hrb, _, hmax⟩ :=
    exists_bounded_ae_profile_run f (B i₀ - A i₀) a b u
      ⟨Ioo (A i₀) (B i₀), isOpen_Ioo, hu, hsub i₀, hprofile i₀⟩
  let S : Set ι := {i | (Ioo l r ∩ Ioo (A i) (B i)).Nonempty}
  have hlenpos : 0 < B i₀ - A i₀ := sub_pos.mpr (hbounds i₀).2.1
  have hS : ∀ i ∈ S, l ≤ A i ∧ B i ≤ r ∧ B i - A i = B i₀ - A i₀ := by
    intro i hi
    obtain ⟨heq, hsubset⟩ := hmax (A i) (B i) (hsub i) hi (B i - A i) (hprofile i)
    exact ⟨(Ioo_subset_Ioo_iff (hbounds i).2.1).mp hsubset |>.1,
      (Ioo_subset_Ioo_iff (hbounds i).2.1).mp hsubset |>.2, heq⟩
  have hfin : S.Finite := by
    have hf := finite_long_disjoint_intervals l r (B i₀ - A i₀) A B S hlenpos
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
  refine ⟨l, r, hal, hlu, hur, hrb, hfin, ⟨u, ⟨hlu, hur⟩, hu⟩, hS, hnull, ?_⟩
  exact closed_interval_subset_of_ae_finite_interval_cover l r
    (fun i : S => A i) (fun i : S => B i) (lt_trans hlu hur) hnull

end LatticeProb
