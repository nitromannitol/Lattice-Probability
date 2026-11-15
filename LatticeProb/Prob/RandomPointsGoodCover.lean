import LatticeProb.Prob.RandomPointsCoverSquare

/-! # Good points in a random covering

A finite random covering contains a covering by good points if the probability
of a covering failure plus the expected number of bad points is less than one.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.RandomPointsCover

/-- A product sample has a realization consisting entirely of good points and
covering `Q` when the union bound for both failures is strictly below one. -/
theorem exists_good_cover_of_failure_bound {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (Q G : Set α) (hG : MeasurableSet G) (r : ℝ) (a : ℝ≥0∞)
    (hcover : Measure.pi (fun _ : Fin N => μ)
      {z | ¬ Q ⊆ ⋃ j, ball (z j) r} ≤ a)
    (hsmall : a + (N : ℝ≥0∞) * μ Gᶜ < 1) :
    ∃ z : Fin N → α, (∀ j, z j ∈ G) ∧ Q ⊆ ⋃ j, ball (z j) r := by
  classical
  let P : Measure (Fin N → α) := Measure.pi (fun _ : Fin N => μ)
  have hcoord : ∀ j : Fin N, P {z | z j ∉ G} = μ Gᶜ := by
    intro j
    exact (measurePreserving_eval (fun _ : Fin N => μ) j).measure_preimage hG.compl.nullMeasurableSet
  have hbad : P (⋃ j : Fin N, {z | z j ∉ G}) ≤ (N : ℝ≥0∞) * μ Gᶜ := by
    calc
      P (⋃ j : Fin N, {z | z j ∉ G}) ≤ ∑ j : Fin N, P {z | z j ∉ G} :=
        measure_iUnion_fintype_le P _
      _ = (N : ℝ≥0∞) * μ Gᶜ := by simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_contra h
  have hsub : Set.univ ⊆ {z : Fin N → α | ¬ Q ⊆ ⋃ j, ball (z j) r} ∪
      ⋃ j : Fin N, {z | z j ∉ G} := by
    intro z _
    by_cases hz : Q ⊆ ⋃ j, ball (z j) r
    · right
      have hg : ¬ ∀ j, z j ∈ G := fun hall => h ⟨z, hall, hz⟩
      push Not at hg
      obtain ⟨j, hj⟩ := hg
      exact mem_iUnion.mpr ⟨j, hj⟩
    · exact Or.inl hz
  have hle := (measure_mono (μ := P) hsub).trans (measure_union_le _ _)
  have hle' : (1 : ℝ≥0∞) ≤ a + (N : ℝ≥0∞) * μ Gᶜ := by
    calc
      1 = P Set.univ := (measure_univ).symm
      _ ≤ P {z : Fin N → α | ¬ Q ⊆ ⋃ j, ball (z j) r} +
          P (⋃ j : Fin N, {z | z j ∉ G}) := hle
      _ ≤ a + (N : ℝ≥0∞) * μ Gᶜ := add_le_add hcover hbad
  exact (not_lt_of_ge hle') hsmall

end LatticeProb.RandomPointsCover
end
