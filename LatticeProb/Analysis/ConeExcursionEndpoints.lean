import LatticeProb.Analysis.FirstDropAfterExcursion
import LatticeProb.Analysis.JointExitAfterExcursions

/-!
# Cone excursions and exit times

Two coordinate excursions from the same time give a cone interval. When the
excursion endpoints are not local minima, the earlier and later endpoints are
the first exit of either coordinate and the first joint exit, respectively.
-/

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Strict coordinate excursions give a cone interval whose endpoint is the
first coordinate exit, and the two excursion endpoints are the two exit times. -/
theorem cone_excursion_exit_times {X Y : ℝ → ℝ} {s a b : ℝ}
    (hsa : s < a) (hXa : X s = X a)
    (hX : ∀ t ∈ Ioo s a, X s < X t) (hXmin : ¬ IsLocalMin X a)
    (hsb : s < b) (hYb : Y s = Y b)
    (hY : ∀ t ∈ Ioo s b, Y s < Y t) (hYmin : ¬ IsLocalMin Y b) :
    let v := sInf {t : ℝ | s < t ∧ (X t < X s ∨ Y t < Y s)}
    let u := sInf {t : ℝ | s < t ∧ (∃ r ∈ Icc s t, X r < X s) ∧
      (∃ r ∈ Icc s t, Y r < Y s)}
    s < v ∧ (∀ t ∈ Icc s v, X s ≤ X t ∧ Y s ≤ Y t) ∧
      (a ≠ b → v < u) ∧ ((a = v ∧ b = u) ∨ (a = u ∧ b = v)) := by
  dsimp only
  rw [firstEitherDrop_eq_min_of_excursions hsa hXa hX hXmin hsb hYb hY hYmin,
    jointExit_eq_max_of_excursions hsa hXa hX hXmin hsb hYb hY hYmin]
  have excursion_le : ∀ (Z : ℝ → ℝ) (c t : ℝ), Z s = Z c →
      (∀ r ∈ Ioo s c, Z s < Z r) → t ∈ Icc s c → Z s ≤ Z t := by
    intro Z c t heq hpos ht
    rcases eq_or_lt_of_le ht.1 with rfl | hst
    · exact le_rfl
    rcases eq_or_lt_of_le ht.2 with htc | htc
    · simpa only [htc] using heq.le
    · exact (hpos t ⟨hst, htc⟩).le
  refine ⟨lt_min hsa hsb, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨excursion_le X a t hXa hX ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩,
      excursion_le Y b t hYb hY ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩⟩
  · intro hne
    rcases le_total a b with hab | hba
    · simpa only [min_eq_left hab, max_eq_right hab] using lt_of_le_of_ne hab hne
    · simpa only [min_eq_right hba, max_eq_left hba] using lt_of_le_of_ne hba hne.symm
  · rcases le_total a b with hab | hba
    · left
      simp [min_eq_left hab, max_eq_right hab]
    · right
      simp [min_eq_right hba, max_eq_left hba]

end LatticeProb
