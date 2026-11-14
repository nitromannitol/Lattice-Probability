import Mathlib

/-!
# Joint exit after excursions

For two real functions with strict excursions from the same starting time,
the first time by which both have dropped below their starting levels is the
later excursion endpoint, provided neither endpoint is a local minimum.
-/

open Set Filter
open scoped Topology

namespace LatticeProb

/-- The joint strict-drop exit is the later of the two excursion endpoints. -/
theorem jointExit_eq_max_of_excursions {X Y : ℝ → ℝ} {s a b : ℝ}
    (hsa : s < a) (hXa : X s = X a)
    (hX : ∀ v ∈ Ioo s a, X s < X v) (hXmin : ¬ IsLocalMin X a)
    (hsb : s < b) (hYb : Y s = Y b)
    (hY : ∀ v ∈ Ioo s b, Y s < Y v) (hYmin : ¬ IsLocalMin Y b) :
    sInf {u : ℝ | s < u ∧ (∃ v ∈ Icc s u, X v < X s) ∧
      (∃ v ∈ Icc s u, Y v < Y s)} = max a b := by
  have near : ∀ (Z : ℝ → ℝ) (t r : ℝ), s < t → t < r → Z s = Z t →
      ¬ IsLocalMin Z t → ∃ v ∈ Ioo s r, Z v < Z s := by
    intro Z t r hst htr heq hmin
    by_contra hn
    have hm : IsMinOn Z (Ioo s r) t := by
      intro v hv
      by_contra hbad
      have hlt : Z v < Z s := by
        rw [heq]
        exact lt_of_not_ge hbad
      exact hn ⟨v, hv, hlt⟩
    exact hmin (hm.isLocalMin (Ioo_mem_nhds hst htr))
  have lower : ∀ (Z : ℝ → ℝ) (t v : ℝ),
      (∀ w ∈ Ioo s t, Z s < Z w) → s ≤ v → Z v < Z s → t ≤ v := by
    intro Z t v hpos hsv hv
    by_contra h
    have hvt : v < t := lt_of_not_ge h
    have hsv' : s < v := lt_of_le_of_ne hsv (by rintro rfl; exact (lt_irrefl _) hv)
    exact (not_lt_of_ge (hpos v ⟨hsv', hvt⟩).le) hv
  have below : ∀ r : ℝ, max a b < r →
      ∃ u ∈ {u : ℝ | s < u ∧ (∃ v ∈ Icc s u, X v < X s) ∧
        (∃ v ∈ Icc s u, Y v < Y s)}, u < r := by
    intro r hr
    obtain ⟨v, hv, hXv⟩ := near X a r hsa (lt_of_le_of_lt (le_max_left _ _) hr) hXa hXmin
    obtain ⟨w, hw, hYw⟩ := near Y b r hsb (lt_of_le_of_lt (le_max_right _ _) hr) hYb hYmin
    refine ⟨max v w, ⟨lt_of_lt_of_le hv.1 (le_max_left _ _), ?_, ?_⟩, max_lt hv.2 hw.2⟩
    · exact ⟨v, ⟨hv.1.le, le_max_left _ _⟩, hXv⟩
    · exact ⟨w, ⟨hw.1.le, le_max_right _ _⟩, hYw⟩
  have hnonempty : {u : ℝ | s < u ∧ (∃ v ∈ Icc s u, X v < X s) ∧
      (∃ v ∈ Icc s u, Y v < Y s)}.Nonempty := by
    obtain ⟨u, hu, _⟩ := below (max a b + 1) (by linarith)
    exact ⟨u, hu⟩
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt hnonempty
  · intro u hu
    obtain ⟨_, ⟨v, hv, hXv⟩, ⟨w, hw, hYw⟩⟩ := hu
    exact max_le (le_trans (lower X a v hX hv.1 hXv) hv.2)
      (le_trans (lower Y b w hY hw.1 hYw) hw.2)
  · exact below

end LatticeProb
