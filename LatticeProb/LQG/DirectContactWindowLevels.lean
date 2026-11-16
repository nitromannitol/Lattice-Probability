import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.PsiBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.RouteM.DLevels

/-! # Levels of direct contour contacts -/

open Set

namespace MatedCRTHarmonic.RouteM

/-- For a direct chord strictly spanning the middle interval, its level lies
in the strict window exactly when each cell contains a lower contour value. -/
theorem directRel_mem_window_iff {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y) (h : directRel X s t)
    (hs : s < ε * x) (ht : ε * ((y : ℝ) - 1) < t) :
    X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) ↔
      (∃ u ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x), X u < X s) ∧
      (∃ v ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y), X v < X s) := by
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hab : ε * ((x : ℝ) - 1) ≤ ε * x := by nlinarith
  have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hcd : ε * ((y : ℝ) - 1) ≤ ε * y := by nlinarith
  obtain ⟨⟨u, hu, huval⟩, hubound⟩ := DAux.intervalInf_spec hX hab
  obtain ⟨⟨w, hw, hwval⟩, -⟩ := DAux.intervalInf_spec hX hbc
  obtain ⟨⟨v, hv, hvval⟩, hvbound⟩ := DAux.intervalInf_spec hX hcd
  have hhi : X s < dWinHi ε X x y := by
    rw [dWinHi, ← hwval]
    exact h.2.2 w ⟨lt_of_lt_of_le hs hw.1, lt_of_le_of_lt hw.2 ht⟩
  constructor
  · intro hwin
    refine ⟨⟨u, hu, ?_⟩, ⟨v, hv, ?_⟩⟩
    · rw [huval]
      exact lt_of_le_of_lt (le_max_left _ _) hwin.1
    · rw [hvval]
      exact lt_of_le_of_lt (le_max_right _ _) hwin.1
  · rintro ⟨⟨u', hu', hlu⟩, ⟨v', hv', hlv⟩⟩
    refine ⟨?_, hhi⟩
    change max _ _ < X s
    exact max_lt (lt_of_le_of_lt (hubound u' hu') hlu)
      (lt_of_le_of_lt (hvbound v' hv') hlv)

/-- The strict window criterion for a direct chord with endpoints in the two
closed cells, including the conditions excluding the middle boundaries. -/
theorem directRel_mem_window_iff_cell_conditions {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y) (h : directRel X s t)
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y)) :
    X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) ↔
      s < ε * x ∧ ε * ((y : ℝ) - 1) < t ∧
      (∃ u ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x), X u < X s) ∧
      (∃ v ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y), X v < X s) := by
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by nlinarith
  obtain ⟨-, hbound⟩ := DAux.intervalInf_spec hX hbc
  constructor
  · intro hwin
    have hsb : s < ε * x := by
      refine lt_of_le_of_ne hs.2 ?_
      intro heq
      have hb := hbound (ε * x) ⟨le_rfl, hbc⟩
      have heqb : X (ε * x) = X s := congrArg X heq.symm
      rw [heqb] at hb
      exact (not_lt_of_ge hb) hwin.2
    have hct : ε * ((y : ℝ) - 1) < t := by
      refine lt_of_le_of_ne ht.1 ?_
      intro heq
      have hc := hbound (ε * ((y : ℝ) - 1)) ⟨hbc, le_rfl⟩
      have heqc : X (ε * ((y : ℝ) - 1)) = X s :=
        (congrArg X heq).trans h.2.1.symm
      rw [heqc] at hc
      exact (not_lt_of_ge hc) hwin.2
    exact ⟨hsb, hct, (directRel_mem_window_iff hX hε hxy h hsb hct).mp hwin⟩
  · rintro ⟨hsb, hct, hlow⟩
    exact (directRel_mem_window_iff hX hε hxy h hsb hct).mpr hlow

end MatedCRTHarmonic.RouteM
