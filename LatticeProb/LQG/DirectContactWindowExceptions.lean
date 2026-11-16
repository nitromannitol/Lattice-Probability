import LatticeProb.LQG.DirectContactWindow
import LatticeProb.LQG.DirectContactWindowLevels
import LatticeProb.Analysis.LocalMinCountable

/-! # Exceptional direct contacts between contour cells -/


open Set Filter
open scoped Topology

namespace MatedCRTHarmonic.RouteM

/-- A direct contact in two cell interiors lies in the strict window when
neither endpoint is a local minimum of the contour. -/
theorem directRel_mem_window_of_not_isLocalMin {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ} (hε : 0 < ε) (hxy : x + 1 < y)
    (hs : s ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Ioo (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel X s t) (hns : ¬ IsLocalMin X s) (hnt : ¬ IsLocalMin X t) :
    X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) := by
  apply (directRel_mem_window_iff hX hε hxy h hs.2 ht.1).2
  constructor
  · by_contra hn
    push Not at hn
    apply hns
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
    exact hn u ⟨hu.1.le, hu.2.le⟩
  · by_contra hn
    push Not at hn
    apply hnt
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [← h.2.1]
    exact hn u ⟨hu.1.le, hu.2.le⟩

/-- The direct cell contacts omitted by a window selector are countable when
local-minimum times are countable and direct contacts have equal images. -/
theorem countable_direct_contacts_outside_window {X : ℝ → ℝ} (hX : Continuous X)
    {η : ℝ → ℂ} {W : Set ℂ} {ε : ℝ} {x y : ℤ}
    (hε : 0 < ε) (hxy : x + 1 < y)
    (hmin : {s | IsLocalMin X s}.Countable)
    (hmerge : ∀ s t, directRel X s t → η s = η t)
    (hwindow : ∀ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
      ∀ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y), directRel X s t →
      X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) → η s ∈ W) :
    {z | ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
      ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
        directRel X s t ∧ η s = z ∧ z ∉ W}.Countable := by
  let B : Set ℝ := {ε * ((x : ℝ) - 1), ε * x, ε * ((y : ℝ) - 1), ε * y}
  have hB : B.Countable := by
    dsimp [B]
    exact (by simp : ({ε * ((x : ℝ) - 1), ε * x, ε * ((y : ℝ) - 1), ε * y} : Set ℝ).Finite).countable
  apply ((hB.union hmin).image η).mono
  rintro z ⟨s, hs, t, ht, hrel, rfl, hout⟩
  by_cases hsmin : IsLocalMin X s
  · exact ⟨s, Or.inr hsmin, rfl⟩
  by_cases htmin : IsLocalMin X t
  · exact ⟨t, Or.inr htmin, (hmerge s t hrel).symm⟩
  by_cases hboundary : s = ε * ((x : ℝ) - 1) ∨ s = ε * x ∨
      t = ε * ((y : ℝ) - 1) ∨ t = ε * y
  · rcases hboundary with h | h | h | h
    · exact ⟨s, Or.inl (by simp [B, h]), rfl⟩
    · exact ⟨s, Or.inl (by simp [B, h]), rfl⟩
    · exact ⟨t, Or.inl (by simp [B, h]), (hmerge s t hrel).symm⟩
    · exact ⟨t, Or.inl (by simp [B, h]), (hmerge s t hrel).symm⟩
  · push Not at hboundary
    have hs' : s ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x) := by
      exact ⟨lt_of_le_of_ne hs.1 hboundary.1.symm, lt_of_le_of_ne hs.2 hboundary.2.1⟩
    have ht' : t ∈ Ioo (ε * ((y : ℝ) - 1)) (ε * y) := by
      exact ⟨lt_of_le_of_ne ht.1 hboundary.2.2.1.symm, lt_of_le_of_ne ht.2 hboundary.2.2.2⟩
    exact (hout (hwindow s hs t ht hrel
      (directRel_mem_window_of_not_isLocalMin hX hε hxy hs' ht' hrel hsmin htmin))).elim

/-- Direct left or right contacts between two cells, except for countably many
points, are represented by one of the strict-window selectors. -/
theorem Peanosphere.countable_direct_contacts_outside_windows
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y) :
    {z | ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
      ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
        (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z ∧
        z ∉ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
          (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))}.Countable := by
  let W : Set ℂ := (fun level => η (ellMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
    (fun level => η (rhoMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y)
  have hL : {s | IsLocalMin (lCoord ω) s}.Countable := by
    apply LatticeProb.countable_localMin_of_distinct_values
    change ∀ a b, a ≠ b → IsLocalMin (fun t => (ω t).1) a →
      IsLocalMin (fun t => (ω t).1) b → (ω a).1 ≠ (ω b).1
    simpa [MatedCRT.lrCoord] using P.locMinDistinct (0 : Fin 2)
  have hR : {s | IsLocalMin (rCoord ω) s}.Countable := by
    apply LatticeProb.countable_localMin_of_distinct_values
    change ∀ a b, a ≠ b → IsLocalMin (fun t => (ω t).2) a →
      IsLocalMin (fun t => (ω t).2) b → (ω a).2 ≠ (ω b).2
    simpa [MatedCRT.lrCoord] using P.locMinDistinct (1 : Fin 2)
  have hleft := countable_direct_contacts_outside_window continuous_lCoord
    (η := η) (W := W) hε hxy hL
    (fun s t h => P.merge s t (Or.inl h))
    (fun s hs t ht h hlevel => Or.inl
      (left_direct_contact_mem_window_image hε hxy hs ht h hlevel))
  have hright := countable_direct_contacts_outside_window continuous_rCoord
    (η := η) (W := W) hε hxy hR
    (fun s t h => P.merge s t (Or.inr h))
    (fun s hs t ht h hlevel => Or.inr
      (right_direct_contact_mem_window_image hε hxy hs ht h hlevel))
  apply (hleft.union hright).mono
  rintro z ⟨s, hs, t, ht, (h | h), heq, hout⟩
  · exact Or.inl ⟨s, hs, t, ht, h, heq, hout⟩
  · exact Or.inr ⟨s, hs, t, ht, h, heq, hout⟩

end MatedCRTHarmonic.RouteM
