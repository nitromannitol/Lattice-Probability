import LatticeProb.LQG.ContourTurnBrownianCoverage
import LatticeProb.LQG.ConsecutiveCellContact

/-! # Contact windows of cells at distance at least one

The strict-window criterion for direct contour chords and the coverage of nonsingleton
components by strict contact windows up to countable exceptions hold for any two cells
`η([ε(x-1), εx])` and `η([ε(y-1), εy])` with `x + 1 ≤ y`. This includes consecutive cells
`y = x + 1`, for which the middle interval `[εx, ε(y-1)]` is the single time `εx`.

For `γ ≤ √2`, almost surely for all meshes, every nonsingleton component of the intersection
of two such cells meets a strict contact window. For two consecutive cells with at least one
strict window, the intersection therefore has exactly one nonsingleton component, the
component of `η(εx)`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace MatedCRTHarmonic.RouteM

/-- For a direct chord strictly spanning the middle interval of two cells at distance at
least one, its level lies in the strict window exactly when each cell contains a lower
contour value. -/
theorem directRel_mem_window_iff_of_le {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 ≤ y) (h : directRel X s t)
    (hs : s < ε * x) (ht : ε * ((y : ℝ) - 1) < t) :
    X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) ↔
      (∃ u ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x), X u < X s) ∧
      (∃ v ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y), X v < X s) := by
  have hxy' : (x : ℝ) + 1 ≤ y := by exact_mod_cast hxy
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

/-- A direct contact in two cell interiors at distance at least one lies in the strict
window when neither endpoint is a local minimum of the contour. -/
theorem directRel_mem_window_of_not_isLocalMin_of_le {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ} (hε : 0 < ε) (hxy : x + 1 ≤ y)
    (hs : s ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Ioo (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel X s t) (hns : ¬ IsLocalMin X s) (hnt : ¬ IsLocalMin X t) :
    X s ∈ Ioo (dWinLo ε X x y) (dWinHi ε X x y) := by
  apply (directRel_mem_window_iff_of_le hX hε hxy h hs.2 ht.1).2
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

/-- For cells at distance at least one, the direct cell contacts omitted by a window
selector are countable when local-minimum times are countable and direct contacts have
equal images. -/
theorem countable_direct_contacts_outside_window_of_le {X : ℝ → ℝ} (hX : Continuous X)
    {η : ℝ → ℂ} {W : Set ℂ} {ε : ℝ} {x y : ℤ}
    (hε : 0 < ε) (hxy : x + 1 ≤ y)
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
    exact (by simp : ({ε * ((x : ℝ) - 1), ε * x, ε * ((y : ℝ) - 1), ε * y} :
      Set ℝ).Finite).countable
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
    have hs' : s ∈ Ioo (ε * ((x : ℝ) - 1)) (ε * x) :=
      ⟨lt_of_le_of_ne hs.1 hboundary.1.symm, lt_of_le_of_ne hs.2 hboundary.2.1⟩
    have ht' : t ∈ Ioo (ε * ((y : ℝ) - 1)) (ε * y) :=
      ⟨lt_of_le_of_ne ht.1 hboundary.2.2.1.symm, lt_of_le_of_ne ht.2 hboundary.2.2.2⟩
    exact (hout (hwindow s hs t ht hrel
      (directRel_mem_window_of_not_isLocalMin_of_le hX hε hxy hs' ht' hrel hsmin htmin))).elim

/-- For consecutive cells, a direct chord from the first cell to the second at a level below
`X(εx)` ends strictly after `εx`. -/
theorem lt_of_directRel_consecutive {X : ℝ → ℝ} (hX : Continuous X)
    {ε : ℝ} {x y : ℤ} {s t : ℝ} (hy : y = x + 1)
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y)) (h : directRel X s t)
    (hlevel : X s < dWinHi ε X x y) : ε * (x : ℝ) < t := by
  have hy' : (y : ℝ) - 1 = x := by rw [hy]; push_cast; ring
  have hle : ε * (x : ℝ) ≤ t := by rw [← hy']; exact ht.1
  refine lt_of_le_of_ne hle ?_
  intro hte
  rw [dWinHi_consecutive hX hy, h.2.1, ← hte] at hlevel
  exact lt_irrefl _ hlevel

/-- A direct left contact between two cells at distance at least one is represented by its
strict-window selector at the boundary of the first cell. -/
theorem left_direct_contact_mem_window_image_of_le {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 ≤ y)
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel (lCoord ω) s t)
    (hlevel : lCoord ω s ∈ Ioo (dWinLo ε (lCoord ω) x y)
      (dWinHi ε (lCoord ω) x y)) :
    η s ∈ (fun level => η (ellMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) := by
  rcases lt_or_eq_of_le hxy with hlt | hxy1
  · exact left_direct_contact_mem_window_image hε hlt hs ht h hlevel
  · have hst : ε * (x : ℝ) < t :=
      lt_of_directRel_consecutive continuous_lCoord hxy1.symm ht h hlevel.2
    have heq : ellMinus ω (ε * x) (lCoord ω s) = s :=
      ellMinus_eq_left_of_above s t (lCoord ω s) rfl h.2.2 hs.2 hst
    exact ⟨lCoord ω s, hlevel, by simp only [heq]⟩

/-- A direct right contact between two cells at distance at least one is represented by its
strict-window selector at the boundary of the first cell. -/
theorem right_direct_contact_mem_window_image_of_le {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    {ε : ℝ} {x y : ℤ} {s t : ℝ}
    (hε : 0 < ε) (hxy : x + 1 ≤ y)
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y))
    (h : directRel (rCoord ω) s t)
    (hlevel : rCoord ω s ∈ Ioo (dWinLo ε (rCoord ω) x y)
      (dWinHi ε (rCoord ω) x y)) :
    η s ∈ (fun level => η (rhoMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y) := by
  rcases lt_or_eq_of_le hxy with hlt | hxy1
  · exact right_direct_contact_mem_window_image hε hlt hs ht h hlevel
  · have hst : ε * (x : ℝ) < t :=
      lt_of_directRel_consecutive continuous_rCoord hxy1.symm ht h hlevel.2
    have heq : rhoMinus ω (ε * x) (rCoord ω s) = s :=
      rhoMinus_eq_left_of_above s t (rCoord ω s) rfl h.2.2 hs.2 hst
    exact ⟨rCoord ω s, hlevel, by simp only [heq]⟩

/-- For cells at distance at least one, direct left or right contacts, except for countably
many points, are represented by one of the strict-window selectors. -/
theorem Peanosphere.countable_direct_contacts_outside_windows_of_le
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 ≤ y) :
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
  have hleft := countable_direct_contacts_outside_window_of_le continuous_lCoord
    (η := η) (W := W) hε hxy hL
    (fun s t h => P.merge s t (Or.inl h))
    (fun s hs t ht h hlevel => Or.inl
      (left_direct_contact_mem_window_image_of_le hε hxy hs ht h hlevel))
  have hright := countable_direct_contacts_outside_window_of_le continuous_rCoord
    (η := η) (W := W) hε hxy hR
    (fun s t h => P.merge s t (Or.inr h))
    (fun s hs t ht h hlevel => Or.inr
      (right_direct_contact_mem_window_image_of_le hε hxy hs ht h hlevel))
  apply (hleft.union hright).mono
  rintro z ⟨s, hs, t, ht, (h | h), heq, hout⟩
  · exact Or.inl ⟨s, hs, t, ht, h, heq, hout⟩
  · exact Or.inr ⟨s, hs, t, ht, h, heq, hout⟩

/-- For cells at distance at least one, countability of cross-cell contacts without a direct
chord implies that every nonsingleton component of the cell intersection meets a strict
selector window. -/
theorem Peanosphere.contact_components_meet_windows_of_countable_nondirect_of_le
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 ≤ y)
    (hbad : {z | z ∈ η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y) ∧
        ¬ ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
          ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
            (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z}.Countable) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  let S := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
    η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
  let W := (fun level => η (ellMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
    (fun level => η (rhoMinus ω (ε * x) level)) ''
      Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y)
  have hex := P.countable_direct_contacts_outside_windows_of_le hε hxy
  have hcount : (S \ W).Countable := by
    apply (hbad.union hex).mono
    intro z hz
    by_cases hd : ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x),
        ∃ t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * y),
          (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z
    · obtain ⟨s, hs, t, ht, hr, he⟩ := hd
      exact Or.inr ⟨s, hs, t, ht, hr, he, hz.2⟩
    · exact Or.inl ⟨hz.1, hd⟩
  intro C hC
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hC.2
  obtain ⟨c, hc, rfl⟩ := hC.1
  have hpre : IsPreconnected (connectedComponentIn S c) := isPreconnected_connectedComponentIn
  have hn := LatticeProb.Topology.not_countable_of_isPreconnected_of_ne hpre ha hb hab
  by_contra hmeet
  apply hn
  apply hcount.mono
  intro z hz
  exact ⟨connectedComponentIn_subset S c hz, fun hw => hmeet ⟨z, hz, hw⟩⟩

/-- For cells at distance at least one, countability of mixed-side contour turns implies
that every nonsingleton component of the cell intersection meets a strict selector window.
For consecutive cells the only cross-cell identification without ordered times is at `εx`. -/
theorem Peanosphere.contact_components_meet_windows_of_countable_mixed_turns_of_le
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 ≤ y)
    (hmixed : {z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z}.Countable) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  apply P.contact_components_meet_windows_of_countable_nondirect_of_le hε hxy
  apply ((P.countable_nondirect_of_countable_mixed_turns hmixed).union
    (countable_singleton (η (ε * x)))).mono
  rintro z ⟨⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩, hno⟩
  have hxy' : (x : ℝ) + 1 ≤ y := by exact_mod_cast hxy
  rcases lt_or_ge s t with hst | hts
  · exact Or.inl ⟨s, t, hst, hsz.trans htz.symm,
      fun hd => hno ⟨s, hs, t, ht, hd, hsz⟩, hsz⟩
  · right
    have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by nlinarith
    have hs' : s = ε * x := le_antisymm hs.2 (by linarith [ht.1])
    rw [mem_singleton_iff, ← hsz, hs']

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRT RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- For `γ ≤ √2`, every nonsingleton component of the intersection of two cells at distance
at least one, consecutive cells included, meets a strict contact window almost surely. -/
theorem ae_contact_components_meet_windows_of_le_sqrt_two_of_le
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 ≤ y →
      ∀ C ∈ LatticeProb.nonSingletonComponents
          ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
           (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
            Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
            Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty := by
  have hγ2 : γ < 2 := by
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    exact lt_of_le_of_lt hγ hsqrt
  have hmix := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (LatticeProb.CorrelatedBM.ae_countable_mixTimes hγ0 hγ2 D.boundaryLawBM)
  have hcone := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (LatticeProb.CorrelatedBM.ae_countable_coneTimes_of_le_sqrt_two hγ0 hγ D.boundaryLawBM)
  filter_upwards [ae_peanosphere D, hmix, hcone] with ω hp hm hc
  have hmixed := countable_mixed_turn_images (η := η ω)
    (L := lCoord (bm ω)) (R := rCoord (bm ω))
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hm.1)
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hm.2)
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hc.1)
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hc.2)
  intro ε x y hε hxy
  exact hp.contact_components_meet_windows_of_countable_mixed_turns_of_le hε hxy hmixed

/-- For `γ ≤ √2`, almost surely, for all meshes and two consecutive cells with at least one
strict contact window, the intersection of the two cells has exactly one nonsingleton
connected component, the component of `η(εx)`. -/
theorem ae_consecutive_contact_components_count_one_of_le_sqrt_two
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → y = x + 1 →
      (dWinLo ε (lCoord (bm ω)) x y < lCoord (bm ω) (ε * x) ∨
        dWinLo ε (rCoord (bm ω)) x y < rCoord (bm ω) (ε * x)) →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      LatticeProb.nonSingletonComponents S = {connectedComponentIn S (η ω (ε * x))} ∧
        (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
        (LatticeProb.nonSingletonComponents S).encard = 1 := by
  filter_upwards [ae_consecutive_contact_components_count_one D,
    ae_contact_components_meet_windows_of_le_sqrt_two_of_le hγ0 hγ D] with ω h1 h2
  intro ε x y hε hy hstrict
  exact h1 ε x y hε hy hstrict (h2 ε x y hε (by omega))

end MatedCRTHarmonic.MoTInput
