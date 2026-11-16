import LatticeProb.LQG.FullFibreContactLocalization
import LatticeProb.LQG.ContourChainRepeatedSide
import LatticeProb.LQG.ContactWindowCountableCoverage

/-! # Turns in contour identification chains -/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.RouteM

/-- A chain without a direct link between its endpoints contains two distinct
links meeting at a vertex in the same equivalence class. -/
theorem eqvGen_exists_turn {α : Type*} {r : α → α → Prop} {s t : α}
    (h : Relation.EqvGen r s t) (hne : s ≠ t)
    (hno : ¬ r s t ∧ ¬ r t s) :
    ∃ a b c, a ≠ c ∧ (r a b ∨ r b a) ∧ (r b c ∨ r c b) ∧
      Relation.EqvGen r s b := by
  classical
  obtain ⟨u, v, huv, hsu, hcut⟩ :=
    eqvGen_exists_crossing_link h {s} (by simp) (by simpa using Ne.symm hne)
  simp only [mem_singleton_iff] at hcut
  have hsuv : s ∈ ({u, v} : Set α) := by
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  have htuv : t ∉ ({u, v} : Set α) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    rcases hcut with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · constructor
      · exact hne.symm
      · intro he
        subst t
        exact hno.1 huv
    · constructor
      · intro he
        subst t
        exact hno.2 huv
      · exact hne.symm
  obtain ⟨p, q, hpq, hsp, hcut₂⟩ :=
    eqvGen_exists_crossing_link h {u, v} hsuv htuv
  have hsq : Relation.EqvGen r s q :=
    Relation.EqvGen.trans _ _ _ hsp (Relation.EqvGen.rel _ _ hpq)
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hcut₂
  rcases hcut₂ with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · rcases hp with hpu | hpv
    · subst p
      exact ⟨v, u, q, Ne.symm hq.2, Or.inr huv, Or.inl hpq, hsp⟩
    · subst p
      exact ⟨u, v, q, Ne.symm hq.1, Or.inl huv, Or.inl hpq, hsp⟩
  · rcases hq with hqu | hqv
    · subst q
      exact ⟨v, u, p, Ne.symm hp.2, Or.inr huv, Or.inr hpq, hsq⟩
    · subst q
      exact ⟨u, v, p, Ne.symm hp.1, Or.inl huv, Or.inr hpq, hsq⟩

/-- A non-direct identification contains a turn of two contour links. -/
theorem Peanosphere.exists_contour_turn_of_nondirect
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {s t : ℝ} (hst : s < t) (he : η s = η t)
    (hno : ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t)) :
    ∃ a b c, a ≠ c ∧
      ((directRel (lCoord ω) a b ∨ directRel (rCoord ω) a b) ∨
        (directRel (lCoord ω) b a ∨ directRel (rCoord ω) b a)) ∧
      ((directRel (lCoord ω) b c ∨ directRel (rCoord ω) b c) ∨
        (directRel (lCoord ω) c b ∨ directRel (rCoord ω) c b)) ∧ η s = η b := by
  have hno' : ¬ (directRel (lCoord ω) t s ∨ directRel (rCoord ω) t s) := by
    rintro (h | h) <;> exact (not_lt_of_ge hst.le) h.1
  obtain ⟨a, b, c, hac, hab, hbc, hsb⟩ :=
    eqvGen_exists_turn (P.onlyMerge s t he) hst.ne ⟨hno, hno'⟩
  exact ⟨a, b, c, hac, hab, hbc, eta_eq_of_eqvGen P hsb⟩


/-- If mixed-side turns have countable image, then non-direct identifications
have countable image. -/
theorem Peanosphere.countable_nondirect_of_countable_mixed_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    (hmixed : {z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z}.Countable) :
    {z | ∃ s t, s < t ∧ η s = η t ∧
      ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z}.Countable := by
  apply (P.countable_repeated_side_turns.union hmixed).mono
  rintro z ⟨s, t, hst, he, hno, hz⟩
  obtain ⟨a, b, c, hac, hab, hbc, hsb⟩ :=
    P.exists_contour_turn_of_nondirect hst he hno
  have hturn :
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b))) ∨
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) := by
    tauto
  rcases hturn with hrepeat | hmixed'
  · exact Or.inl ⟨a, b, c, hac, hrepeat, hsb.symm.trans hz⟩
  · exact Or.inr ⟨a, b, c, hac, hmixed', hsb.symm.trans hz⟩


/-- Countability of mixed-side contour turns implies that every nonsingleton
component of a cell intersection meets a strict selector window. -/
theorem Peanosphere.contact_components_meet_windows_of_countable_mixed_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
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
  apply P.contact_components_meet_windows_of_countable_nondirect hε hxy
  apply (P.countable_nondirect_of_countable_mixed_turns hmixed).mono
  rintro z ⟨⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩, hno⟩
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : s < t := by nlinarith [hs.2, ht.1]
  refine ⟨s, t, hst, hsz.trans htz.symm, ?_, hsz⟩
  intro hd
  exact hno ⟨s, hs, t, ht, hd, hsz⟩

end MatedCRTHarmonic.RouteM
