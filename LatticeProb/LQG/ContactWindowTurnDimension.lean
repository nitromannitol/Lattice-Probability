import LatticeProb.LQG.ContactWindowLocalConeTurns
import LatticeProb.LQG.ContactWindowDimensionCoverage

/-! # Dimension bounds for contour-turn images -/

open Set MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.RouteM

/-- Mixed contour-turn images have dimension below one if the two local
same-direction images do and the opposite-direction turn times are countable. -/
theorem dimH_mixed_turn_images_inter_lt_one {L R : ℝ → ℝ} {η : ℝ → ℂ} {S : Set ℂ}
    (hmix₁ : {s | ∃ a t, directRel L s t ∧ directRel R a s}.Countable)
    (hmix₂ : {s | ∃ a t, directRel R s t ∧ directRel L a s}.Countable)
    (hcone₁ : dimH (η '' {s | ∃ a c, a ≠ c ∧ directRel L s a ∧ directRel R s c} ∩ S) < 1)
    (hcone₂ : dimH (η '' {s | ∃ a c, a ≠ c ∧ directRel L a s ∧ directRel R c s} ∩ S) < 1) :
    dimH ({z | ∃ a b c, a ≠ c ∧
      (((directRel L a b ∨ directRel L b a) ∧ (directRel R b c ∨ directRel R c b)) ∨
       ((directRel R a b ∨ directRel R b a) ∧ (directRel L b c ∨ directRel L c b))) ∧
      η b = z} ∩ S) < 1 := by
  let E := η '' ({s | ∃ a t, directRel L s t ∧ directRel R a s} ∪
    {s | ∃ a t, directRel R s t ∧ directRel L a s})
  let F := η '' {s | ∃ a c, a ≠ c ∧ directRel L s a ∧ directRel R s c} ∩ S
  let G := η '' {s | ∃ a c, a ≠ c ∧ directRel L a s ∧ directRel R c s} ∩ S
  have hE : E.Countable := (hmix₁.union hmix₂).image η
  have hsub : ({z | ∃ a b c, a ≠ c ∧
      (((directRel L a b ∨ directRel L b a) ∧ (directRel R b c ∨ directRel R c b)) ∨
       ((directRel R a b ∨ directRel R b a) ∧ (directRel L b c ∨ directRel L c b))) ∧
      η b = z} ∩ S) ⊆ (E ∪ F) ∪ G := by
    rintro z ⟨⟨a, b, c, hac, h, hη⟩, hz⟩
    rcases h with ⟨hl | hl, hr | hr⟩ | ⟨hr | hr, hl | hl⟩
    · exact Or.inl (Or.inl ⟨b, Or.inr ⟨a, c, hr, hl⟩, hη⟩)
    · exact Or.inr ⟨⟨b, ⟨a, c, hac, hl, hr⟩, hη⟩, hz⟩
    · exact Or.inl (Or.inr ⟨⟨b, ⟨a, c, hac, hl, hr⟩, hη⟩, hz⟩)
    · exact Or.inl (Or.inl ⟨b, Or.inl ⟨c, a, hl, hr⟩, hη⟩)
    · exact Or.inl (Or.inl ⟨b, Or.inl ⟨a, c, hl, hr⟩, hη⟩)
    · exact Or.inr ⟨⟨b, ⟨c, a, hac.symm, hl, hr⟩, hη⟩, hz⟩
    · exact Or.inl (Or.inr ⟨⟨b, ⟨c, a, hac.symm, hl, hr⟩, hη⟩, hz⟩)
    · exact Or.inl (Or.inl ⟨b, Or.inr ⟨c, a, hr, hl⟩, hη⟩)
  apply lt_of_le_of_lt (dimH_mono hsub)
  rw [dimH_union, dimH_union, hE.dimH_zero, zero_max]
  exact max_lt hcone₁ hcone₂

/-- Local mixed-turn image dimension controls non-direct contour contacts. -/
theorem Peanosphere.dimH_nondirect_inter_lt_one_of_mixed_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) {S : Set ℂ}
    (hmixed : dimH ({z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z} ∩ S) < 1) :
    dimH ({z | ∃ s t, s < t ∧ η s = η t ∧
      ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z} ∩ S) < 1 := by
  let E := {z | ∃ a b c, a ≠ c ∧
    (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
      (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b)) ∨
     ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
      (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b))) ∧ η b = z}
  have hE : E.Countable := P.countable_repeated_side_turns
  have hsub : ({z | ∃ s t, s < t ∧ η s = η t ∧
      ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z} ∩ S) ⊆
      E ∪ ({z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z} ∩ S) := by
    rintro z ⟨⟨s, t, hst, he, hno, hz⟩, hzS⟩
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
    · exact Or.inr ⟨⟨a, b, c, hac, hmixed', hsb.symm.trans hz⟩, hzS⟩
  apply lt_of_le_of_lt (dimH_mono hsub)
  rw [dimH_union, hE.dimH_zero, zero_max]
  exact hmixed

/-- Local cone-turn image dimension bounds imply strict-window coverage of
nonsingleton contact components. -/
theorem Peanosphere.contact_components_meet_windows_of_dimH_cone_turns_lt_one
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
    (hmix₁ : {s | ∃ a t, directRel (lCoord ω) s t ∧ directRel (rCoord ω) a s}.Countable)
    (hmix₂ : {s | ∃ a t, directRel (rCoord ω) s t ∧ directRel (lCoord ω) a s}.Countable)
    (hcone₁ : dimH (η '' {s | ∃ a c, a ≠ c ∧ directRel (lCoord ω) s a ∧
      directRel (rCoord ω) s c} ∩ (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
      η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) < 1)
    (hcone₂ : dimH (η '' {s | ∃ a c, a ≠ c ∧ directRel (lCoord ω) a s ∧
      directRel (rCoord ω) c s} ∩ (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
      η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) < 1) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  have hdim := P.dimH_nondirect_inter_lt_one_of_mixed_turns
    (dimH_mixed_turn_images_inter_lt_one hmix₁ hmix₂ hcone₁ hcone₂)
  apply P.contact_components_meet_windows_of_dimH_nondirect_lt_one hε hxy
  apply lt_of_le_of_lt (dimH_mono ?_) hdim
  rintro z ⟨hzS, hno⟩
  obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hzS
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : s < t := by nlinarith [hs.2, ht.1]
  refine ⟨⟨s, t, hst, hsz.trans htz.symm, ?_, hsz⟩, ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩⟩
  intro hd
  exact hno ⟨s, hs, t, ht, hd, hsz⟩

end MatedCRTHarmonic.RouteM
