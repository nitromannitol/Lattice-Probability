import LatticeProb.LQG.ContourChainTurns
import LatticeProb.Prob.CorrelatedBMMixedTimes

/-! # Contact windows and local contour turns -/


open Set MeasureTheory
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.RouteM

/-- Local mixed-turn image countability follows from global opposite-direction
turn countability and local countability of the two same-direction cases. -/
theorem countable_mixed_turn_images_inter {L R : ℝ → ℝ} {η : ℝ → ℂ} {S : Set ℂ}
    (hmix₁ : {s | ∃ a t, directRel L s t ∧ directRel R a s}.Countable)
    (hmix₂ : {s | ∃ a t, directRel R s t ∧ directRel L a s}.Countable)
    (hcone₁ : (η '' {s | ∃ a c, a ≠ c ∧ directRel L s a ∧ directRel R s c} ∩ S).Countable)
    (hcone₂ : (η '' {s | ∃ a c, a ≠ c ∧ directRel L a s ∧ directRel R c s} ∩ S).Countable) :
    ({z | ∃ a b c, a ≠ c ∧
      (((directRel L a b ∨ directRel L b a) ∧ (directRel R b c ∨ directRel R c b)) ∨
       ((directRel R a b ∨ directRel R b a) ∧ (directRel L b c ∨ directRel L c b))) ∧
      η b = z} ∩ S).Countable := by
  apply ((((hmix₁.union hmix₂).image η).union hcone₁).union hcone₂).mono
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

/-- Local mixed-turn image countability gives local non-direct image countability. -/
theorem Peanosphere.countable_nondirect_inter_of_countable_mixed_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η) {S : Set ℂ}
    (hmixed : ({z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z} ∩ S).Countable) :
    ({z | ∃ s t, s < t ∧ η s = η t ∧
      ¬ (directRel (lCoord ω) s t ∨ directRel (rCoord ω) s t) ∧ η s = z} ∩ S).Countable := by
  apply (P.countable_repeated_side_turns.union hmixed).mono
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

/-- Local mixed-turn image countability gives strict-window coverage of every
nonsingleton component of a cell intersection. -/
theorem Peanosphere.contact_components_meet_windows_of_local_mixed_turns
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
    (hmixed : ({z | ∃ a b c, a ≠ c ∧
      (((directRel (lCoord ω) a b ∨ directRel (lCoord ω) b a) ∧
        (directRel (rCoord ω) b c ∨ directRel (rCoord ω) c b)) ∨
       ((directRel (rCoord ω) a b ∨ directRel (rCoord ω) b a) ∧
        (directRel (lCoord ω) b c ∨ directRel (lCoord ω) c b))) ∧ η b = z} ∩
      (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
       η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))).Countable) :
    ∀ C ∈ LatticeProb.nonSingletonComponents
        (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)),
      (C ∩ ((fun level => η (ellMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (lCoord ω) x y) (dWinHi ε (lCoord ω) x y) ∪
        (fun level => η (rhoMinus ω (ε * x) level)) ''
          Ioo (dWinLo ε (rCoord ω) x y) (dWinHi ε (rCoord ω) x y))).Nonempty := by
  apply P.contact_components_meet_windows_of_countable_nondirect hε hxy
  apply (P.countable_nondirect_inter_of_countable_mixed_turns hmixed).mono
  rintro z ⟨hzS, hno⟩
  obtain ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩ := hzS
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have hst : s < t := by nlinarith [hs.2, ht.1]
  refine ⟨⟨s, t, hst, hsz.trans htz.symm, ?_, hsz⟩, ⟨⟨s, hs, hsz⟩, ⟨t, ht, htz⟩⟩⟩
  intro hd
  exact hno ⟨s, hs, t, ht, hd, hsz⟩

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRT RouteM

/-- For the full parameter range, local countability of same-direction cone-turn
images implies that every nonsingleton contact component meets a strict window. -/
theorem ae_contact_components_meet_windows_of_local_cone_turns
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ((η ω) '' {s | ∃ a c, a ≠ c ∧ directRel (lCoord (bm ω)) s a ∧
        directRel (rCoord (bm ω)) s c} ∩ S).Countable →
      ((η ω) '' {s | ∃ a c, a ≠ c ∧ directRel (lCoord (bm ω)) a s ∧
        directRel (rCoord (bm ω)) c s} ∩ S).Countable →
      ∀ C ∈ LatticeProb.nonSingletonComponents S,
        (C ∩ ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) ''
            Ioo (dWinLo ε (lCoord (bm ω)) x y) (dWinHi ε (lCoord (bm ω)) x y) ∪
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) ''
            Ioo (dWinLo ε (rCoord (bm ω)) x y) (dWinHi ε (rCoord (bm ω)) x y))).Nonempty := by
  have hmix := ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable
    (LatticeProb.CorrelatedBM.ae_countable_mixTimes hγ0 hγ2 D.boundaryLawBM)
  filter_upwards [ae_peanosphere D, hmix] with ω hp hm
  intro ε x y hε hxy
  dsimp only
  intro hcone₁ hcone₂
  have hmixed := countable_mixed_turn_images_inter (η := η ω)
    (L := lCoord (bm ω)) (R := rCoord (bm ω))
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hm.1)
    (by simpa [lCoord, rCoord, MatedCRT.lrCoord, directRel, MatedCRT.DirectRel] using hm.2)
    hcone₁ hcone₂
  exact hp.contact_components_meet_windows_of_local_mixed_turns hε hxy hmixed

end MatedCRTHarmonic.MoTInput
