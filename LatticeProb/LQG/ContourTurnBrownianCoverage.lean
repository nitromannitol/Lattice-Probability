import LatticeProb.LQG.ContourChainTurns
import LatticeProb.Prob.CorrelatedBMMixedTimes
import LatticeProb.Prob.CorrelatedBMConeTimes

/-! # Contact components and Brownian contour turns -/

set_option autoImplicit false

open Set MeasureTheory
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.RouteM

/-- Countability of opposite-direction mixed times and same-direction cone times
implies countability of images of mixed contour turns. -/
theorem countable_mixed_turn_images {L R : ℝ → ℝ} {η : ℝ → ℂ}
    (hmix₁ : {s | ∃ a t, directRel L s t ∧ directRel R a s}.Countable)
    (hmix₂ : {s | ∃ a t, directRel R s t ∧ directRel L a s}.Countable)
    (hcone₁ : {s | ∃ a c, a ≠ c ∧ directRel L s a ∧ directRel R s c}.Countable)
    (hcone₂ : {s | ∃ a c, a ≠ c ∧ directRel L a s ∧ directRel R c s}.Countable) :
    {z | ∃ a b c, a ≠ c ∧
      (((directRel L a b ∨ directRel L b a) ∧ (directRel R b c ∨ directRel R c b)) ∨
       ((directRel R a b ∨ directRel R b a) ∧ (directRel L b c ∨ directRel L c b))) ∧
      η b = z}.Countable := by
  apply (((hmix₁.union hmix₂).union hcone₁).union hcone₂).image η |>.mono
  rintro z ⟨a, b, c, hac, h, hη⟩
  refine ⟨b, ?_, hη⟩
  rcases h with ⟨hl | hl, hr | hr⟩ | ⟨hr | hr, hl | hl⟩
  · exact Or.inl (Or.inl (Or.inr ⟨a, c, hr, hl⟩))
  · exact Or.inr ⟨a, c, hac, hl, hr⟩
  · exact Or.inl (Or.inr ⟨a, c, hac, hl, hr⟩)
  · exact Or.inl (Or.inl (Or.inl ⟨c, a, hl, hr⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨a, c, hl, hr⟩))
  · exact Or.inr ⟨c, a, hac.symm, hl, hr⟩
  · exact Or.inl (Or.inr ⟨c, a, hac.symm, hl, hr⟩)
  · exact Or.inl (Or.inl (Or.inr ⟨c, a, hr, hl⟩))

end MatedCRTHarmonic.RouteM

namespace MatedCRTHarmonic.MoTInput

open MatedCRT RouteM

/-- For `γ ≤ √2`, every nonsingleton component of the intersection of two
nonconsecutive cells meets a strict contact window almost surely. -/
theorem ae_contact_components_meet_windows_of_le_sqrt_two
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ), 0 < ε → x + 1 < y →
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
  exact hp.contact_components_meet_windows_of_countable_mixed_turns hε hxy hmixed

end MatedCRTHarmonic.MoTInput
