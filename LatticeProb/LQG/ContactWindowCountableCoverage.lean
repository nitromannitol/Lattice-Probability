import LatticeProb.LQG.DirectContactWindowExceptions
import LatticeProb.LQG.ContactFrontierUncountable
import LatticeProb.LQG.ContactWindowComponentCount

/-! # Contact components and countable exceptional fibres -/


open Set

namespace MatedCRTHarmonic.RouteM

/-- Countability of cross-cell contacts without a direct chord implies that every
nonsingleton component of the cell intersection meets a strict selector window. -/
theorem Peanosphere.contact_components_meet_windows_of_countable_nondirect
    {ω : MatedCRT.Path2} {η : ℝ → ℂ} (P : Peanosphere ω η)
    {ε : ℝ} {x y : ℤ} (hε : 0 < ε) (hxy : x + 1 < y)
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
  have hex := P.countable_direct_contacts_outside_windows hε hxy
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

end MatedCRTHarmonic.RouteM
