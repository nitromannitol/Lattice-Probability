import LatticeProb.LQG.PeanosphereContactContinuity
import LatticeProb.LQG.ContourWindowInfiniteContact

/-! # Contact paths for contour windows -/

set_option autoImplicit false

open Set

namespace MatedCRTHarmonic.RouteM

/-- A compact interval of left-contour levels in a strict window gives a
continuous path in the intersection of the two cell images. If the curve has
finite point fibres and the level interval is nondegenerate, its image is infinite. -/
theorem Peanosphere.left_contact_window {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) {ε : ℝ} {x y : ℤ} {a b : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y)
    (ha : dWinLo ε (lCoord ω) x y < a)
    (hb : b < dWinHi ε (lCoord ω) x y) (hab : a < b)
    (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite) :
    ContinuousOn (fun level => η (ellMinus ω (ε * x) level)) (Icc a b) ∧
    (∀ level ∈ Icc a b,
      η (ellMinus ω (ε * x) level) ∈
        η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) ∧
    ((fun level => η (ellMinus ω (ε * x) level)) '' Icc a b).Infinite := by
  have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by
    have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    nlinarith
  obtain ⟨_, hmid⟩ := DAux.intervalInf_spec continuous_lCoord hbc
  have hbound : dWinHi ε (lCoord ω) x y ≤ lCoord ω (ε * x) :=
    hmid _ ⟨le_rfl, hbc⟩
  have hsub : Icc a b ⊆ Iio (lCoord ω (ε * x)) := by
    intro level hl
    exact lt_of_le_of_lt hl.2 (lt_of_lt_of_le hb hbound)
  refine ⟨(P.continuousOn_eta_ellMinus _).mono hsub, ?_, ?_⟩
  · intro level hl
    have hlo : dWinLo ε (lCoord ω) x y < level := lt_of_lt_of_le ha hl.1
    have hhi : level < dWinHi ε (lCoord ω) x y := lt_of_le_of_lt hl.2 hb
    obtain ⟨hd, _⟩ := lowArcData_contacts continuous_lCoord hε hxy hlo hhi
    change η (dLast (lCoord ω) (ε * x) level) ∈ _
    constructor
    · exact ⟨_, ⟨hd.mem₁.1.le, hd.mem₁.2.le⟩, rfl⟩
    · exact ⟨_, ⟨hd.mem₂.1.le, hd.mem₂.2.le⟩,
        (P.merge _ _ (Or.inl hd.rel)).symm⟩
  · intro hfin
    have htimes : (η ⁻¹' ((fun level => η (ellMinus ω (ε * x) level)) '' Icc a b)).Finite :=
      hfin.preimage' (fun z _ => hfinite z)
    apply (Set.Icc_infinite hab) ((htimes.image (lCoord ω)).subset ?_)
    intro level hl
    refine ⟨ellMinus ω (ε * x) level, ?_, ellMinus_level P (hsub hl)⟩
    exact ⟨level, hl, rfl⟩

/-- A compact interval of right-contour levels in a strict window gives a
continuous path in the intersection of the two cell images. If the curve has
finite point fibres and the level interval is nondegenerate, its image is infinite. -/
theorem Peanosphere.right_contact_window {ω : MatedCRT.Path2} {η : ℝ → ℂ}
    (P : Peanosphere ω η) {ε : ℝ} {x y : ℤ} {a b : ℝ}
    (hε : 0 < ε) (hxy : x + 1 < y)
    (ha : dWinLo ε (rCoord ω) x y < a)
    (hb : b < dWinHi ε (rCoord ω) x y) (hab : a < b)
    (hfinite : ∀ z : ℂ, (η ⁻¹' {z}).Finite) :
    ContinuousOn (fun level => η (rhoMinus ω (ε * x) level)) (Icc a b) ∧
    (∀ level ∈ Icc a b,
      η (rhoMinus ω (ε * x) level) ∈
        η '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        η '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) ∧
    ((fun level => η (rhoMinus ω (ε * x) level)) '' Icc a b).Infinite := by
  have hbc : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by
    have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
    nlinarith
  obtain ⟨_, hmid⟩ := DAux.intervalInf_spec continuous_rCoord hbc
  have hbound : dWinHi ε (rCoord ω) x y ≤ rCoord ω (ε * x) :=
    hmid _ ⟨le_rfl, hbc⟩
  have hsub : Icc a b ⊆ Iio (rCoord ω (ε * x)) := by
    intro level hl
    exact lt_of_le_of_lt hl.2 (lt_of_lt_of_le hb hbound)
  refine ⟨(P.continuousOn_eta_rhoMinus _).mono hsub, ?_, ?_⟩
  · intro level hl
    have hlo : dWinLo ε (rCoord ω) x y < level := lt_of_lt_of_le ha hl.1
    have hhi : level < dWinHi ε (rCoord ω) x y := lt_of_le_of_lt hl.2 hb
    obtain ⟨hd, _⟩ := lowArcData_contacts continuous_rCoord hε hxy hlo hhi
    change η (dLast (rCoord ω) (ε * x) level) ∈ _
    constructor
    · exact ⟨_, ⟨hd.mem₁.1.le, hd.mem₁.2.le⟩, rfl⟩
    · exact ⟨_, ⟨hd.mem₂.1.le, hd.mem₂.2.le⟩,
        (P.merge _ _ (Or.inr hd.rel)).symm⟩
  · intro hfin
    have htimes : (η ⁻¹' ((fun level => η (rhoMinus ω (ε * x) level)) '' Icc a b)).Finite :=
      hfin.preimage' (fun z _ => hfinite z)
    apply (Set.Icc_infinite hab) ((htimes.image (rCoord ω)).subset ?_)
    intro level hl
    refine ⟨rhoMinus ω (ε * x) level, ?_, rhoMinus_level P (hsub hl)⟩
    exact ⟨level, hl, rfl⟩

end MatedCRTHarmonic.RouteM
