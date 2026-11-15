import LatticeProb.LQG.CoupledContactWindow
import LatticeProb.Topology.CompactIntervalPath

/-! # Locally connected contact continua -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal Topology

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, each compact left-contour window gives an infinite locally
connected continuum contained in the intersection of the two cells. -/
theorem ae_left_contact_continuum
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (lCoord (bm ω)) x y < a →
      b < dWinHi ε (lCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (ellMinus (bm ω) (ε * x) level)
      IsCompact (f '' Icc a b) ∧ IsConnected (f '' Icc a b) ∧
      LatticeProb.Topology.IsLocallyConnectedSet (f '' Icc a b) ∧ (f '' Icc a b).Infinite ∧
      f '' Icc a b ⊆
        (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  filter_upwards [ae_left_contact_window D] with ω h
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨hc, hmem, hinf⟩ := h ε x y a b hε hxy ha hb hab
  exact ⟨isCompact_Icc.image_of_continuousOn hc, (isConnected_Icc hab.le).image _ hc,
    LatticeProb.Topology.isLocallyConnectedSet_image_Icc hab.le hc, hinf,
    image_subset_iff.mpr hmem⟩

/-- Almost surely, each compact right-contour window gives an infinite locally
connected continuum contained in the intersection of the two cells. -/
theorem ae_right_contact_continuum
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (rCoord (bm ω)) x y < a →
      b < dWinHi ε (rCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (rhoMinus (bm ω) (ε * x) level)
      IsCompact (f '' Icc a b) ∧ IsConnected (f '' Icc a b) ∧
      LatticeProb.Topology.IsLocallyConnectedSet (f '' Icc a b) ∧ (f '' Icc a b).Infinite ∧
      f '' Icc a b ⊆
        (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y) := by
  filter_upwards [ae_right_contact_window D] with ω h
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨hc, hmem, hinf⟩ := h ε x y a b hε hxy ha hb hab
  exact ⟨isCompact_Icc.image_of_continuousOn hc, (isConnected_Icc hab.le).image _ hc,
    LatticeProb.Topology.isLocallyConnectedSet_image_Icc hab.le hc, hinf,
    image_subset_iff.mpr hmem⟩

end MatedCRTHarmonic.MoTInput
