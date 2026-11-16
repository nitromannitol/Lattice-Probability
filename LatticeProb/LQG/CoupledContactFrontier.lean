import LatticeProb.LQG.CoupledContactContinuum
import LatticeProb.LQG.CouplingSharedSegmentFrontiers

/-! # Contact continua in shared-frontier components -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Every strict left contour window gives an infinite shared-frontier component
containing its contact continuum, simultaneously for all meshes and windows. -/
theorem ae_left_contact_frontier_component
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (lCoord (bm ω)) x y < a →
      b < dWinHi ε (lCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (ellMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧ f '' Icc a b ⊆ C := by
  filter_upwards [ae_left_contact_continuum D, ae_shared_frontiers_of_coupling D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨_, hconn, _, hinf, hsub⟩ := hc ε x y a b hε hxy ha hb hab
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  rw [hfront] at hsub
  obtain ⟨z, hz⟩ := hinf.nonempty
  have hzS := hsub hz
  have hcont := hconn.isPreconnected.subset_connectedComponentIn hz hsub
  exact ⟨_, ⟨z, hzS, rfl⟩, hinf.mono hcont, hcont⟩

/-- Every strict right contour window gives an infinite shared-frontier component
containing its contact continuum, simultaneously for all meshes and windows. -/
theorem ae_right_contact_frontier_component
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (rCoord (bm ω)) x y < a →
      b < dWinHi ε (rCoord (bm ω)) x y → a < b →
      let f := fun level => η ω (rhoMinus (bm ω) (ε * x) level)
      let S := frontier ((η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        frontier ((η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y))
      ∃ C ∈ connectedComponentIn S '' S, C.Infinite ∧ f '' Icc a b ⊆ C := by
  filter_upwards [ae_right_contact_continuum D, ae_shared_frontiers_of_coupling D] with ω hc hf
  intro ε x y a b hε hxy ha hb hab
  obtain ⟨_, hconn, _, hinf, hsub⟩ := hc ε x y a b hε hxy ha hb hab
  have hx : ε * ((x : ℝ) - 1) < ε * x := by nlinarith
  have hy : ε * ((y : ℝ) - 1) < ε * y := by nlinarith
  have hxy' : (x : ℝ) + 1 < y := by exact_mod_cast hxy
  have horder : ε * x ≤ ε * ((y : ℝ) - 1) := by nlinarith
  have hfront := (hf _ _ _ _ hx horder hy).2.1
  rw [hfront] at hsub
  obtain ⟨z, hz⟩ := hinf.nonempty
  have hzS := hsub hz
  have hcont := hconn.isPreconnected.subset_connectedComponentIn hz hsub
  exact ⟨_, ⟨z, hzS, rfl⟩, hinf.mono hcont, hcont⟩

end MatedCRTHarmonic.MoTInput
