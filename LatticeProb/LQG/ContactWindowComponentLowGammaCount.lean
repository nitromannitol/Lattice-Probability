import LatticeProb.LQG.ContactWindowComponentExactCount
import LatticeProb.LQG.ContourTurnBrownianCoverage

/-! # Contact-window component counts for small γ -/

open MeasureTheory Set
open scoped NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- For `0 < γ ≤ √2`, the two strict contact windows determine exactly one
or two nonsingleton components, according to whether their components coincide. -/
theorem ae_contact_window_components_exact_count_of_le_sqrt_two
    (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ),
      0 < ε → x + 1 < y →
      dWinLo ε (lCoord (bm ω)) x y < dWinHi ε (lCoord (bm ω)) x y →
      dWinLo ε (rCoord (bm ω)) x y < dWinHi ε (rCoord (bm ω)) x y →
      let S := (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
        (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)
      ∃ C ∈ LatticeProb.nonSingletonComponents S, ∃ E ∈ LatticeProb.nonSingletonComponents S,
        (∀ a b, dWinLo ε (lCoord (bm ω)) x y < a →
          b < dWinHi ε (lCoord (bm ω)) x y → a < b →
          (fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ C) ∧
        (∀ a b, dWinLo ε (rCoord (bm ω)) x y < a →
          b < dWinHi ε (rCoord (bm ω)) x y → a < b →
          (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b ⊆ E) ∧
        LatticeProb.nonSingletonComponents S = {C, E} ∧
        (C = E → (LatticeProb.nonSingletonComponents S).ncard = 1 ∧
          (LatticeProb.nonSingletonComponents S).encard = 1) ∧
        (C ≠ E → (LatticeProb.nonSingletonComponents S).ncard = 2 ∧
          (LatticeProb.nonSingletonComponents S).encard = 2) := by
  filter_upwards [ae_contact_window_components_exact_count_of_meets_windows D,
    ae_contact_components_meet_windows_of_le_sqrt_two hγ0 hγ D] with ω hcount hmeet
  intro ε x y hε hxy hl hr
  exact hcount ε x y hε hxy hl hr (hmeet ε x y hε hxy)

end MatedCRTHarmonic.MoTInput
