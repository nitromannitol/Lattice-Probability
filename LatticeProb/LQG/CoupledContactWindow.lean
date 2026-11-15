import LatticeProb.LQG.PeanosphereContactWindow
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.VisitBoundQuantum

/-! # Contact paths for coupled area-parametrized curves -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.RouteM

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- Almost surely, every strict left-contour window has an infinite continuous
contact image contained in both associated cells. -/
theorem ae_left_contact_window
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (lCoord (bm ω)) x y < a →
      b < dWinHi ε (lCoord (bm ω)) x y → a < b →
      ContinuousOn (fun level => η ω (ellMinus (bm ω) (ε * x) level)) (Icc a b) ∧
      (∀ level ∈ Icc a b,
        η ω (ellMinus (bm ω) (ε * x) level) ∈
          (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) ∧
      ((fun level => η ω (ellMinus (bm ω) (ε * x) level)) '' Icc a b).Infinite := by
  filter_upwards [ae_peanosphere D, GMS4c.ae_bundle_finite_quantum_visits D] with ω hP hfinite
  intro ε x y a b hε hxy ha hb hab
  exact hP.left_contact_window hε hxy ha hb hab hfinite

/-- Almost surely, every strict right-contour window has an infinite continuous
contact image contained in both associated cells. -/
theorem ae_right_contact_window
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ) (x y : ℤ) (a b : ℝ),
      0 < ε → x + 1 < y → dWinLo ε (rCoord (bm ω)) x y < a →
      b < dWinHi ε (rCoord (bm ω)) x y → a < b →
      ContinuousOn (fun level => η ω (rhoMinus (bm ω) (ε * x) level)) (Icc a b) ∧
      (∀ level ∈ Icc a b,
        η ω (rhoMinus (bm ω) (ε * x) level) ∈
          (η ω) '' Icc (ε * ((x : ℝ) - 1)) (ε * x) ∩
          (η ω) '' Icc (ε * ((y : ℝ) - 1)) (ε * y)) ∧
      ((fun level => η ω (rhoMinus (bm ω) (ε * x) level)) '' Icc a b).Infinite := by
  filter_upwards [ae_peanosphere D, GMS4c.ae_bundle_finite_quantum_visits D] with ω hP hfinite
  intro ε x y a b hε hxy ha hb hab
  exact hP.right_contact_window hε hxy ha hb hab hfinite

end MatedCRTHarmonic.MoTInput
