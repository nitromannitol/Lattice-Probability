import Mathlib
import LatticeProb.LQG.LQGBallMassBoundsOfNegMoment
import LatticeProb.LQG.LQGNegMomentMain

/-!
# Ball-mass bounds of the whole-plane LQG measure

For every real `γ`, every probability space (or measurable space) of the universe `u` and every
whole-plane Gaussian free field model on it, the polynomial bounds on the mass of small balls of the
whole-plane `γ`-Liouville measure (Ding-Gwynne 2020, Lemma 3.8) hold.  For `0 < γ < 2` they follow
from the assembly out of the negative moments of the unit-ball mass of every order
(`wholePlaneLQGBallMassBoundsLP_of_negMoment`), which are supplied by `ballMassNegMoment_of_lt`;
outside `(0, 2)` the statement is vacuous.
-/

namespace LatticeProb.LQG

/-- **Ball-mass bounds of the whole-plane γ-LQG measure**, without hypothesis. -/
theorem wholePlaneLQGBallMassBoundsLP_holds.{u} {Ω : Type u} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    WholePlaneLQGBallMassBoundsLP P γ hC hcirc := by
  by_cases hγ : 0 < γ ∧ γ < 2
  · refine wholePlaneLQGBallMassBoundsLP_of_negMoment fun q hq =>
      ballMassNegMoment_of_lt hγ.1.ne' ?_ hq
    nlinarith [hγ.1, hγ.2]
  · exact wholePlaneLQGBallMassBoundsLP_of_single fun _ hγ0 hγ2 _ _ => absurd ⟨hγ0, hγ2⟩ hγ

end LatticeProb.LQG
