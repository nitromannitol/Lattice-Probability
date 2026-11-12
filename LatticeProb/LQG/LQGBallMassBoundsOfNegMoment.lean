import Mathlib
import LatticeProb.LQG.LQGMassFatou
import LatticeProb.LQG.LQGBallMassUpperDyadic
import LatticeProb.LQG.LQGBallMassLowerTail

/-!
# Ball-mass bounds of the whole-plane LQG measure from negative moments

Ding-Gwynne (Comm. Math. Phys. 374 (2020), arXiv:1807.01072, Lemma 3.8) bound the γ-LQG mass of every Euclidean
ball of radius `ε ^ β` centred in the unit square, with polynomially high probability: from below by `ε` when
`β < 2 / (2 + γ)²`, from above by `ε` when `β > 2 / (2 - γ)²`. The upper bound follows from the positive moment of
order `2 / γ` of the ball mass (`ballMassPosMoment_of_lt`, Kahane 1985), the lower bound from the negative moments of
every order (`BallMassNegMoment`, Robert-Vargas 2010; Rhodes-Vargas 2014, Thm. 2.12).

`wholePlaneLQGBallMassBoundsLP_of_negMoment` assembles `WholePlaneLQGBallMassBoundsLP` from the negative moments of
every order, which are its only hypothesis.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

/-- An LQG measure of the field with zero added function is an LQG measure of the whole-plane GFF itself. -/
theorem isLQGMeasure_of_isLQGMeasureOfField_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    IsLQGMeasure P γ hcirc μ := by
  have : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  unfold IsLQGMeasureOfField at hμ
  rw [this] at hμ
  exact hμ

/-- **Ball-mass bounds of the whole-plane γ-LQG measure** (Ding-Gwynne 2020, Lemma 3.8) from the negative moments of
the unit-ball mass of every order. The upper bound uses the positive moment of order `2 / γ`, which holds for
`0 < γ < 2`. -/
theorem wholePlaneLQGBallMassBoundsLP_of_negMoment.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hN : ∀ q : ℝ, 0 < q → BallMassNegMoment.{u} γ q) :
    WholePlaneLQGBallMassBoundsLP P γ hC hcirc := by
  refine wholePlaneLQGBallMassBoundsLP_of_single fun hh hγ0 hγ2 μ hμ => ?_
  have hμ' : IsLQGMeasure P γ hcirc μ := isLQGMeasure_of_isLQGMeasureOfField_zero hμ
  have hPos : BallMassPosMoment.{u} γ (2 / γ) := by
    refine ballMassPosMoment_of_lt hγ0.ne' ?_ ?_
    · rw [le_div_iff₀ hγ0]; linarith
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hγ0]; nlinarith
  exact ⟨ballMassUpperTail_of_posMoment hγ0 hγ2 hh hμ' hPos,
    ballMassLowerTail_of_negMoment hγ0 hγ2 hh hμ' hN⟩

end LatticeProb.LQG
