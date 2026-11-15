import LatticeProb.Topology.MeasurableVariableRadiusExitBall
import LatticeProb.Prob.IndependentRandomParameter

/-! # Exit-ball bounds at an independent random radius -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A uniform open-ball estimate at fixed positive radii gives a closed-ball
estimate at an independent positive random radius, with half the inner radius. -/
theorem measure_forward_variableBallExitFailure_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : Ω → ℝ} {Y : Ω → C(ℝ, EuclideanSpace ℝ (Fin d))}
    (hR : Measurable R) (hY : Measurable Y) (hind : IndepFun R Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < R ω) {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 0 < r →
      P {ω | ¬ (openExitTime (fun s (_ : Unit) => Y ω (0 + (s : ℝ)))
          (ball 0 r) () ≠ ⊤ ∧ ∃ z, ball z (ε * r) ⊆
          Y ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ Y ω t ∉ ball 0 r}))} ≤ p) :
    P {ω | ¬ (openExitTime (fun s (_ : Unit) => Y ω (0 + (s : ℝ)))
        (ball 0 (R ω)) () ≠ ⊤ ∧ 0 ≤ ε * R ω / 2 ∧ ∃ z,
        closedBall z (ε * R ω / 2) ⊆
        Y ω '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ Y ω t ∉ ball 0 (R ω)}))} ≤ p := by
  let E : Set (ℝ × C(ℝ, EuclideanSpace ℝ (Fin d))) :=
    {a | ¬ (openExitTime (fun s (_ : Unit) => a.2 (0 + (s : ℝ)))
        (ball 0 a.1) () ≠ ⊤ ∧ 0 ≤ ε * a.1 / 2 ∧ ∃ z,
        closedBall z (ε * a.1 / 2) ⊆
        a.2 '' Icc 0 (sInf {t : ℝ | 0 ≤ t ∧ a.2 t ∉ ball 0 a.1}))}
  have hE : MeasurableSet E := by
    exact (measurableSet_forward_variableBallExitTrace_contains_closedBall
      measurable_snd measurable_fst ((measurable_const.mul measurable_fst).div_const 2)).compl
  have hsections : ∀ r ∈ Ioi (0 : ℝ), P {ω | (r, Y ω) ∈ E} ≤ p := by
    intro r hr
    apply (measure_mono ?_).trans (hbound r hr)
    intro ω hfail hgood
    apply hfail
    obtain ⟨hfin, z, hz⟩ := hgood
    have hερ : 0 < ε * r := mul_pos hε hr
    exact ⟨hfin, (half_pos hερ).le, z,
      (closedBall_subset_ball (half_lt_self hερ)).trans hz⟩
  exact measure_mem_of_indepFun_le hR hY hind E hE (Ioi 0) measurableSet_Ioi hpos p hsections

end LatticeProb
