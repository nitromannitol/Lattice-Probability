import LatticeProb.Prob.BrownianExit
import LatticeProb.Prob.GaussianFreezing

/-! # A fixed-time Brownian ball bound -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb

/-- A fixed-time ball probability is bounded using a single Gaussian coordinate.
The estimate is uniform in the starting point. -/
theorem brownian_ball_marginal_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : EuclideanSpace ℝ (Fin 2)}
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 2)}
    (hB : IsBrownianSpace 2 x B P) {t : ℝ≥0} (ht : t ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | B t ω ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r} ≤
      (2 * Real.sqrt 2 * r) / Real.sqrt (2 * Real.pi * t) := by
  let i : Fin 2 := 0
  let W : Ω → ℝ := fun ω => Real.sqrt 2 * (B t ω i - x i)
  let a : ℝ := -Real.sqrt 2 * x i
  let q : ℝ := Real.sqrt 2 * r
  have hsq : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hq : 0 ≤ q := mul_nonneg hsq hr
  have hlaw : HasLaw W (gaussianReal 0 t) P := (hB.coord i).hasLaw_eval t
  have hsub : {ω | B t ω ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r} ⊆
      {ω | W ω ∈ Icc (a - q) (a + q)} := by
    intro ω hω
    have hn : ‖B t ω‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hω
    have hi : |B t ω i| ≤ r := (PiLp.norm_apply_le (B t ω) i).trans (le_of_lt hn)
    have hi' := abs_le.mp hi
    change a - q ≤ W ω ∧ W ω ≤ a + q
    dsimp [a, q, W]
    constructor <;> nlinarith
  have hbound : P {ω | B t ω ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r} ≤
      ENNReal.ofReal ((2 * Real.sqrt 2 * r) / Real.sqrt (2 * Real.pi * t)) := by
    calc
      _ ≤ P {ω | W ω ∈ Icc (a - q) (a + q)} := measure_mono hsub
      _ = gaussianReal 0 t (Icc (a - q) (a + q)) := hlaw.measure_eq measurableSet_Icc
      _ ≤ ENNReal.ofReal (((a + q) - (a - q)) / Real.sqrt (2 * Real.pi * t)) :=
        gaussianReal_Icc_le ht (by linarith)
      _ = _ := by congr 1; congr 1; dsimp [q]; ring
  have hnonneg : 0 ≤ (2 * Real.sqrt 2 * r) / Real.sqrt (2 * Real.pi * t) := by positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hnonneg)

end LatticeProb
