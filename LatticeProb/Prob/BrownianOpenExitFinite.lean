module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianFiniteExit.lean.
-/

public import LatticeProb.Prob.BrownianOpenExit
public import LatticeProb.Prob.BrownianExit
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Finiteness of the open-set exit time of Brownian motion

For Brownian motion `B` on `EuclideanSpace ℝ (Fin d)` with `1 ≤ d`, the first exit time
`openExitTime B U` from a bounded set `U` is almost surely finite. The probability that it exceeds
`(n + 1)^2` is bounded uniformly in the starting point in `U` and in the law, and tends to zero.

Only one coordinate and its Gaussian marginal laws are needed. At the square times `(n + 1)^2`,
the coordinate lies in any fixed bounded interval with probability tending to zero. This rules out
remaining in a bounded set forever.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

private lemma standardGaussian_measure_shrinking_interval_tendsto_zero
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ ↦ gaussianReal 0 1 {x : ℝ | |x| ≤ R / (n + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let S : ℕ → Set ℝ := fun n ↦ {x | |x| ≤ R / (n + 1)}
  have hmeas (n : ℕ) : MeasurableSet (S n) :=
    (isClosed_le continuous_abs continuous_const).measurableSet
  have hanti : Antitone S := by
    intro n m hnm x hx
    exact hx.trans (div_le_div_of_nonneg_left hR (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hinter : (⋂ n, S n) = {0} := by
    ext x
    simp only [mem_iInter, S, mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxzero
      have hxpos : 0 < |x| := abs_pos.mpr hxzero
      obtain ⟨n, hn⟩ := exists_nat_gt (R / |x|)
      have hlarge : R < (n : ℝ) * |x| := (div_lt_iff₀ hxpos).mp hn
      have hsmall : |x| * ((n : ℝ) + 1) ≤ R :=
        (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp (hx n)
      nlinarith
    · rintro rfl n
      simpa only [abs_zero] using div_nonneg hR (by positivity : 0 ≤ (n : ℝ) + 1)
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hlim := tendsto_measure_iInter_atTop
    (fun n ↦ (hmeas n).nullMeasurableSet (μ := gaussianReal 0 1)) hanti
    ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, measure_singleton, Function.comp_def, S] using hlim

/-- The probability that a centred Gaussian of variance `(n + 1)^2` lies in a fixed bounded
interval tends to zero as `n → ∞`. -/
theorem gaussian_square_time_measure_bounded_tendsto_zero {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ ↦ gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2)
      {x : ℝ | |x| ≤ R}) atTop (𝓝 (0 : ℝ≥0∞)) := by
  have heq (n : ℕ) : gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ R} =
      gaussianReal 0 1 {x : ℝ | |x| ≤ R / (n + 1)} := by
    have hc : 0 < (n : ℝ) + 1 := by positivity
    have hmap : (gaussianReal 0 1).map (fun x : ℝ ↦ ((n : ℝ) + 1) * x) =
        gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) := by
      rw [gaussianReal_map_const_mul, mul_zero, mul_one]
      congr 1
    rw [← hmap, Measure.map_apply (by fun_prop)
      (isClosed_le continuous_abs continuous_const).measurableSet]
    congr 1
    ext x
    simp only [mem_preimage, mem_setOf_eq, abs_mul, abs_of_pos hc, le_div_iff₀ hc]
    rw [mul_comm]
  simp_rw [heq]
  exact standardGaussian_measure_shrinking_interval_tendsto_zero hR

/-- A pre-Brownian process is almost surely not bounded at all square times.
This uses Gaussian marginals and no independence or stopping theorem. -/
theorem preBrownian_ae_not_bounded_square_times {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, ¬ ∀ n : ℕ, |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R := by
  have hbound (n : ℕ) :
      P {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} ≤
        gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {x : ℝ | |x| ≤ R} := by
    calc
      _ ≤ P {ω | |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R} :=
        measure_mono (show {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} ⊆
          {ω | |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ R} from fun ω hω ↦ hω n)
      _ = _ := (hB.hasLaw_eval _).measure_eq
        (isClosed_le continuous_abs continuous_const).measurableSet
  have hzero : P {ω | ∀ m : ℕ, |B (((m : ℝ≥0) + 1) ^ 2) ω| ≤ R} = 0 :=
    le_antisymm (ge_of_tendsto' (gaussian_square_time_measure_bounded_tendsto_zero hR)
      hbound) bot_le
  simpa only [ae_iff, not_not] using hzero

/-- A coordinate of a difference of two vectors of `EuclideanSpace ℝ (Fin d)` is at most the sum
of their norms. -/
private lemma abs_coord_sub_le {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |v i - w i| ≤ ‖v‖ + ‖w‖ := by
  have h : ∀ u : EuclideanSpace ℝ (Fin d), |u i| ≤ ‖u‖ := fun u ↦ by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le u i
  exact (abs_sub _ _).trans (add_le_add (h v) (h w))

/-- The scaled coordinate `√d (v i - x i)` is bounded by `√d c` once `‖v‖ + ‖x‖ ≤ c`. -/
private lemma abs_sqrt_coord_sub_le {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (i : Fin d) {c : ℝ}
    (hc : ‖v‖ + ‖x‖ ≤ c) :
    |Real.sqrt d * (v i - x i)| ≤ Real.sqrt d * c := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left ((abs_coord_sub_le v x i).trans hc) (Real.sqrt_nonneg _)

/-- Brownian motion on `EuclideanSpace ℝ (Fin d)` with `1 ≤ d` started at `x` leaves a bounded
set almost surely: its open-set exit time is finite almost surely. -/
theorem ae_openExitTime_ne_top {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {P : Measure Ω} {U : Set (EuclideanSpace ℝ (Fin d))} (hd : 1 ≤ d)
    (hB : IsBrownianSpace d x B P) (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, openExitTime B U ω ≠ ⊤ := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  let i : Fin d := ⟨0, hd⟩
  have hnot := preBrownian_ae_not_bounded_square_times
    (hB.coord i).toIsPreBrownianReal
    (R := Real.sqrt d * (R + ‖x‖))
    (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hRpos.le (norm_nonneg _)))
  filter_upwards [hnot] with ω hω
  intro hnever
  apply hω
  intro n
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  have hin : B t ω ∈ U := by
    by_contra hout
    have hle : openExitTime B U ω ≤ (t : ℝ≥0∞) := openExitTime_le_of_not_mem hout
    rw [hnever] at hle
    exact ENNReal.coe_ne_top (top_le_iff.mp hle)
  exact abs_sqrt_coord_sub_le x (B t ω) i (add_le_add (hR _ hin) le_rfl)

/-- For Brownian motion started in `U`, the probability that the open-set exit time exceeds
`(n + 1)^2` is at most the Gaussian probability that a coordinate of variance `(n + 1)^2` lies in
`[-2 √d R, 2 √d R]`, where `R` bounds the norms of the points of `U`. Before the exit time the
path stays in `U`, which gives the bound on the scaled coordinate. -/
theorem measure_lateExit_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {x : EuclideanSpace ℝ (Fin d)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    {P : Measure Ω} (hd : 1 ≤ d) (hB : IsBrownianSpace d x B P)
    {U : Set (EuclideanSpace ℝ (Fin d))} {R : ℝ} (hR : ∀ y ∈ U, ‖y‖ ≤ R)
    (hx : x ∈ U) (n : ℕ) :
    P {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < openExitTime B U ω} ≤
      gaussianReal 0 (((n : ℝ≥0) + 1) ^ 2) {y : ℝ | |y| ≤ 2 * Real.sqrt d * R} := by
  let i : Fin d := ⟨0, hd⟩
  let t : ℝ≥0 := ((n : ℝ≥0) + 1) ^ 2
  calc
    _ ≤ P {ω | |Real.sqrt d * (B t ω i - x i)| ≤ 2 * Real.sqrt d * R} := by
      apply measure_mono
      intro ω hω
      have hin : B t ω ∈ U := mem_of_lt_openExitTime hω
      show |Real.sqrt d * (B t ω i - x i)| ≤ 2 * Real.sqrt d * R
      calc
        _ ≤ Real.sqrt d * (R + R) :=
          abs_sqrt_coord_sub_le x (B t ω) i (add_le_add (hR _ hin) (hR _ hx))
        _ = 2 * Real.sqrt d * R := by ring
    _ = _ := ((hB.coord i).toIsPreBrownianReal.hasLaw_eval t).measure_eq
      (p := fun y : ℝ ↦ |y| ≤ 2 * Real.sqrt d * R)
      (isClosed_le continuous_abs continuous_const).measurableSet

section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Brownian exit tails vanish uniformly over starting points and laws. For every positive `ε`,
eventually in `n` the probability that the open-set exit time exceeds `(n + 1)^2` is at most `ε`,
for every Brownian motion on `EuclideanSpace ℝ (Fin d)` with `1 ≤ d` started in `U`. -/
theorem openExitTime_uniform_tail {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hd : 1 ≤ d)
    (hU : Bornology.IsBounded U) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Measure Ω) (x : EuclideanSpace ℝ (Fin d))
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)), IsBrownianSpace d x B P → x ∈ U →
      P {ω | ((((n : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) < openExitTime B U ω} ≤ ε := by
  obtain ⟨R, hRpos, hR⟩ := hU.exists_pos_norm_le
  have hlim := gaussian_square_time_measure_bounded_tendsto_zero
    (show 0 ≤ 2 * Real.sqrt d * R from
      mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hRpos.le)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro P x B hB hx
  exact (measure_lateExit_le hd hB hR hx n).trans hn.le

end

namespace BrownianOpenExitFiniteExample

/-- The one-dimensional square-time estimate at radius `R = 1` holds for every pre-Brownian
process: it is not almost surely bounded by `1` at all square times. -/
theorem preBrownian_ae_not_bounded_unit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ¬ ∀ n : ℕ, |B (((n : ℝ≥0) + 1) ^ 2) ω| ≤ 1 :=
  preBrownian_ae_not_bounded_square_times hB zero_le_one

/-- The late-exit bound at `n = 0` for Brownian motion on `EuclideanSpace ℝ (Fin 1)` started in
the open unit ball, with `R = 1` bounding the norms of its points. The hypotheses are satisfiable:
the ball has norm at most `1`, and its centre lies in it. -/
theorem measure_lateExit_le_unitBall {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {x : EuclideanSpace ℝ (Fin 1)} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 1)}
    (hB : IsBrownianSpace 1 x B P) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :
    P {ω | (((((0 : ℕ) : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ≥0∞) <
        openExitTime B (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ω} ≤
      gaussianReal 0 ((((0 : ℕ) : ℝ≥0) + 1) ^ 2)
        {y : ℝ | |y| ≤ 2 * Real.sqrt ((1 : ℕ) : ℝ) * 1} :=
  measure_lateExit_le le_rfl hB (fun _ hy ↦ (mem_ball_zero_iff.mp hy).le) hx 0

end BrownianOpenExitFiniteExample

end LatticeProb
