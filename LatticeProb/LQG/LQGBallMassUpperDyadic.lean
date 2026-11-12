import Mathlib
import LatticeProb.LQG.LQGBallMassUpperTail
import LatticeProb.LQG.LQGBallMassUpperLocal
import LatticeProb.LQG.GMCPointwiseMomentsLe
import LatticeProb.LQG.LQGBallMassLowerTail
import LatticeProb.LQG.LQGDyadicScaling
import LatticeProb.LQG.LQGBallMassGrid2

/-! # Upper tail of the mass of small balls from a positive moment

For the γ-LQG measure `μ` of a whole-plane GFF `h` and `z ∈ ℂ`, `j ∈ ℕ`, put `r = 2^{-j}`. Almost surely
`μ(B(z, r/4)) = r^{2+γ²/2} e^{γ h_r(z)} μ'(B(0, 1/4))` (`LQGDyadicScaling.ae_measure_ball_eq`), where `μ'` is the LQG
measure of the recentred field `h'`. Write `h_r(z) = h_1(z) + X` with `X = h_r(z) - h_1(z) = -h'_{1/r}(0)`: `X` is
`N(0, log (1/r))`, independent of `μ'(B(0,1/4))` (`IsWholePlaneGFF.indepFun_circle_measure_open`), and `h_1(z)` has a
Chernoff tail. A Markov bound of order `p` for `μ'(B(0,1/4))` then gives the single-ball upper tail.

The positive moment of the quarter-ball mass is the input `BallMassPosMoment γ p`
(`E[μ(B(0,1/4))^p] ≤ C` uniformly over the realisations; Rhodes-Vargas 2014, Thm. 2.12 for `p < 4/γ²`); it is a
hypothesis here, not proved in this module.

Main results:
* `upperTail_dyadic_single`: the estimate at one ball `B(z, 2^{-j}/4)`.
* `ballMassUpperTail_of_posMoment`: `BallMassUpperTail P γ μ` from `BallMassPosMoment γ (2/γ)`, with the exponent
  bookkeeping (`b < b'' < (2-γ)²/2`, `δ = ((2-γ)²/2 - b)/4`, `p = 2/γ`, tail exponent `2 + 2δ/γ > 2`).
-/

open MeasureTheory Filter Set Topology Metric ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

/-- **Positive moments of the quarter-ball mass.** `BallMassPosMoment γ p` states that there is a constant `C` with
`E[μ(B(0,1/4))^p] ≤ C` for the γ-LQG measure `μ` of every whole-plane GFF, on every probability space of the
universe `u`. This is the positive-moment estimate of Gaussian multiplicative chaos (Kahane 1985; Rhodes-Vargas 2014,
Thm. 2.12), taken here as a hypothesis. -/
def BallMassPosMoment.{u} (γ p : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ →
      ∫⁻ ω, (μ ω (ball 0 (1 / 4))) ^ p ∂P ≤ C

/-- **The upper tail at one ball.** For `‖z‖ ≤ 2`, `r = 2^{-j}`, and a moment bound `E[μ'(B(0,1/4))^p] ≤ C` for the LQG
measure of the recentred field,
`P(μ(B(z, r/4)) > r^b) ≤ 2 · 3^{t²} r^{tδ/γ} + C r^{p(2+γ²/2-b-δ) - p²γ²/2}`. -/
theorem upperTail_dyadic_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞} (j : ℕ) {z : ℂ}
    (hmom : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (μ' : Ω → Measure ℂ),
      IsWholePlaneGFF P hC' (recentredField hcirc j z) →
      IsLQGMeasure P γ (recentredField hcirc j z) μ' → ∫⁻ ω, (μ' ω (ball 0 (1 / 4))) ^ p ∂P ≤ C)
    (hz : ‖z‖ ≤ 2) {b δ t : ℝ} (ht : 0 ≤ t) :
    P {ω | ENNReal.ofReal (dyadicScale j ^ b) < μ ω (ball z (dyadicScale j * (1 / 4)))} ≤
      ENNReal.ofReal (2 * (3 : ℝ) ^ (t ^ 2) * dyadicScale j ^ (t * δ / γ)) +
        C * ENNReal.ofReal (dyadicScale j ^ (p * (2 + γ ^ 2 / 2 - b - δ) - p ^ 2 * γ ^ 2 / 2)) := by
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh j z
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  have hr0 : 0 < dyadicScale j := dyadicScale_pos' j
  have hr1 : dyadicScale j ≤ 1 := dyadicScale_le_one' j
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hM' : AEMeasurable (fun ω => μ' ω (ball 0 (1 / 4))) P :=
    aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh' (isLQGMeasureOfField_zero hμ')
      (lqgLocality_of_gff P γ 0 hC' (recentredField hcirc j z)) _ measurableSet_ball
  have hind : IndepFun (fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z)
      (fun ω => μ' ω (ball 0 (1 / 4))) P := by
    have h0 := hh'.indepFun_circle_measure_open hγ0 hγ2 hμ' (R := (dyadicScale j)⁻¹)
      ((one_le_inv₀ hr0).2 hr1) (U := ball 0 (1 / 4)) isOpen_ball
      (ball_subset_ball (by norm_num))
    have e : (fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z) =
        (fun x : ℝ => -x) ∘ (fun ω => recentredField hcirc j z ω (dyadicScale j)⁻¹ 0) := by
      funext ω
      simp only [Function.comp, recentredField, mul_inv_cancel₀ hr0.ne', mul_zero, zero_add]
      ring
    rw [e]
    exact h0.comp (φ := fun x : ℝ => -x) (ψ := id) measurable_neg measurable_id
  have hmass : ∀ᵐ ω ∂P, μ ω (ball z (dyadicScale j * (1 / 4))) ≤
      ENNReal.ofReal (dyadicScale j ^ (2 + γ ^ 2 / 2) *
        Real.exp (γ * (hcirc ω 1 z + (hcirc ω (dyadicScale j) z - hcirc ω 1 z)))) *
        μ' ω (ball 0 (1 / 4)) := by
    filter_upwards [ae_measure_ball_eq hγ0 hμ j z hμ'] with ω hω
    rw [hω _ (by norm_num), add_sub_cancel]
    exact le_rfl
  have hv : (((Real.log (1 / dyadicScale j)).toNNReal : ℝ≥0) : ℝ) ≤ -Real.log (dyadicScale j) := by
    rw [Real.coe_toNNReal', one_div, Real.log_inv]
    exact max_le le_rfl (neg_nonneg.2 (Real.log_nonpos hr0.le hr1))
  exact upperTail_single (X := fun ω => hcirc ω (dyadicScale j) z - hcirc ω 1 z)
    (Y := fun ω => hcirc ω 1 z) (Mass := fun ω => μ ω (ball z (dyadicScale j * (1 / 4))))
    (M' := fun ω => μ' ω (ball 0 (1 / 4))) hr0 hp (hh.hasLaw_incr_le hr0 hr1 z) hv hM' hind
    (hmom hC' μ' hh' hμ') hmass (hh.measure_circle_one_gt_le hz hr0 hr1 hγ0 ht)

/-- `2^{-(k+2)} = 2^{-k} / 4`. -/
theorem dyadicScale_add_two (k : ℕ) : dyadicScale (k + 2) = dyadicScale k * (1 / 4) := by
  rw [dyadicScale_succ_eq_half (k + 1), dyadicScale_succ_eq_half k]
  ring

/-- The exponent bookkeeping of the upper tail: with `p = 2/γ`, `b'' = (b + a)/2`, `δ = (a - b)/4`, `a = (2-γ)²/2`,
the exponent `p(2 + γ²/2 - b'' - δ) - p²γ²/2` equals `2 + 2δ/γ`. -/
theorem upper_exponent_eq {γ b δ : ℝ} (hγ : 0 < γ) (hδ : δ = ((2 - γ) ^ 2 / 2 - b) / 4) :
    (2 / γ) * (2 + γ ^ 2 / 2 - (b + (2 - γ) ^ 2 / 2) / 2 - δ) - (2 / γ) ^ 2 * γ ^ 2 / 2 =
      2 + 2 * δ / γ := by
  subst hδ
  field_simp
  ring

/-- **Upper tail of the mass of small balls from a positive moment.** If `E[μ(B(0,1/4))^{2/γ}] ≤ C` uniformly over the
whole-plane GFFs and their LQG measures (`BallMassPosMoment γ (2/γ)`), then the single-ball upper tail
`BallMassUpperTail P γ μ` holds: for `b < (2-γ)²/2` the probability that a ball of radius `r` centred in the unit
square has mass larger than `r^b` is at most `C' r^θ` with `θ > 2`. -/
theorem ballMassUpperTail_of_posMoment.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hPos : BallMassPosMoment.{u} γ (2 / γ)) : BallMassUpperTail P γ μ := by
  obtain ⟨C, hCm⟩ := hPos
  refine ballMassUpperTail_of_dyadic fun b hb => ?_
  obtain ⟨b'', hb''⟩ : ∃ b'' : ℝ, b'' = (b + (2 - γ) ^ 2 / 2) / 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((2 - γ) ^ 2 / 2 - b) / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hp0 : 0 < 2 / γ := by positivity
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 + 2 * δ / γ := ⟨_, rfl⟩
  have hE2 : 2 < E := by
    have : 0 < 2 * δ / γ := by positivity
    rw [hE]; linarith
  have hE0 : 0 < E := by linarith
  have hexp : (2 / γ) * (2 + γ ^ 2 / 2 - b'' - δ) - (2 / γ) ^ 2 * γ ^ 2 / 2 = E := by
    rw [hb'', hE]; exact upper_exponent_eq hγ0 hδ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = γ * E / δ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htE : t * δ / γ = E := by rw [ht]; field_simp
  have hbb : 0 < b'' - b := by rw [hb'']; linarith
  obtain ⟨r₁, hr₁, H1⟩ :=
    exists_pos_forall_of_eventually_nhdsGT (eventually_mul_rpow_lt_one ((4 : ℝ) ^ b) hbb)
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, dyadicScale k₀ < r₁ :=
    exists_pow_lt_of_lt_one hr₁ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨E, hE2, (2 * (3 : ℝ) ^ (t ^ 2) + C) * (4 : ℝ) ^ E, k₀ + 2, ?_⟩
  intro z hz j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hr : dyadicScale k < r₁ := lt_of_le_of_lt (dyadicScale_le_of_le (by omega : k₀ ≤ k)) hk₀
  have hr0 : 0 < dyadicScale k := dyadicScale_pos' k
  have hz2 : ‖z‖ ≤ 2 := by
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.1 hz
    have a1 : |z.re| ≤ 1 := abs_le.2 ⟨by linarith [h1.1], h1.2⟩
    have a2 : |z.im| ≤ 1 := abs_le.2 ⟨by linarith [h2.1], h2.2⟩
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ b := by positivity
  have h41 : (4 : ℝ) ^ b * (1 / 4 : ℝ) ^ b = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hsmall : dyadicScale k ^ (b'' - b) ≤ (1 / 4 : ℝ) ^ b := by
    refine le_of_mul_le_mul_left ?_ h4
    rw [h41]
    exact (H1 _ hr0 hr).le
  have hsub : {ω | ENNReal.ofReal (dyadicScale (k + 2) ^ b) < μ ω (ball z (dyadicScale (k + 2)))} ⊆
      {ω | ENNReal.ofReal (dyadicScale k ^ b'') <
        μ ω (ball z (dyadicScale k * (1 / 4)))} := by
    intro ω hω
    have hω' : ENNReal.ofReal (dyadicScale (k + 2) ^ b) < μ ω (ball z (dyadicScale (k + 2))) := hω
    rw [dyadicScale_add_two] at hω'
    show ENNReal.ofReal (dyadicScale k ^ b'') < μ ω (ball z (dyadicScale k * (1 / 4)))
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hω'
    calc dyadicScale k ^ b'' = dyadicScale k ^ b * dyadicScale k ^ (b'' - b) := by
          rw [← Real.rpow_add hr0]; congr 1; ring
      _ ≤ dyadicScale k ^ b * (1 / 4 : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hr0.le _)
      _ = (dyadicScale k * (1 / 4)) ^ b := (Real.mul_rpow hr0.le (by norm_num)).symm
  refine (measure_mono hsub).trans ?_
  refine (upperTail_dyadic_single hγ0 hγ2 hh hμ hp0 k (C := (C : ℝ≥0∞))
    (fun hC' μ' h h' => hCm Ω P hC' _ μ' h h') hz2 (b := b'') (δ := δ) ht0).trans ?_
  rw [htE, hexp, dyadicScale_add_two]
  have h41E : (4 : ℝ) ^ E * (1 / 4 : ℝ) ^ E = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e1 : (2 * (3 : ℝ) ^ (t ^ 2) + C) * (4 : ℝ) ^ E * (dyadicScale k * (1 / 4)) ^ E =
      2 * (3 : ℝ) ^ (t ^ 2) * dyadicScale k ^ E + C * dyadicScale k ^ E := by
    calc (2 * (3 : ℝ) ^ (t ^ 2) + C) * (4 : ℝ) ^ E * (dyadicScale k * (1 / 4)) ^ E
        = (2 * (3 : ℝ) ^ (t ^ 2) + C) * dyadicScale k ^ E * ((4 : ℝ) ^ E * (1 / 4 : ℝ) ^ E) := by
          rw [Real.mul_rpow hr0.le (by norm_num)]; ring
      _ = _ := by rw [h41E]; ring
  rw [e1, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

end LatticeProb.LQG
