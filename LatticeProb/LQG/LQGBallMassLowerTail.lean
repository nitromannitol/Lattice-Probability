import Mathlib
import LatticeProb.LQG.LQGBallMassGrid2
import LatticeProb.LQG.LQGCircleTail
import LatticeProb.LQG.LQGDyadicScaling
import LatticeProb.LQG.LQGMeasureSquare
import LatticeProb.LQG.LQGMeasureLocality2
import LatticeProb.LQG.GMCDyadicLimit

/-! # Lower tail of the mass of small balls from negative moments

For the γ-LQG measure `μ` of a whole-plane GFF `h` (`0 < γ < 2`), the mass of a small ball satisfies
`μ(B(z, r)) = r^{γ Q} e^{γ h_r(z)} μ'(B(0, 1))` almost surely, where `μ'` is the LQG measure of the field
recentred and dilated at `(z, r)` (`LQGDyadicScaling.ae_measure_ball_eq`), `h_r(z)` is Gaussian with variance at most
`log (1/r) + 2 log 3` (`IsWholePlaneGFF.measure_circle_le_neg`), and `μ'(B(0,1))` has the law of the unit-ball mass.
Hence the lower tail of the ball mass follows from a Gaussian lower tail for `h_r(z)` and a Markov bound for the
negative moments of the unit-ball mass.

The negative moments of the unit-ball mass are the input `BallMassNegMoment γ q`
(`E[μ(B(0,1))^{-q}] ≤ C` uniformly over the realisations); it is a hypothesis here, not proved in this module.

Main results:
* `measure_lt_le_of_lintegral_rpow_neg`: Markov's inequality for a negative moment.
* `lowerTail_single`: the elementary estimate at one ball.
* `lowerTail_dyadic_of_negMoment`: the dyadic lower-tail estimate with the exact hypothesis shape of
  `ballMassLowerTail_of_dyadic`, from the negative moments `BallMassNegMoment γ q` for all `q > 0`.
* `ballMassLowerTail_of_negMoment`: `BallMassLowerTail P γ μ`.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LatticeProb.LQG.LQGDyadicScaling

/-- **Markov's inequality for a negative moment.** If `∫⁻ f^{-q} ≤ C` then `P(f < s) ≤ C s^q`. -/
theorem measure_lt_le_of_lintegral_rpow_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {q : ℝ} (hq : 0 < q) {C : ℝ≥0∞}
    (hmom : ∫⁻ ω, f ω ^ (-q) ∂P ≤ C) {s : ℝ} (hs : 0 < s) :
    P {ω | f ω < ENNReal.ofReal s} ≤ C * ENNReal.ofReal (s ^ q) := by
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs).ne'
  have hsT : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpos : (ENNReal.ofReal s) ^ q ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hs0) hsT).ne'
  have hfin : (ENNReal.ofReal s) ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq.le hsT
  have hmeas : AEMeasurable (fun ω => f ω ^ (-q)) P :=
    hf.pow_const (-q)
  have h1 := mul_meas_ge_le_lintegral₀ hmeas (((ENNReal.ofReal s) ^ q)⁻¹)
  have hsub : {ω | f ω < ENNReal.ofReal s} ⊆ {ω | ((ENNReal.ofReal s) ^ q)⁻¹ ≤ f ω ^ (-q)} := by
    intro ω (hω : f ω < ENNReal.ofReal s)
    show ((ENNReal.ofReal s) ^ q)⁻¹ ≤ f ω ^ (-q)
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hω.le hq.le)
  calc P {ω | f ω < ENNReal.ofReal s}
      = (ENNReal.ofReal s) ^ q * (((ENNReal.ofReal s) ^ q)⁻¹ * P {ω | f ω < ENNReal.ofReal s}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hpos hfin, one_mul]
    _ ≤ (ENNReal.ofReal s) ^ q *
          (((ENNReal.ofReal s) ^ q)⁻¹ * P {ω | ((ENNReal.ofReal s) ^ q)⁻¹ ≤ f ω ^ (-q)}) := by
        gcongr
    _ ≤ (ENNReal.ofReal s) ^ q * C := mul_le_mul_right (h1.trans hmom) _
    _ = C * ENNReal.ofReal (s ^ q) := by rw [mul_comm, ENNReal.ofReal_rpow_of_pos hs]

/-- **Negative moments of the unit-ball mass.** `BallMassNegMoment γ q` states that there is a constant `C` with
`E[μ(B(0,1))^{-q}] ≤ C` for the γ-LQG measure `μ` of every whole-plane GFF, on every probability space of the
universe `u`. This is the negative-moment estimate of Gaussian multiplicative chaos (Kahane 1985; Robert-Vargas 2010;
Rhodes-Vargas 2014, Thm. 2.12), taken here as a hypothesis. -/
def BallMassNegMoment.{u} (γ q : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ hcirc μ → ∫⁻ ω, (μ ω (ball 0 1)) ^ (-q) ∂P ≤ C

theorem isLQGMeasureOfField_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasure P γ hcirc μ) :
    IsLQGMeasureOfField P γ 0 hcirc μ := by
  have : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  unfold IsLQGMeasureOfField
  rw [this]
  exact hμ

/-- Markov's inequality for the unit-ball mass of the LQG measure of a whole-plane GFF. -/
theorem measure_ball_zero_lt_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {q : ℝ} (hq : 0 < q) {C : ℝ≥0∞} (hmom : ∫⁻ ω, (μ ω (ball 0 1)) ^ (-q) ∂P ≤ C) {s : ℝ}
    (hs : 0 < s) :
    P {ω | μ ω (ball 0 1) < ENNReal.ofReal s} ≤ C * ENNReal.ofReal (s ^ q) := by
  have hα : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hmeas := aemeasurable_lqgMeasure_borel hγ0 hγ2 hα hh (isLQGMeasureOfField_zero hμ)
    (lqgLocality_of_gff P γ 0 hC hcirc) (ball 0 1) measurableSet_ball
  exact measure_lt_le_of_lintegral_rpow_neg hmeas hq hmom hs

/-- The exponent arithmetic of the lower tail: on `{h_r(z) > τ log r}` and `{m ≥ r^δ}` the ball mass
`r^{2+γ²/2} e^{γ X} m` is at least `r^c`, where `c = 2 + γ²/2 + γτ + δ`. -/
theorem ofReal_rpow_le_of_gt {γ r X δ τ c : ℝ} {M m : ℝ≥0∞} (hr0 : 0 < r) (hγ0 : 0 < γ)
    (hc : c = (2 + γ ^ 2 / 2) + γ * τ + δ) (hX : τ * Real.log r < X)
    (hm : ENNReal.ofReal (r ^ δ) ≤ m)
    (hM : M = ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X)) * m) :
    ENNReal.ofReal (r ^ c) ≤ M := by
  have hexp : r ^ (γ * τ) ≤ Real.exp (γ * X) := by
    rw [Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    nlinarith
  have hF : r ^ c ≤ r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X) * r ^ δ := by
    calc r ^ c = r ^ (2 + γ ^ 2 / 2) * r ^ (γ * τ) * r ^ δ := by
          rw [← Real.rpow_add hr0, ← Real.rpow_add hr0, hc]
      _ ≤ r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X) * r ^ δ := by
          have h1 : 0 ≤ r ^ (2 + γ ^ 2 / 2) := Real.rpow_nonneg hr0.le _
          have h2 : 0 ≤ r ^ δ := Real.rpow_nonneg hr0.le _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp h1) h2
  rw [hM]
  calc ENNReal.ofReal (r ^ c) ≤ ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X) * r ^ δ) :=
        ENNReal.ofReal_le_ofReal hF
    _ = ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X)) * ENNReal.ofReal (r ^ δ) :=
        ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr0.le _) (Real.exp_pos _).le)
    _ ≤ ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * X)) * m := mul_le_mul_right hm _

/-- **Lower tail at one ball, from the scaling relation.** Suppose `0 < r ≤ 1`, `‖z‖ ≤ 2`, and almost surely the
mass `M` of `B(z, r)` equals `r^{2+γ²/2} e^{γ h_r(z)} m` with `P(m < r^δ) ≤ C_N r^3`. If
`c = 2 + γ²/2 + γτ + δ`, `τ > 2`, `θ ≤ τ²/2` and `θ ≤ 3`, then `P(M < r^c) ≤ (2·3^{τ²} + C_N) r^θ`. -/
theorem lowerTail_single {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ r δ τ θ c : ℝ} {z : ℂ}
    {M m : Ω → ℝ≥0∞} {CN : ℝ≥0} (hr0 : 0 < r) (hr1 : r ≤ 1) (hz : ‖z‖ ≤ 2) (hγ0 : 0 < γ)
    (hτ : 0 ≤ τ) (hc : c = (2 + γ ^ 2 / 2) + γ * τ + δ) (hθ1 : θ ≤ τ ^ 2 / 2) (hθ2 : θ ≤ 3)
    (hM : ∀ᵐ ω ∂P, M ω = ENNReal.ofReal (r ^ (2 + γ ^ 2 / 2) * Real.exp (γ * hcirc ω r z)) * m ω)
    (hm : P {ω | m ω < ENNReal.ofReal (r ^ δ)} ≤ CN * ENNReal.ofReal (r ^ (3 : ℝ))) :
    P {ω | M ω < ENNReal.ofReal (r ^ c)} ≤
      ENNReal.ofReal ((2 * (3 : ℝ) ^ (τ ^ 2) + CN) * r ^ θ) := by
  have hPA := hh.measure_circle_le_neg hr0 hr1 hz hτ
  have hsub : {ω | M ω < ENNReal.ofReal (r ^ c)} ≤ᵐ[P]
      ({ω | hcirc ω r z ≤ -(τ * -Real.log r)} ∪ {ω | m ω < ENNReal.ofReal (r ^ δ)} : Set Ω) := by
    filter_upwards [hM] with ω hω hev
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    have hA : ¬ hcirc ω r z ≤ -(τ * -Real.log r) := hnot.1
    have hB : ¬ m ω < ENNReal.ofReal (r ^ δ) := hnot.2
    have hX : τ * Real.log r < hcirc ω r z := by
      push Not at hA
      linarith
    have hm' : ENNReal.ofReal (r ^ δ) ≤ m ω := not_lt.1 hB
    exact absurd (show M ω < ENNReal.ofReal (r ^ c) from hev)
      (not_lt.2 (ofReal_rpow_le_of_gt hr0 hγ0 hc hX hm' hω))
  have ha : r ^ (τ ^ 2 / 2) ≤ r ^ θ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hθ1
  have hb : r ^ (3 : ℝ) ≤ r ^ θ := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hθ2
  have h3 : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ (τ ^ 2) := by positivity
  have e1 : (CN : ℝ≥0∞) * ENNReal.ofReal (r ^ (3 : ℝ)) = ENNReal.ofReal (CN * r ^ (3 : ℝ)) := by
    rw [ENNReal.ofReal_mul CN.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  calc P {ω | M ω < ENNReal.ofReal (r ^ c)}
      ≤ P ({ω | hcirc ω r z ≤ -(τ * -Real.log r)} ∪ {ω | m ω < ENNReal.ofReal (r ^ δ)}) :=
        measure_mono_ae hsub
    _ ≤ P {ω | hcirc ω r z ≤ -(τ * -Real.log r)} + P {ω | m ω < ENNReal.ofReal (r ^ δ)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2)) +
          ENNReal.ofReal (CN * r ^ (3 : ℝ)) := add_le_add hPA (hm.trans e1.le)
    _ = ENNReal.ofReal (2 * (3 : ℝ) ^ (τ ^ 2) * r ^ (τ ^ 2 / 2) + CN * r ^ (3 : ℝ)) :=
        (ENNReal.ofReal_add (mul_nonneg h3 (Real.rpow_nonneg hr0.le _))
          (mul_nonneg CN.coe_nonneg (Real.rpow_nonneg hr0.le _))).symm
    _ ≤ ENNReal.ofReal ((2 * (3 : ℝ) ^ (τ ^ 2) + CN) * r ^ θ) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left ha h3,
          mul_le_mul_of_nonneg_left hb (CN.coe_nonneg : (0 : ℝ) ≤ CN)]

/-- **Dyadic lower tail of the ball mass from negative moments.** If `E[μ(B(0,1))^{-q}]` is bounded uniformly for
every `q > 0` (`BallMassNegMoment`), then for every `c > (2+γ)²/2` the probability that a dyadic ball of radius
`2^{-j}` centred in the unit square has mass below `2^{-jc}` is at most `C 2^{-jθ}` for some `θ > 2`. This is the
hypothesis of `ballMassLowerTail_of_dyadic`. -/
theorem lowerTail_dyadic_of_negMoment.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hN : ∀ q : ℝ, 0 < q → BallMassNegMoment.{u} γ q) :
    ∀ c : ℝ, (2 + γ) ^ 2 / 2 < c → ∃ θ : ℝ, 2 < θ ∧ ∃ C : ℝ, ∃ j₀ : ℕ,
      ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, ∀ j : ℕ, j₀ ≤ j →
        P {ω | μ ω (ball z (dyadicScale j)) < ENNReal.ofReal (dyadicScale j ^ c)} ≤
          ENNReal.ofReal (C * dyadicScale j ^ θ) := by
  intro c hc
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (c - (2 + γ) ^ 2 / 2) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 2 + δ / γ := ⟨_, rfl⟩
  have hτ2 : 2 < τ := by
    have : 0 < δ / γ := div_pos hδ0 hγ0
    rw [hτdef]; linarith
  have hγτ : γ * τ = 2 * γ + δ := by rw [hτdef]; field_simp
  have hcδ : c = (2 + γ ^ 2 / 2) + γ * τ + δ := by
    rw [hγτ]; nlinarith [hδdef]
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 3 / δ := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hδq : δ * q = 3 := by rw [hqdef]; field_simp
  obtain ⟨CN, hCN⟩ := hN q hq0
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (τ ^ 2 / 2) 3 := ⟨_, rfl⟩
  have hθ2 : 2 < θ := by rw [hθdef]; exact lt_min (by nlinarith) (by norm_num)
  refine ⟨θ, hθ2, 2 * (3 : ℝ) ^ (τ ^ 2) + CN, 0, ?_⟩
  intro z hz j _
  have hr0 : 0 < dyadicScale j := dyadicScale_pos' j
  have hr1 : dyadicScale j ≤ 1 := dyadicScale_le_one' j
  have hz2 : ‖z‖ ≤ 2 := by
    rw [Complex.mem_reProdIm] at hz
    have h1 : |z.re| ≤ 1 := abs_le.2 ⟨by linarith [hz.1.1], hz.1.2⟩
    have h2 : |z.im| ≤ 1 := abs_le.2 ⟨by linarith [hz.2.1], hz.2.2⟩
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  obtain ⟨hC', hh'⟩ := isWholePlaneGFF_recentredField hh j z
  obtain ⟨μ', hμ'⟩ := hh'.exists_isLQGMeasure hγ0 hγ2
  have hae := ae_measure_ball_eq hγ0 hμ j z hμ'
  have hmom := hCN Ω P hC' _ μ' hh' hμ'
  have hm := measure_ball_zero_lt_le hγ0 hγ2 hh' hμ' hq0 hmom (s := dyadicScale j ^ δ)
    (Real.rpow_pos_of_pos hr0 δ)
  rw [← Real.rpow_mul hr0.le, hδq] at hm
  refine lowerTail_single hh hr0 hr1 hz2 hγ0 (by linarith) hcδ
    (by rw [hθdef]; exact min_le_left _ _) (by rw [hθdef]; exact min_le_right _ _) ?_ hm
  filter_upwards [hae] with ω hω
  have := hω 1 one_pos
  rw [mul_one] at this
  exact this

/-- The lower tail of the ball mass, `BallMassLowerTail`, from negative moments of the unit-ball mass. -/
theorem ballMassLowerTail_of_negMoment.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (hN : ∀ q : ℝ, 0 < q → BallMassNegMoment.{u} γ q) : BallMassLowerTail P γ μ :=
  ballMassLowerTail_of_dyadic (lowerTail_dyadic_of_negMoment hγ0 hγ2 hh hμ hN)

end LatticeProb.LQG
