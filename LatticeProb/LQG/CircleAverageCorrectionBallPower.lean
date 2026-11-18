import LatticeProb.LQG.NormalizedCoordinateBallPower

/-!
# Approximants of a field plus a continuous correction

Let `h_ε(z)` be circle averages and `F` a continuous function on the plane. The field `h + F`
has circle averages `h_ε(z) + F_ε(z)`, where `F_ε(z)` is the circle average of `F` over
`∂B(z, ε)`. On a set of centers `x` with `‖x‖ + ε ≤ L`, every circle average `F_ε(x)` is at
most the maximum `M` of `F` on `closedBall 0 L`, so the approximation density
`ε^{γ²/2} e^{γ (h_ε + F_ε)}` is at most `e^{γ M}` times `ε^{γ²/2} e^{γ h_ε}`.

* `circleAverage_le_of_closedBall`, `lqgApprox_add_circleAverage_le`: the deterministic
  comparison.
* `ae_singular_approximant_add_circleAverage_ball_rpow_bound`: for jointly continuous
  circle-average coordinates `c` of a normalized whole-plane GFF, `0 ≤ α < Q`, and any family
  of continuous corrections `F ω`, almost surely, for every `R > 0`, there are `β, C > 0` with
  `ν_k(B(z, r)) ≤ C r^β` for all `‖z‖ ≤ R`, `0 < r ≤ 1` and all levels `k`, where `ν_k` is
  the dyadic approximant of the field `c - α log |·| + F ω`.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- The circle average of a continuous function bounded above by `M` on `closedBall 0 L`,
over a circle `∂B(x, |ε|)` with `‖x‖ + |ε| ≤ L`, is at most `M`. -/
theorem circleAverage_le_of_closedBall {F : ℂ → ℝ} (hF : Continuous F) {L M : ℝ}
    (hFM : ∀ y ∈ closedBall (0 : ℂ) L, F y ≤ M) {x : ℂ} {ε : ℝ} (hxε : ‖x‖ + |ε| ≤ L) :
    Real.circleAverage F x ε ≤ M := by
  refine Real.circleAverage_mono_on_of_le_circle hF.continuousOn.circleIntegrable'
    fun y hy => hFM y ?_
  rw [mem_sphere, dist_eq_norm] at hy
  rw [mem_closedBall_zero_iff]
  have := norm_sub_norm_le y x
  linarith

/-- **Adding a continuous correction to the field.** If `γ ≥ 0`, `ε ≥ 0`, `F` is continuous
and bounded above by `M` on `closedBall 0 L`, and every point `x` of the measurable set `S`
has `‖x‖ + ε ≤ L`, then the approximant of the field with circle averages
`h_ε + F_ε` gives `S` at most `e^{γ M}` times the mass given by the approximant of `h`. -/
theorem lqgApprox_add_circleAverage_le {γ : ℝ} (hγ : 0 ≤ γ) (h : ℝ → ℂ → ℝ) {F : ℂ → ℝ}
    (hF : Continuous F) {ε L M : ℝ} (hε : 0 ≤ ε) {S : Set ℂ} (hS : MeasurableSet S)
    (hFM : ∀ y ∈ closedBall (0 : ℂ) L, F y ≤ M) (hSL : ∀ x ∈ S, ‖x‖ + ε ≤ L) :
    lqgApprox γ (fun r z => h r z + Real.circleAverage F z r) ε S ≤
      ENNReal.ofReal (Real.exp (γ * M)) * lqgApprox γ h ε S := by
  unfold lqgApprox
  rw [withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono_ae' hS (ae_of_all _ fun x hx => ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hav : Real.circleAverage F x ε ≤ M :=
    circleAverage_le_of_closedBall hF hFM (by rw [abs_of_nonneg hε]; exact hSL x hx)
  have h1 : Real.exp (γ * Real.circleAverage F x ε) ≤ Real.exp (γ * M) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hav hγ)
  have hA : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x) :=
    mul_nonneg (Real.rpow_nonneg hε _) (Real.exp_pos _).le
  calc ε ^ (γ ^ 2 / 2) * Real.exp (γ * (h ε x + Real.circleAverage F x ε))
      = (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) *
          Real.exp (γ * Real.circleAverage F x ε) := by
        rw [mul_add, Real.exp_add]
        ring
    _ ≤ (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) * Real.exp (γ * M) :=
        mul_le_mul_of_nonneg_left h1 hA
    _ = Real.exp (γ * M) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε x)) := mul_comm _ _

/-- `γ < Q = 2/γ + γ/2` for `0 < γ < 2`. -/
theorem self_lt_lqgQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have : γ / 2 < 2 / γ := by
    rw [lt_div_iff₀ hγ]
    nlinarith
  linarith

/-- **Approximants of a field with a logarithmic singularity and a continuous correction.**
Let `c ω` be jointly continuous circle-average coordinates of a whole-plane GFF `X`
normalized by `X_1(0) = 0`, let `0 ≤ α < Q`, and let `F ω` be continuous for every sample.
Almost surely, for every `R > 0`, there are `β > 0` and `C > 0` such that the dyadic
approximants of the `γ`-LQG measure of the field `c ω - α log |·| + F ω` give every ball
`B(z, r)` with `‖z‖ ≤ R` and `0 < r ≤ 1` mass at most `C r^β`, for every level `k`. The
event does not depend on `F`. -/
theorem ae_singular_approximant_add_circleAverage_ball_rpow_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ F : ℂ → ℝ, Continuous F → ∀ R : ℝ, 0 < R →
      ∃ β C : ℝ, 0 < β ∧ 0 < C ∧
        ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ k : ℕ,
          lqgApprox γ (fun s x => fieldCircleAverage α (c ω) s x + Real.circleAverage F x s)
            (dyadicScale k) (ball z r) ≤ ENNReal.ofReal (C * r ^ β) := by
  filter_upwards [ae_singular_approximant_ball_rpow_bound hX hG hc heq hγ hγ2 hα hαQ]
    with ω hω F hF R _hR
  obtain ⟨K, β, hβ, hK⟩ := hω R
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) (R + 2)).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨β, max (Real.exp (γ * M) * K) 1, hβ, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun z hz r hr hr1 k => ?_⟩
  have hk0 : 0 ≤ dyadicScale k := by
    unfold dyadicScale
    positivity
  have hk1 : dyadicScale k ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hFM : ∀ y ∈ closedBall (0 : ℂ) (R + 2), F y ≤ M := fun y hy => by
    have := hM y hy
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hSL : ∀ x ∈ ball z r, ‖x‖ + dyadicScale k ≤ R + 2 := fun x hx => by
    rw [mem_ball, dist_eq_norm] at hx
    have := norm_sub_norm_le x z
    linarith
  calc lqgApprox γ (fun s x => fieldCircleAverage α (c ω) s x + Real.circleAverage F x s)
        (dyadicScale k) (ball z r)
      ≤ ENNReal.ofReal (Real.exp (γ * M)) *
          lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball z r) :=
        lqgApprox_add_circleAverage_le hγ.le (fieldCircleAverage α (c ω)) hF hk0
          measurableSet_ball hFM hSL
    _ ≤ ENNReal.ofReal (Real.exp (γ * M)) * ENNReal.ofReal (K * r ^ β) :=
        mul_le_mul_of_nonneg_left (hK k z hz r hr hr1) zero_le
    _ = ENNReal.ofReal (Real.exp (γ * M) * K * r ^ β) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    _ ≤ ENNReal.ofReal (max (Real.exp (γ * M) * K) 1 * r ^ β) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _))

end LatticeProb.LQG
