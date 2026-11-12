import LatticeProb.LQG.GMCDilation
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Dilated recentred whole-plane Gaussian free fields and annular comparison with the singular field

For a whole-plane Gaussian free field with circle averages `h` and a real `c > 0`, the circle averages
`(r, w) ↦ h (c r) (c w) - h c 0` of the field dilated by `c` and recentred at the circle of radius `c` about the
origin again form a whole-plane Gaussian free field (a special case of affine invariance). On an annulus away from
the origin and for scales below its inner radius, the circle averages of the field with logarithmic singularity
`-α log |·|` differ from those of the underlying field by at most `|α| max(|log a|, |log b|)`, so the
approximations of the Gaussian multiplicative chaos are comparable up to a constant.

## Main results

* `isWholePlaneGFF_dilateRecentre`: the dilated recentred circle averages are those of a whole-plane GFF.
* `fieldCircleAverage_of_le_norm`: `h_ε(z) = h^ℂ_ε(z) - α log |z|` for `ε ≤ |z|`.
* `lqgApprox_apply_le_of_le_add`: monotonicity of the mass of a measurable set in the circle averages.
* `lqgApprox_fieldCircleAverage_dyadic_annulus_le`: the mass at scale `2^{-(j+n)}` of the annulus
  `B_{2^{-j} b}(0) \ B_{2^{-j} a}(0)` for the singular field is at most `2^{-jσ} e^{γ h^ℂ_{2^{-j}}(0)} e^{γ K}` times the
  mass at scale `2^{-n}` of `B_b(0) \ B_a(0)` for the dilated recentred field without singularity, `σ = γ (Q - α)`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **The dilated recentred circle averages of a whole-plane GFF are those of a whole-plane GFF.** -/
theorem isWholePlaneGFF_dilateRecentre {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {c : ℝ}
    (hc : 0 < c) :
    ∃ hC' : Ω → (ℂ → ℝ) → ℝ, IsWholePlaneGFF P hC' (fun ω => dilateRecentre c (hcirc ω)) := by
  have h := AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG (c : ℂ)
    (Complex.ofReal_ne_zero.2 hc.ne') 0
  have heq : (fun ω r z => hcirc ω (‖(c : ℂ)‖ * r) ((c : ℂ) * z + 0) - hcirc ω ‖(c : ℂ)‖ 0) =
      fun ω => dilateRecentre c (hcirc ω) := by
    funext ω r z
    simp only [dilateRecentre, add_zero, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [heq] at h
  exact ⟨_, h⟩

/-- Away from the origin and at scales at most the distance to the origin, the circle averages of the singular
field `h^ℂ - α log |·|` are those of `h^ℂ` minus `α log |z|`. -/
theorem fieldCircleAverage_of_le_norm (α : ℝ) (H : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ε ≤ ‖z‖) : fieldCircleAverage α H ε z = H ε z - α * Real.log ‖z‖ := by
  have h1 : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε = Real.log (max ε ‖z‖) := by
    simpa only [sub_zero] using circleAverage_log_norm_sub_eq_log_max hε z 0
  simp only [fieldCircleAverage, h1, max_eq_right hz]

/-- **Monotonicity of the mass in the circle averages.** If the circle averages at scale `ε` of `h'` exceed those of
`h` by at most `K` on a measurable set `A`, then the `h'`-mass of `A` is at most `e^{γ K}` times its `h`-mass. -/
theorem lqgApprox_apply_le_of_le_add {γ : ℝ} (hγ : 0 ≤ γ) {h h' : ℝ → ℂ → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) {A : Set ℂ} (hA : MeasurableSet A) {K : ℝ}
    (hK : ∀ z ∈ A, h' ε z ≤ h ε z + K) :
    lqgApprox γ h' ε A ≤ ENNReal.ofReal (Real.exp (γ * K)) * lqgApprox γ h ε A := by
  simp only [lqgApprox]
  rw [withDensity_apply _ hA, withDensity_apply _ hA, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hA fun z hz => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp (γ * h' ε z) ≤ Real.exp (γ * K) * Real.exp (γ * h ε z) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [hK z hz])
  have h2 : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε _
  calc ε ^ (γ ^ 2 / 2) * Real.exp (γ * h' ε z)
      ≤ ε ^ (γ ^ 2 / 2) * (Real.exp (γ * K) * Real.exp (γ * h ε z)) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = Real.exp (γ * K) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z)) := by ring

/-- **Annular comparison with the field without singularity.** If `ε ≤ a`, `0 < ε`, and
`|α log |z|| ≤ K` on the annulus `a ≤ |z| < b`, the mass of the annulus for the singular field is at most
`e^{γ K}` times its mass for `H`. -/
theorem lqgApprox_fieldCircleAverage_annulus_le {γ : ℝ} (hγ : 0 ≤ γ) (α : ℝ) (H : ℝ → ℂ → ℝ)
    {ε a b K : ℝ} (hε : 0 < ε) (hεa : ε ≤ a) (hK : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ < b → |α * Real.log ‖z‖| ≤ K) :
    lqgApprox γ (fieldCircleAverage α H) ε (ball 0 b \ ball 0 a) ≤
      ENNReal.ofReal (Real.exp (γ * K)) * lqgApprox γ H ε (ball 0 b \ ball 0 a) := by
  refine lqgApprox_apply_le_of_le_add hγ hε.le (measurableSet_ball.diff measurableSet_ball) ?_
  intro z hz
  have hz1 : ‖z‖ < b := by simpa using hz.1
  have hz2 : a ≤ ‖z‖ := by simpa using hz.2
  rw [fieldCircleAverage_of_le_norm α H hε (hεa.trans hz2)]
  have := hK z hz2 hz1
  linarith [(abs_le.1 this).1, (abs_le.1 this).2, neg_abs_le (α * Real.log ‖z‖)]

/-- **Annular comparison at dyadic scales for the singular field.** Let `σ = γ (Q - α)`. For `γ > 0`, `0 < a`,
`2^{-n} ≤ a` and `|α log |z|| ≤ K` on `a ≤ |z| < b`, the mass at the scale `2^{-(j+n)}` of the annulus
`B_{2^{-j} b}(0) \ B_{2^{-j} a}(0)` for the singular field is at most `2^{-jσ} e^{γ h^ℂ_{2^{-j}}(0)} e^{γ K}` times the
mass at the scale `2^{-n}` of `B_b(0) \ B_a(0)` for the dilated recentred circle averages. -/
theorem lqgApprox_fieldCircleAverage_dyadic_annulus_le {γ : ℝ} (hγ : 0 < γ) (α : ℝ)
    (hcirc : ℝ → ℂ → ℝ) (j n : ℕ) {a b K : ℝ} (hna : dyadicScale n ≤ a)
    (hK : ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ < b → |α * Real.log ‖z‖| ≤ K) :
    lqgApprox γ (fieldCircleAverage α hcirc) (dyadicScale (j + n))
        (ball 0 (dyadicScale j * b) \ ball 0 (dyadicScale j * a)) ≤
      ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc (dyadicScale j) 0) *
          Real.exp (γ * K)) *
        lqgApprox γ (dilateRecentre (dyadicScale j) hcirc) (dyadicScale n) (ball 0 b \ ball 0 a) := by
  have hdp : ∀ k : ℕ, 0 < dyadicScale k := fun k => by unfold dyadicScale; positivity
  have hj : 0 < dyadicScale j := hdp j
  rw [dyadicScale_add, lqgApprox_fieldCircleAverage_dilation_annulus hγ.ne' α hcirc (hdp j) (hdp n)]
  refine le_trans (mul_le_mul' le_rfl (lqgApprox_fieldCircleAverage_annulus_le hγ.le α
    (dilateRecentre (dyadicScale j) hcirc) (hdp n) hna hK)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul]
  positivity

/-- **Annular comparison on the dyadic annulus `{2^{-j} / 2 ≤ |z| < 2^{-j}}`.** For `n ≥ 1` the mass at the scale
`2^{-(j+n)}` of the annulus `B_{2^{-j}}(0) \ B_{2^{-j}/2}(0)` for the singular field is at most
`2^{-jσ} e^{γ h^ℂ_{2^{-j}}(0)} 2^{γ |α|}` times the mass at the scale `2^{-n}` of `B_1(0) \ B_{1/2}(0)` for the
dilated recentred circle averages, `σ = γ (Q - α)`. -/
theorem lqgApprox_fieldCircleAverage_dyadic_annulus_le_two {γ : ℝ} (hγ : 0 < γ) (α : ℝ)
    (hcirc : ℝ → ℂ → ℝ) (j n : ℕ) (hn : 1 ≤ n) :
    lqgApprox γ (fieldCircleAverage α hcirc) (dyadicScale (j + n))
        (ball 0 (dyadicScale j * 1) \ ball 0 (dyadicScale j * (1 / 2))) ≤
      ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * hcirc (dyadicScale j) 0) *
          Real.exp (γ * (|α| * Real.log 2))) *
        lqgApprox γ (dilateRecentre (dyadicScale j) hcirc) (dyadicScale n)
          (ball 0 1 \ ball 0 (1 / 2)) := by
  refine lqgApprox_fieldCircleAverage_dyadic_annulus_le hγ α hcirc j n (a := 1 / 2) (b := 1)
    (K := |α| * Real.log 2) ?_ ?_
  · unfold dyadicScale
    calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1 / 2 := by norm_num
  · intro z h1 h2
    rw [abs_mul]
    have hlog : |Real.log ‖z‖| ≤ Real.log 2 := by
      rw [abs_le]
      refine ⟨?_, (Real.log_nonpos (norm_nonneg _) h2.le).trans (Real.log_nonneg one_le_two)⟩
      have := Real.log_le_log (by norm_num) h1
      rwa [one_div, Real.log_inv] at this
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg α)

end LatticeProb.LQG
