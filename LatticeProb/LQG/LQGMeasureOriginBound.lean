import LatticeProb.LQG.GMCDilationField
import LatticeProb.LQG.LQGMeasureExistenceSingular

/-! # Mass of the circle-average approximations near a logarithmic singularity

For the field `h - α log |·|`, with circle averages `fieldCircleAverage α h`, the mass at the dyadic scale `2^{-k}` of
the ball `B(0, 2^{-J})`, `J ≤ k`, is bounded by splitting the ball into the dyadic annuli
`B(0, 2^{-j}) \ B(0, 2^{-j-1})`, `J ≤ j < k`, and the innermost ball `B(0, 2^{-k})`, and by rescaling each piece to
unit size (Duplantier-Sheffield 2011, Section 3):
  `ν_{2^{-k}}(B(0, 2^{-J})) ≤ 2^{γ|α|} ∑_{J ≤ j ≤ k} 2^{-jσ} e^{γ h_{2^{-j}}(0)} Z_j`,
where `σ = γ (Q - α)` and `Z_j = sup_n m^{(j)}_{2^{-n}}(B(0, 1))` is the maximal unit-ball mass of the dyadic
approximations of the dilated recentred field `h^{(j)} = h(2^{-j} ·)(2^{-j} ·) - h_{2^{-j}}(0)`. When
`e^{γ h_{2^{-j}}(0)} Z_j` grows subexponentially in `j` and `α < Q`, the right side is bounded by the tail of a
convergent geometric series. This gives the bound on the mass near the origin
  `∀ η > 0, ∃ δ > 0, ∃ K, ∀ k ≥ K, ν_{2^{-k}}(B(0, δ)) ≤ η`
used for the existence of the LQG measure with a logarithmic singularity.

Main results:
* `lqgApprox_fieldCircleAverage_ball_dyadicScale_le_sum`: the dyadic decomposition bound.
* `exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually`: the bound near the origin from subexponential growth.
* `lqgMeasureExistenceLP_of_eventually_le`: existence of the LQG measure from an almost sure subexponential bound.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace LQGMeasureOriginBound

theorem dyadicScale_pos' (k : ℕ) : 0 < dyadicScale k := by
  unfold dyadicScale; positivity

/-- **Innermost ball.** The mass at scale `2^{-k}` of `B(0, 2^{-k})` for the singular field is at most
`2^{-kσ} e^{γ h_{2^{-k}}(0)}` times the maximal unit-ball mass of the dilated recentred field. -/
theorem lqgApprox_fieldCircleAverage_ball_dyadicScale_self_le {γ : ℝ} (hγ : 0 < γ) (α : ℝ)
    (h : ℝ → ℂ → ℝ) (k : ℕ) :
    lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale k)) ≤
      ENNReal.ofReal (dyadicScale k ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale k) 0)) *
        ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale k) h) (dyadicScale n) (ball 0 1) := by
  have h1 := lqgApprox_fieldCircleAverage_dyadic hγ.ne' α h k 0 1
  rw [add_zero, mul_one] at h1
  rw [h1]
  refine mul_le_mul' le_rfl ?_
  have hs0 : dyadicScale 0 = 1 := by simp [dyadicScale]
  calc lqgApprox γ (fieldCircleAverage α (dilateRecentre (dyadicScale k) h)) (dyadicScale 0) (ball 0 1)
      ≤ ENNReal.ofReal (Real.exp (γ * 0)) *
          lqgApprox γ (dilateRecentre (dyadicScale k) h) (dyadicScale 0) (ball 0 1) := by
        refine lqgApprox_apply_le_of_le_add hγ.le (dyadicScale_pos' 0).le measurableSet_ball ?_
        intro z hz
        have hz1 : ‖z‖ ≤ 1 := by
          have := mem_ball_zero_iff.1 hz
          exact this.le
        have hc : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale 0) = 0 := by
          have := circleAverage_log_norm_sub_eq_log_max (dyadicScale_pos' 0) z 0
          simp only [sub_zero] at this
          rw [this, hs0, max_eq_left hz1, Real.log_one]
        simp [fieldCircleAverage, hc]
    _ ≤ ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale k) h) (dyadicScale n) (ball 0 1) := by
        rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
        exact le_iSup (fun n : ℕ => lqgApprox γ (dilateRecentre (dyadicScale k) h) (dyadicScale n)
          (ball 0 1)) 0

/-- **Dyadic annulus.** For `j < k`, the mass at scale `2^{-k}` of `B(0, 2^{-j}) \ B(0, 2^{-j-1})` for the singular
field is at most `2^{γ|α|} 2^{-jσ} e^{γ h_{2^{-j}}(0)}` times the maximal unit-ball mass of the dilated recentred
field. -/
theorem lqgApprox_fieldCircleAverage_dyadic_annulus_le_iSup {γ : ℝ} (hγ : 0 < γ) (α : ℝ)
    (h : ℝ → ℂ → ℝ) {j k : ℕ} (hjk : j < k) :
    lqgApprox γ (fieldCircleAverage α h) (dyadicScale k)
        (ball 0 (dyadicScale j) \ ball 0 (dyadicScale (j + 1))) ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
        (ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale j) 0)) *
          ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = j + n := ⟨k - j, by omega⟩
  have h1 := lqgApprox_fieldCircleAverage_dyadic_annulus_le_two hγ α h j n (by omega)
  have hset : ball (0 : ℂ) (dyadicScale j) \ ball 0 (dyadicScale (j + 1)) =
      ball 0 (dyadicScale j * 1) \ ball 0 (dyadicScale j * (1 / 2)) := by
    rw [mul_one, show dyadicScale (j + 1) = dyadicScale j * (1 / 2) by
      simp [dyadicScale, pow_succ]]
  rw [hset]
  refine h1.trans ?_
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (dyadicScale_pos' j).le _) (Real.exp_pos _).le)]
  calc ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale j) 0)) *
          ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
          lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1 \ ball 0 (1 / 2))
      = ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
          (ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale j) 0)) *
            lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n)
              (ball 0 1 \ ball 0 (1 / 2))) := by ring
    _ ≤ _ := by
        gcongr
        exact (measure_mono sdiff_subset).trans (le_iSup (fun n : ℕ => lqgApprox γ
          (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) n)

/-- **Dyadic decomposition near the origin.** For `J ≤ k`,
`ν_{2^{-k}}(B(0, 2^{-J})) ≤ 2^{γ|α|} ∑_{J ≤ j ≤ k} 2^{-jσ} e^{γ h_{2^{-j}}(0)} Z_j`, `σ = γ (Q - α)`. -/
theorem lqgApprox_fieldCircleAverage_ball_dyadicScale_le_sum {γ : ℝ} (hγ : 0 < γ) (α : ℝ)
    (h : ℝ → ℂ → ℝ) {J k : ℕ} (hJk : J ≤ k) :
    lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
        ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1) := by
  have hC : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp
      (mul_nonneg hγ.le (mul_nonneg (abs_nonneg _) (Real.log_nonneg one_le_two))))
  suffices H : ∀ d J : ℕ, J + d = k →
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
          ∑ j ∈ Finset.Ico J (k + 1),
            ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h (dyadicScale j) 0)) *
              ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1) from
    H (k - J) J (by omega)
  intro d
  induction d with
  | zero =>
    intro J hJ
    rw [add_zero] at hJ
    subst hJ
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    exact (lqgApprox_fieldCircleAverage_ball_dyadicScale_self_le hγ α h J).trans
      (le_mul_of_one_le_left' hC)
  | succ d ih =>
    intro J hJ
    have hsplit : ball (0 : ℂ) (dyadicScale J) ⊆
        (ball 0 (dyadicScale J) \ ball 0 (dyadicScale (J + 1))) ∪ ball 0 (dyadicScale (J + 1)) := by
      rw [sdiff_union_self]
      exact subset_union_left
    calc lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale J))
        ≤ lqgApprox γ (fieldCircleAverage α h) (dyadicScale k)
            (ball 0 (dyadicScale J) \ ball 0 (dyadicScale (J + 1))) +
          lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 (dyadicScale (J + 1))) :=
          (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ _ := add_le_add (lqgApprox_fieldCircleAverage_dyadic_annulus_le_iSup hγ α h (by omega))
          (ih (J + 1) (by omega))
      _ = _ := by
          rw [← mul_add, Finset.sum_eq_sum_Ico_succ_bot (by omega : J < k + 1)]

/-- **Mass near the origin from subexponential growth.** If `0 < γ`, `α < Q` and, for every `η > 0`, eventually
`e^{γ h_{2^{-j}}(0)} Z_j ≤ e^{η j}`, then `∀ η > 0, ∃ δ > 0, ∃ K, ∀ k ≥ K, ν_{2^{-k}}(B(0, δ)) ≤ η`. -/
theorem exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually {γ α : ℝ} (hγ : 0 < γ)
    (hαQ : α < lqgQ γ) (h : ℝ → ℂ → ℝ)
    (hZ : ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α h) (dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  intro η hη
  have hσ : 0 < γ * (lqgQ γ - α) := mul_pos hγ (sub_pos.2 hαQ)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set σ := γ * (lqgQ γ - α) with hσdef
  set c := Real.exp (γ * (|α| * Real.log 2)) with hc
  set r := Real.exp (-(σ * Real.log 2 / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have : 0 < σ * Real.log 2 / 2 := by positivity
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hev := hZ (σ * Real.log 2 / 2) (by positivity)
  have hsmall : ∀ᶠ J : ℕ in atTop, c * (r ^ J / (1 - r)) ≤ η := by
    have ht : Tendsto (fun J : ℕ => c * (r ^ J / (1 - r))) atTop (𝓝 (c * (0 / (1 - r)))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).div_const _).const_mul _
    rw [zero_div, mul_zero] at ht
    exact ht.eventually (ge_mem_nhds hη)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hev
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hsmall.and (eventually_ge_atTop J₀))
  obtain ⟨hJη, hJJ₀⟩ := hJ J le_rfl
  refine ⟨dyadicScale J, dyadicScale_pos' J, J, fun k hk => ?_⟩
  refine (lqgApprox_fieldCircleAverage_ball_dyadicScale_le_sum hγ α h hk).trans ?_
  have hterm : ∀ j ∈ Finset.Ico J (k + 1),
      ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)) ≤
        ENNReal.ofReal (r ^ j) := by
    intro j hj
    have hjJ : J₀ ≤ j := hJJ₀.trans (Finset.mem_Ico.1 hj).1
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos' j).le _), mul_assoc]
    calc ENNReal.ofReal (dyadicScale j ^ σ) *
          (ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1))
        ≤ ENNReal.ofReal (dyadicScale j ^ σ) * ENNReal.ofReal (Real.exp (σ * Real.log 2 / 2 * j)) := by
          gcongr
          exact hJ₀ j hjJ
      _ = ENNReal.ofReal (r ^ j) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos' j).le _), hr,
            ← Real.exp_nat_mul, Real.rpow_def_of_pos (dyadicScale_pos' j), ← Real.exp_add]
          congr 2
          simp only [dyadicScale, Real.log_pow, Real.log_inv]
          ring
  calc ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 1)
      ≤ ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1), ENNReal.ofReal (r ^ j) := by
        gcongr with j hj
        exact hterm j hj
    _ = ENNReal.ofReal (c * ∑ j ∈ Finset.Ico J (k + 1), r ^ j) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg hr0 j)]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal
        ((mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (Real.exp_pos _).le).trans hJη)

/-- **Existence of the LQG measure with a logarithmic singularity from subexponential growth.** If, for a whole-plane
GFF and `0 < γ < 2`, almost surely `e^{γ h_{2^{-j}}(0)} Z_j ≤ e^{η j}` eventually for every `η > 0`, then the LQG
measure of `h^ℂ - α₀ log |·|` exists for every `α₀ < Q`. -/
theorem lqgMeasureExistenceLP_of_eventually_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α₀ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hZ : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
      ∀ᶠ j : ℕ in atTop,
        ENNReal.ofReal (Real.exp (γ * hcirc ω (dyadicScale j) 0)) *
            (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (hcirc ω)) (dyadicScale n) (ball 0 1)) ≤
          ENNReal.ofReal (Real.exp (η * j))) :
    LQGMeasureExistenceLP P γ α₀ hC hcirc :=
  LQGMeasureExistenceSingular.lqgMeasureExistenceLP_of_ae_origin P hC hcirc fun hG hγ hγ2 hQ => by
    filter_upwards [hZ hG hγ hγ2] with ω hω
    exact exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually hγ hQ (hcirc ω) hω

end LQGMeasureOriginBound

end LatticeProb.LQG
