import LatticeProb.LQG.GMCRatioLimitSingular

/-!
# Mass near the origin along every ratio of the dyadic scales

Let `h` be the circle-average process of a field on `ℂ`, `0 < γ`, `α < Q = 2/γ + γ/2`, and let
`ν_s = lqgApprox γ (fieldCircleAverage α h) s` be the approximations of the γ-LQG measure of `h - α log |·|`.
For each fixed `r > 0`, smallness of `ν_{r 2^{-k}}(B(0, δ))` follows from the dyadic statement for the dilated
recentred field `h(r ·) - h_r(0)`, by the scaling law of the approximations. To get it for all `r ∈ (0, 1]` on one
event, we use a single growth condition along the dyadic dilations in which the scale ranges over the whole
interval `(0, 1]`:

`ContinuumOriginGrowth γ h`: for every `η > 0`, eventually in `j`,
`e^{γ h_{2^{-j}}(0)} sup_{t ∈ (0, 1]} μ^{(j)}_t(B(0, 1)) ≤ e^{η j}`, where `μ^{(j)}_t` is the approximation at
scale `t` of the dilated recentred field `h^{(j)} = h(2^{-j} ·) - h_{2^{-j}}(0)`.

Since `h(r 2^{-j} ·) - h_{r 2^{-j}}(0)` is the dilation by `r` of `h^{(j)}`, its dyadic maximal masses on `B(0, 1)`
are, up to the factor `r^{-γ Q} e^{-γ (h_{r 2^{-j}}(0) - h_{2^{-j}}(0))}`, masses of `B(0, r)` under the
approximations of `h^{(j)}` at the scales `r 2^{-n} ∈ (0, 1]`. Hence `ContinuumOriginGrowth γ h` gives, for every
`r ∈ (0, 1]`, the dyadic growth hypothesis of `LQGMeasureOriginBound` for the field dilated by `r`, and therefore
the near-origin bound at the scales `r 2^{-k}`.

## Main results

* `dilateRecentre_dilateRecentre`: dilating and recentring at `c` and then at `r` is the same at `c r`.
* `ContinuumOriginGrowth.eventually_dilateRecentre`: the dyadic growth hypothesis for `h(r ·) - h_r(0)`,
  `0 < r ≤ 1`.
* `ContinuumOriginGrowth.exists_lqgApprox_fieldCircleAverage_ball_le_mul`: deterministic near-origin bound
  `∀ η > 0, ∃ δ > 0, ∃ K, ∀ k ≥ K, ν_{r 2^{-k}}(B(0, δ)) ≤ η` for every `r ∈ (0, 1]`.
* `ae_origin_ratio_of_ae_continuumOriginGrowth`: almost surely for all `r ∈ (1/2, 1]` at once.
* `coordChangeLP_of_ae_continuumOriginGrowth`: the coordinate change rule of the LQG measure of `h - α₀ log |·|`
  for every `α₀`, given `ContinuumOriginGrowth γ (hcirc ω)` almost surely for whole-plane GFFs and `0 < γ < 2`.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

open LatticeProb.Gauss

namespace LatticeProb.LQG

/-- **Composition of dilations.** Dilating and recentring at `c` and then at `r` is dilating and recentring at
`c r`. -/
theorem dilateRecentre_dilateRecentre (c r : ℝ) (h : ℝ → ℂ → ℝ) :
    dilateRecentre r (dilateRecentre c h) = dilateRecentre (c * r) h := by
  funext t w
  simp only [dilateRecentre, mul_zero, Complex.ofReal_mul, mul_assoc]
  ring

/-- **Scaling law of the approximations on balls.** For `c, ε > 0`,
`μ_{c ε}(B(0, c ρ)) = c^{γ Q} e^{γ h_c(0)} μ'_ε(B(0, ρ))`, where `μ'` are the approximations of the dilated
recentred field `h(c ·) - h_c(0)`. -/
theorem lqgApprox_ball_mul_eq {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (ρ : ℝ) :
    lqgApprox γ h (c * ε) (ball 0 (c * ρ)) =
      ENNReal.ofReal (c ^ (γ * lqgQ γ) * Real.exp (γ * h c 0)) *
        lqgApprox γ (dilateRecentre c h) ε (ball 0 ρ) := by
  have h0 : ∀ g : ℝ → ℂ → ℝ, fieldCircleAverage 0 g = g := fun g => by
    funext t z
    simp [fieldCircleAverage]
  have key := lqgApprox_fieldCircleAverage_dilation_ball hγ 0 h hc hε ρ
  simpa only [h0, sub_zero] using key

/-- **Subexponential growth of the continuum maximal masses along the dyadic dilations.** For every `η > 0`,
eventually in `j`, `e^{γ h_{2^{-j}}(0)} sup_{t ∈ (0, 1]} μ^{(j)}_t(B(0, 1)) ≤ e^{η j}`, where `μ^{(j)}_t` is the
approximation at scale `t` of the dilated recentred field `h(2^{-j} ·) - h_{2^{-j}}(0)`. -/
def ContinuumOriginGrowth (γ : ℝ) (h : ℝ → ℂ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
    ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
        (⨆ t ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) t (ball 0 1)) ≤
      ENNReal.ofReal (Real.exp (η * j))

namespace ContinuumOriginGrowth

/-- **The dyadic growth hypothesis for the field dilated by `r ∈ (0, 1]`.** If `ContinuumOriginGrowth γ h`, then
for `h' = h(r ·) - h_r(0)` and every `η > 0`, eventually in `j`,
`e^{γ h'_{2^{-j}}(0)} sup_n μ'^{(j)}_{2^{-n}}(B(0, 1)) ≤ e^{η j}`. -/
theorem eventually_dilateRecentre {γ : ℝ} (hγ : 0 < γ) {h : ℝ → ℂ → ℝ} (hU : ContinuumOriginGrowth γ h)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ η : ℝ, 0 < η → ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (γ * dilateRecentre r h (dyadicScale j) 0)) *
          (⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) (dilateRecentre r h)) (dyadicScale n)
            (ball 0 1)) ≤
        ENNReal.ofReal (Real.exp (η * j)) := by
  intro η hη
  have hR : 0 < r ^ (γ * lqgQ γ) := Real.rpow_pos_of_pos hr0 _
  set A : ℝ := (r ^ (γ * lqgQ γ))⁻¹ * Real.exp (-(γ * h r 0)) with hAdef
  have hA0 : 0 < A := mul_pos (inv_pos.2 hR) (Real.exp_pos _)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log A / (η / 2))
  filter_upwards [hU (η / 2) (half_pos hη), eventually_ge_atTop N] with j hj hjN
  set c : ℝ := dyadicScale j with hcdef
  have hc : 0 < c := pow_pos (by norm_num) j
  -- `A ≤ e^{η j / 2}` for `j ≥ N`
  have hAj : A ≤ Real.exp (η / 2 * j) := by
    have h1 : Real.log A < η / 2 * j := by
      have h2 : Real.log A / (η / 2) < j := hN.trans_le (by exact_mod_cast hjN)
      rw [div_lt_iff₀ (half_pos hη)] at h2
      linarith
    exact ((Real.log_lt_iff_lt_exp hA0).1 h1).le
  set M : ℝ≥0∞ := ⨆ t ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre c h) t (ball 0 1) with hMdef
  have hterm : ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (γ * dilateRecentre r h c 0)) *
          lqgApprox γ (dilateRecentre c (dilateRecentre r h)) (dyadicScale n) (ball 0 1) ≤
        ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (γ * h c 0)) * M) := by
    intro n
    have hn0 : 0 < dyadicScale n := pow_pos (by norm_num) n
    have hn1 : dyadicScale n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hscale := lqgApprox_ball_mul_eq hγ.ne' (dilateRecentre c h) hr0 hn0 1
    rw [dilateRecentre_dilateRecentre c r h] at hscale
    rw [dilateRecentre_dilateRecentre r c h, mul_comm r c]
    set T := lqgApprox γ (dilateRecentre (c * r) h) (dyadicScale n) (ball 0 1) with hT
    have hS : lqgApprox γ (dilateRecentre c h) (r * dyadicScale n) (ball 0 (r * 1)) ≤ M := by
      refine le_iSup₂_of_le (f := fun t (_ : t ∈ Ioc (0 : ℝ) 1) =>
        lqgApprox γ (dilateRecentre c h) t (ball 0 1)) (r * dyadicScale n)
        ⟨mul_pos hr0 hn0, (mul_le_mul hr1 hn1 hn0.le zero_le_one).trans_eq (one_mul 1)⟩ ?_
      exact measure_mono (ball_subset_ball (by linarith))
    have hdc : dilateRecentre c h r 0 = h (c * r) 0 - h c 0 := by
      simp [dilateRecentre]
    have hdr : dilateRecentre r h c 0 = h (c * r) 0 - h r 0 := by
      simp [dilateRecentre, mul_comm r c]
    rw [hdc] at hscale
    rw [hdr]
    have hreal : Real.exp (γ * (h (c * r) 0 - h r 0)) =
        A * Real.exp (γ * h c 0) * (r ^ (γ * lqgQ γ) * Real.exp (γ * (h (c * r) 0 - h c 0))) := by
      rw [hAdef]
      calc Real.exp (γ * (h (c * r) 0 - h r 0))
          = ((r ^ (γ * lqgQ γ))⁻¹ * r ^ (γ * lqgQ γ)) *
              (Real.exp (-(γ * h r 0)) * Real.exp (γ * h c 0) * Real.exp (γ * (h (c * r) 0 - h c 0))) := by
            rw [inv_mul_cancel₀ hR.ne', one_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
        _ = _ := by ring
    calc ENNReal.ofReal (Real.exp (γ * (h (c * r) 0 - h r 0))) * T
        = ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (γ * h c 0)) *
            (ENNReal.ofReal (r ^ (γ * lqgQ γ) * Real.exp (γ * (h (c * r) 0 - h c 0))) * T)) := by
          rw [hreal, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ = ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (γ * h c 0)) *
            lqgApprox γ (dilateRecentre c h) (r * dyadicScale n) (ball 0 (r * 1))) := by
          rw [hscale]
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (γ * h c 0)) * M) := by
          gcongr
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => (hterm n).trans ?_
  calc ENNReal.ofReal A * (ENNReal.ofReal (Real.exp (γ * h c 0)) * M)
      ≤ ENNReal.ofReal A * ENNReal.ofReal (Real.exp (η / 2 * j)) := by
        gcongr
    _ ≤ ENNReal.ofReal (Real.exp (η / 2 * j)) * ENNReal.ofReal (Real.exp (η / 2 * j)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (η * j)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring

/-- **Mass near the origin at the scales `r 2^{-k}`, deterministic form.** If `0 < γ`, `α < Q` and
`ContinuumOriginGrowth γ h`, then for every `r ∈ (0, 1]` and every `η > 0` there are `δ > 0` and `K` such that
`ν_{r 2^{-k}}(B(0, δ)) ≤ η` for all `k ≥ K`, where `ν_s` are the approximations of `h - α log |·|`. -/
theorem exists_lqgApprox_fieldCircleAverage_ball_le_mul {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    {h : ℝ → ℂ → ℝ} (hU : ContinuumOriginGrowth γ h) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α h) (r * dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  have hω := LQGMeasureOriginBound.exists_lqgApprox_fieldCircleAverage_ball_le_of_eventually hγ hαQ
    (dilateRecentre r h) (hU.eventually_dilateRecentre hγ hr0 hr1)
  intro η hη
  set A : ℝ := r ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h r 0) with hA
  have hA0 : 0 < A := mul_pos (Real.rpow_pos_of_pos hr0 _) (Real.exp_pos _)
  obtain ⟨δ, hδ, K, hK⟩ := hω (η / A) (div_pos hη hA0)
  refine ⟨r * δ, mul_pos hr0 hδ, K, fun k hk => ?_⟩
  rw [lqgApprox_fieldCircleAverage_dilation_ball hγ.ne' α h hr0
    (show (0 : ℝ) < dyadicScale k from pow_pos (by norm_num) k) δ]
  calc ENNReal.ofReal A *
        lqgApprox γ (fieldCircleAverage α (dilateRecentre r h)) (dyadicScale k) (ball 0 δ)
      ≤ ENNReal.ofReal A * ENNReal.ofReal (η / A) := by gcongr; exact hK k hk
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_mul hA0.le, mul_div_cancel₀ η hA0.ne']

end ContinuumOriginGrowth

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Mass near the origin along every ratio, almost surely.** If `0 < γ`, `α < Q` and almost surely
`ContinuumOriginGrowth γ (hcirc ω)`, then almost surely, for every `r ∈ (1/2, 1]` and every `η > 0`, the singular
approximations at the scales `r 2^{-k}` have mass at most `η` on a small ball about the origin for all large `k`. -/
theorem ae_origin_ratio_of_ae_continuumOriginGrowth {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ)
    (hU : ∀ᵐ ω ∂P, ContinuumOriginGrowth γ (hcirc ω)) :
    ∀ᵐ ω ∂P, ∀ r ∈ Ioc (1 / 2 : ℝ) 1, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (r * dyadicScale k) (ball 0 δ) ≤ ENNReal.ofReal η := by
  filter_upwards [hU] with ω hω r hr
  exact hω.exists_lqgApprox_fieldCircleAverage_ball_le_mul hγ hαQ (by linarith [hr.1]) hr.2

/-- **Coordinate change rule from the continuum growth condition.** If, for whole-plane GFFs and `0 < γ < 2`,
almost surely `ContinuumOriginGrowth γ (hcirc ω)`, then the γ-LQG measure of `h - α₀ log |·|` satisfies the
coordinate change rule under complex affine maps, for every `α₀`. -/
theorem coordChangeLP_of_ae_continuumOriginGrowth (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ)
    (H : IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ContinuumOriginGrowth γ (hcirc ω)) :
    LQGMeasureCoordChangeLP P γ α₀ hC hcirc :=
  coordChangeLP_of_ae_origin_ratio P γ α₀ hC hcirc fun hG hγ0 hγ2 hα =>
    ae_origin_ratio_of_ae_continuumOriginGrowth hγ0 hα (H hG hγ0 hγ2)

end LatticeProb.LQG
