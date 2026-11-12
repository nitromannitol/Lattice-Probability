import LatticeProb.LQG.GMCDilatedGrid
import LatticeProb.LQG.GMCOriginContinuum
import LatticeProb.LQG.GMCOriginGrowth
import LatticeProb.LQG.GMCScaleSandwich
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2
import LatticeProb.LQG.GMCMaximalMoment
import LatticeProb.LQG.GMCCircleLaw
import LatticeProb.Gauss.CircleAverageModulusUniform

/-!
# Continuum maximal masses of the dilated recentred fields

Let `h` be a whole-plane Gaussian free field with circle averages `h_r(z)`, and let `μ^{(j)}_t` be the
approximation at scale `t` of the γ-LQG measure of the dilated recentred field
`h^{(j)} = h(2^{-j} ·) - h_{2^{-j}}(0)`. We show that almost surely, for every `η > 0` and all large `j`,
`e^{γ h_{2^{-j}}(0)} sup_{t ∈ (0, 1]} μ^{(j)}_t(B(0, 1)) ≤ e^{η j}`, i.e. `ContinuumOriginGrowth γ h`.

The supremum over the continuum of radii is reduced to a grid of radii in each dyadic block `[2^{-n-1}, 2^{-n}]`
whose mesh, in the coordinates of `h`, is a power of the absolute scale `2^{-(n+j)}`: the uniform modulus of the
circle averages in the radius compares the recentred approximations at `t` and at the nearest grid radius, the grid
estimate for the dilated fields compares the grid radius with `2^{-n}`, and the dyadic radii are controlled by the
maximal masses of the next dilated field `h^{(j-1)}` through the scaling law of the approximations on balls.

## Main results

* `GMCContinuumMaximal.lqgApprox_ball_le_of_grid`: the deterministic grid-to-continuum comparison.
* `GMCContinuumMaximal.exp_mul_iSup_lqgApprox_le`: the deterministic bound of the continuum maximal mass.
* `IsWholePlaneGFF.ae_continuumOriginGrowth`: almost surely `ContinuumOriginGrowth γ (hcirc ω)`, `0 < γ < 2`.
* `coordChangeLP_of_isWholePlaneGFF`: the coordinate change rule `LQGMeasureCoordChangeLP` for every `α₀`.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.LQG.GMCContinuumMaximal

open LatticeProb.Gauss LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit
  LatticeProb.LQG.GMCScaleSandwich

/-- The recentred ball cut-off integral bounds the mass of the ball of radius `2`:
`e^{γ H_R(0)} ∫ b(z) s^{γ²/2} e^{γ (H_s(z) - H_R(0))} dz ≤ μ_s(B(0, 2))`, `b` the ball cut-off. -/
theorem ofReal_exp_mul_integral_ballCutoff_le {γ : ℝ} {H : ℝ → ℂ → ℝ} {s : ℝ} (R : ℝ) (hs : 0 < s)
    (hcont : Continuous (H s)) :
    ENNReal.ofReal (rexp (γ * H R 0) *
        ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H R 0)))) ≤
      lqgApprox γ H s (ball 0 2) := by
  have hint : Integrable (fun z => Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H R 0)))) :=
    (Gauss.ballCutoff_continuous.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hcont.sub continuous_const))))).integrable_of_hasCompactSupport
      Gauss.ballCutoff_hasCompactSupport.mul_right
  have hnn : 0 ≤ᵐ[volume] fun z => Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H R 0))) :=
    ae_of_all _ fun z => mul_nonneg (Gauss.ballCutoff_nonneg z)
      (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le)
  rw [lqgApprox, withDensity_apply _ isOpen_ball.measurableSet, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
      (hnn.mono fun z hz => mul_nonneg (Real.exp_pos _).le hz),
    ← lintegral_indicator isOpen_ball.measurableSet]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) 2
  · rw [Set.indicator_of_mem hz]
    refine ENNReal.ofReal_le_ofReal ?_
    have he : rexp (γ * H R 0) * (Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H R 0)))) =
        Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * H s z)) := by
      have := (Real.exp_pos (γ * H R 0)).ne'
      rw [mul_sub, Real.exp_sub]
      field_simp
    rw [he]
    exact mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le)
      (Gauss.ballCutoff_le_one z)
  · rw [Set.indicator_of_notMem hz, Gauss.ballCutoff_eq_zero (by simpa [mem_ball_zero_iff] using hz)]
    simp

/-- **Grid-to-continuum comparison for the dilated recentred field.** Let `h^{(j)} = h(2^{-j} ·) - h_{2^{-j}}(0)`,
`j ≥ 1`, `a > 0`. Suppose that at every level `n` the recentred ball cut-off integrals of `h^{(j)}` at the grid
radii `s_{n,i}` (grid of size `⌊2^{a (n+j)/2}⌋`) and at `2^{-n}` differ by less than `E`, and that the circle
averages of `h` at radii in `[2^{-k-1}, 2^{-k}]` at distance less than `2^{-k} 2^{-ka/4}`, `k ≥ j`, differ by at
most `1` on `B̄(0, 2)`. Then for every `t ∈ (0, 1]`,
`μ^{(j)}_t(B(0,1)) ≤ e^{(γ²/2) log 2 + γ} (sup_n μ^{(j)}_{2^{-n}}(B(0,2)) + e^{γ h^{(j)}_4(0)} E)`. -/
theorem lqgApprox_ball_le_of_grid {γ a E : ℝ} (hγ : 0 < γ) (ha : 0 < a) {h : ℝ → ℂ → ℝ} {j : ℕ}
    (hj : 1 ≤ j) (hcont : ∀ s, 0 < s → Continuous (h s))
    (hgrid : ∀ n, ∀ i ≤ gridCount a (n + j),
      |∫ z, Gauss.ballCutoff z * (gridScale (fun m => gridCount a (m + j)) n i ^ (γ ^ 2 / 2) *
          rexp (γ * (dilateRecentre (dyadicScale j) h (gridScale (fun m => gridCount a (m + j)) n i) z -
            dilateRecentre (dyadicScale j) h 4 0)) -
        dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (dilateRecentre (dyadicScale j) h (dyadicScale n) z -
            dilateRecentre (dyadicScale j) h 4 0)))| < E)
    (hmod : ∀ k, j ≤ k → ∀ z : ℂ, ‖z‖ ≤ 2 → ∀ s s' : ℝ,
      dyadicScale k / 2 ≤ s → s ≤ dyadicScale k → dyadicScale k / 2 ≤ s' → s' ≤ dyadicScale k →
      |s - s'| < dyadicScale k * dyadicScale k ^ (a / 4) → |h s z - h s' z| ≤ 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    lqgApprox γ (dilateRecentre (dyadicScale j) h) t (ball 0 1) ≤
      ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        ((⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale j) h) (dyadicScale n) (ball 0 2)) +
          ENNReal.ofReal (rexp (γ * dilateRecentre (dyadicScale j) h 4 0) * E)) := by
  have hdj : 0 < dyadicScale j := pow_pos (by norm_num) j
  set H := dilateRecentre (dyadicScale j) h with hHdef
  have hHc : ∀ r, 0 < r → Continuous (H r) := fun r hr => by
    show Continuous fun z => h (dyadicScale j * r) ((dyadicScale j : ℂ) * z) - h (dyadicScale j) 0
    exact ((hcont _ (mul_pos hdj hr)).comp (continuous_const.mul continuous_id)).sub continuous_const
  have hint : ∀ r, 0 < r →
      Integrable (fun z => Gauss.ballCutoff z * (r ^ (γ ^ 2 / 2) * rexp (γ * (H r z - H 4 0)))) :=
    fun r hr => (Gauss.ballCutoff_continuous.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((hHc r hr).sub continuous_const))))).integrable_of_hasCompactSupport
      Gauss.ballCutoff_hasCompactSupport.mul_right
  -- the dyadic block of `t`
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, dyadicScale n / 2 ≤ t ∧ t ≤ dyadicScale n := by
    rcases ht1.lt_or_eq with ht1' | rfl
    · obtain ⟨n, h1, h2⟩ := exists_dyadicScale_bracket ht0 ht1'
      exact ⟨n, by rw [← dyadicScale_succ_eq_half]; exact h1, h2.le⟩
    · exact ⟨0, by norm_num [dyadicScale], by norm_num [dyadicScale]⟩
  have hdn : 0 < dyadicScale n := pow_pos (by norm_num) n
  obtain ⟨hN1, hmesh0⟩ := one_le_gridCount_and_mesh_le ha.le (n + j)
  obtain ⟨i, hi, hti⟩ := exists_gridScale_near (fun m => gridCount a (m + j)) hN1 hn1 hn2
  have hgi := hgrid n i hi
  have hE : 0 ≤ E := (abs_nonneg _).trans hgi.le
  obtain ⟨hs1, hs2⟩ := gridScale_mem_Icc (fun m => gridCount a (m + j)) hi
  set s := gridScale (fun m => gridCount a (m + j)) n i with hsdef
  have hs0 : 0 < s := by linarith
  -- the modulus of the circle averages on the support of the cut-off
  have hk : dyadicScale (n + j) = dyadicScale j * dyadicScale n := by
    rw [add_comm]; exact dyadicScale_add j n
  have hk0 : 0 < dyadicScale (n + j) := pow_pos (by norm_num) _
  have hk1 : dyadicScale (n + j) < 1 := by
    unfold dyadicScale; exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hmesh : |dyadicScale j * t - dyadicScale j * s| <
      dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 4) := by
    rw [← mul_sub, abs_mul, abs_of_pos hdj]
    calc dyadicScale j * |t - s| ≤ dyadicScale j * (dyadicScale n / (2 * gridCount a (n + j))) :=
          mul_le_mul_of_nonneg_left hti hdj.le
      _ = dyadicScale (n + j) / (2 * gridCount a (n + j)) := by rw [hk]; ring
      _ ≤ dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 2) := hmesh0
      _ < dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 4) :=
          mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_gt hk0 hk1 (by linarith)) hk0
  have hb1 : dyadicScale (n + j) / 2 ≤ dyadicScale j * t := by
    rw [hk, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hn1 hdj.le
  have hb2 : dyadicScale j * t ≤ dyadicScale (n + j) := by
    rw [hk]; exact mul_le_mul_of_nonneg_left hn2 hdj.le
  have hb3 : dyadicScale (n + j) / 2 ≤ dyadicScale j * s := by
    rw [hk, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hs1 hdj.le
  have hb4 : dyadicScale j * s ≤ dyadicScale (n + j) := by
    rw [hk]; exact mul_le_mul_of_nonneg_left hs2 hdj.le
  have hη : ∀ z, Gauss.ballCutoff z ≠ 0 → |H t z - H s z| ≤ 1 := by
    intro z hz
    have hz2 : ‖z‖ < 2 := by
      by_contra hcon
      exact hz (Gauss.ballCutoff_eq_zero (not_lt.mp hcon))
    have hdj1 : dyadicScale j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnorm : ‖(dyadicScale j : ℂ) * z‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdj.le]
      nlinarith [norm_nonneg z]
    have := hmod (n + j) (by omega) _ hnorm _ _ hb1 hb2 hb3 hb4 hmesh
    simpa [hHdef, dilateRecentre] using this
  -- comparison of the recentred integrals at `t` and at the grid radius `s`
  have hlog : |Real.log t - Real.log s| ≤ Real.log 2 := by
    have h1 : Real.log t ≤ Real.log (dyadicScale n) := Real.log_le_log ht0 hn2
    have h2 : Real.log s ≤ Real.log (dyadicScale n) := Real.log_le_log hs0 hs2
    have h3 : Real.log (dyadicScale n / 2) ≤ Real.log t := Real.log_le_log (by positivity) hn1
    have h4 : Real.log (dyadicScale n / 2) ≤ Real.log s := Real.log_le_log (by positivity) hs1
    rw [Real.log_div hdn.ne' two_ne_zero] at h3 h4
    rw [abs_le]; constructor <;> linarith
  have hcmp := abs_integral_recentred_sub_le (μ := volume) (γ := γ) (η := 1) (H₀ := H 4 0) ht0 hs0 hη
    (hint t ht0) (hint s hs0)
  have habs : ∫ z, |Gauss.ballCutoff z| * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) =
      ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) := by
    congr 1; funext z; rw [abs_of_nonneg (Gauss.ballCutoff_nonneg z)]
  rw [habs] at hcmp
  have hsplit : (∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0)))) -
      ∫ z, Gauss.ballCutoff z * (dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (H (dyadicScale n) z - H 4 0))) =
      ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0)) -
        dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (H (dyadicScale n) z - H 4 0))) := by
    rw [← integral_sub (hint s hs0) (hint _ hdn)]
    congr 1; funext z; ring
  rw [← hsplit] at hgi
  set It := ∫ z, Gauss.ballCutoff z * (t ^ (γ ^ 2 / 2) * rexp (γ * (H t z - H 4 0))) with hIt
  set Is := ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) with hIs
  set Id := ∫ z, Gauss.ballCutoff z * (dyadicScale n ^ (γ ^ 2 / 2) *
    rexp (γ * (H (dyadicScale n) z - H 4 0))) with hId
  have hIs0 : 0 ≤ Is := integral_nonneg fun z => mul_nonneg (Gauss.ballCutoff_nonneg z) (by positivity)
  have hId0 : 0 ≤ Id := integral_nonneg fun z => mul_nonneg (Gauss.ballCutoff_nonneg z) (by positivity)
  have hexp : rexp (γ ^ 2 / 2 * |Real.log t - Real.log s| + |γ| * 1) ≤
      rexp (γ ^ 2 / 2 * Real.log 2 + γ) := by
    rw [abs_of_pos hγ, mul_one]
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
    exact Real.exp_le_exp.mpr (by linarith)
  have hc0 := Real.exp_pos (γ ^ 2 / 2 * Real.log 2 + γ)
  have hIt_le : It ≤ rexp (γ ^ 2 / 2 * Real.log 2 + γ) * Is := by
    have h1 := (abs_le.mp hcmp).2
    have h2 := mul_le_mul_of_nonneg_right hexp hIs0
    linarith
  have hIs_le : Is ≤ Id + E := by linarith [(abs_lt.mp hgi).2]
  have hball := Gauss.lqgApprox_ball_le (γ := γ) (h := H) 4 ht0 (hHc t ht0)
  have hd2 := ofReal_exp_mul_integral_ballCutoff_le (γ := γ) (H := H) 4 hdn (hHc _ hdn)
  refine hball.trans ?_
  have he0 := Real.exp_pos (γ * H 4 0)
  have hreal : rexp (γ * H 4 0) * It ≤
      rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (rexp (γ * H 4 0) * Id + rexp (γ * H 4 0) * E) := by
    calc rexp (γ * H 4 0) * It ≤ rexp (γ * H 4 0) * (rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (Id + E)) :=
          mul_le_mul_of_nonneg_left (hIt_le.trans (mul_le_mul_of_nonneg_left hIs_le hc0.le)) he0.le
      _ = rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (rexp (γ * H 4 0) * Id + rexp (γ * H 4 0) * E) := by ring
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_add (mul_nonneg he0.le hId0) (mul_nonneg he0.le hE)]
  gcongr
  exact hd2.trans (le_iSup (fun n => lqgApprox γ H (dyadicScale n) (ball 0 2)) n)

/-- **Scaling of the dyadic masses of the ball of radius `2`.** For the dilated recentred fields
`h^{(k)} = h(2^{-k} ·) - h_{2^{-k}}(0)`:
`e^{γ h_{2^{-k-1}}(0)} μ^{(k+1)}_{2^{-n}}(B(0,2)) = 2^{γ Q} e^{γ h_{2^{-k}}(0)} μ^{(k)}_{2^{-n-1}}(B(0,1))`. -/
theorem ofReal_exp_mul_lqgApprox_ball_two_eq {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) (k n : ℕ) :
    ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 1)) 0)) *
        lqgApprox γ (dilateRecentre (dyadicScale (k + 1)) h) (dyadicScale n) (ball 0 2) =
      ENNReal.ofReal (2 ^ (γ * lqgQ γ)) * (ENNReal.ofReal (rexp (γ * h (dyadicScale k) 0)) *
        lqgApprox γ (dilateRecentre (dyadicScale k) h) (dyadicScale (n + 1)) (ball 0 1)) := by
  have key := lqgApprox_ball_mul_eq hγ (dilateRecentre (dyadicScale (k + 1)) h) (c := 2)
    (ε := dyadicScale (n + 1)) two_pos (pow_pos (by norm_num) _) 1
  have h1 : (2 : ℝ) * dyadicScale (n + 1) = dyadicScale n := by rw [dyadicScale_succ_eq_half]; ring
  have h2 : dyadicScale (k + 1) * 2 = dyadicScale k := by rw [dyadicScale_succ_eq_half]; ring
  rw [h1, mul_one, dilateRecentre_dilateRecentre, h2] at key
  rw [key, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (γ * lqgQ γ))]
  congr 2
  simp only [dilateRecentre, mul_zero, h2]
  rw [mul_sub, Real.exp_sub]
  have := (Real.exp_pos (γ * h (dyadicScale (k + 1)) 0)).ne'
  field_simp

/-- **Deterministic bound of the continuum maximal mass.** Under the hypotheses of `lqgApprox_ball_le_of_grid`
at `j = k + 2`,
`e^{γ h_{2^{-k-2}}(0)} sup_{t ∈ (0,1]} μ^{(k+2)}_t(B(0,1)) ≤ e^{(γ²/2) log 2 + γ} (2^{γ Q} e^{γ h_{2^{-k-1}}(0)} Z_{k+1}
+ e^{γ h_{2^{-k}}(0)} E)`, where `Z_{k+1} = sup_n μ^{(k+1)}_{2^{-n}}(B(0,1))`. -/
theorem exp_mul_iSup_lqgApprox_le {γ a E : ℝ} (hγ : 0 < γ) (ha : 0 < a) {h : ℝ → ℂ → ℝ} {k : ℕ}
    (hcont : ∀ s, 0 < s → Continuous (h s))
    (hgrid : ∀ n, ∀ i ≤ gridCount a (n + (k + 2)),
      |∫ z, Gauss.ballCutoff z * (gridScale (fun m => gridCount a (m + (k + 2))) n i ^ (γ ^ 2 / 2) *
          rexp (γ * (dilateRecentre (dyadicScale (k + 2)) h
            (gridScale (fun m => gridCount a (m + (k + 2))) n i) z -
            dilateRecentre (dyadicScale (k + 2)) h 4 0)) -
        dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (dilateRecentre (dyadicScale (k + 2)) h (dyadicScale n) z -
            dilateRecentre (dyadicScale (k + 2)) h 4 0)))| < E)
    (hmod : ∀ k', k + 2 ≤ k' → ∀ z : ℂ, ‖z‖ ≤ 2 → ∀ s s' : ℝ,
      dyadicScale k' / 2 ≤ s → s ≤ dyadicScale k' → dyadicScale k' / 2 ≤ s' → s' ≤ dyadicScale k' →
      |s - s'| < dyadicScale k' * dyadicScale k' ^ (a / 4) → |h s z - h s' z| ≤ 1) :
    ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 2)) 0)) *
        (⨆ t ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale (k + 2)) h) t (ball 0 1)) ≤
      ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        (ENNReal.ofReal (2 ^ (γ * lqgQ γ)) * (ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 1)) 0)) *
          ⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale (k + 1)) h) (dyadicScale n) (ball 0 1)) +
        ENNReal.ofReal (rexp (γ * h (dyadicScale k) 0) * E)) := by
  have hU4 : ∀ t ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale (k + 2)) h) t (ball 0 1) ≤
      ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        ((⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale (k + 2)) h) (dyadicScale n) (ball 0 2)) +
          ENNReal.ofReal (rexp (γ * dilateRecentre (dyadicScale (k + 2)) h 4 0) * E)) :=
    fun t ht => lqgApprox_ball_le_of_grid hγ ha (j := k + 2) (by omega) hcont hgrid hmod ht.1 ht.2
  calc _ ≤ ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 2)) 0)) *
        (ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
          ((⨆ n : ℕ, lqgApprox γ (dilateRecentre (dyadicScale (k + 2)) h) (dyadicScale n) (ball 0 2)) +
            ENNReal.ofReal (rexp (γ * dilateRecentre (dyadicScale (k + 2)) h 4 0) * E))) :=
        mul_le_mul' le_rfl (iSup₂_le hU4)
    _ = ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        ((⨆ n : ℕ, ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 2)) 0)) *
            lqgApprox γ (dilateRecentre (dyadicScale (k + 2)) h) (dyadicScale n) (ball 0 2)) +
          ENNReal.ofReal (rexp (γ * h (dyadicScale (k + 2)) 0)) *
            ENNReal.ofReal (rexp (γ * dilateRecentre (dyadicScale (k + 2)) h 4 0) * E)) := by
        rw [← ENNReal.mul_iSup]; ring
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (add_le_add (iSup_le fun n => ?_) (le_of_eq ?_))
        · have hsc := ofReal_exp_mul_lqgApprox_ball_two_eq hγ.ne' h (k + 1) n
          rw [show k + 1 + 1 = k + 2 from rfl] at hsc
          rw [hsc]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (le_iSup (fun n =>
            lqgApprox γ (dilateRecentre (dyadicScale (k + 1)) h) (dyadicScale n) (ball 0 1)) (n + 1)))
        · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          have h4 : dyadicScale (k + 2) * 4 = dyadicScale k := by unfold dyadicScale; ring
          simp only [dilateRecentre, mul_zero, h4]
          rw [mul_sub, Real.exp_sub]
          have := (Real.exp_pos (γ * h (dyadicScale (k + 2)) 0)).ne'
          field_simp

end LatticeProb.LQG.GMCContinuumMaximal

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCContinuumMaximal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Subexponential growth of the continuum maximal masses at the origin.** For a whole-plane Gaussian free
field and `0 < γ < 2`, almost surely, for every `η > 0` and all large `j`,
`e^{γ h_{2^{-j}}(0)} sup_{t ∈ (0,1]} μ^{(j)}_t(B(0,1)) ≤ e^{η j}`, where `μ^{(j)}_t` are the approximations of the
dilated recentred field `h(2^{-j} ·) - h_{2^{-j}}(0)`. -/
theorem ae_continuumOriginGrowth (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ContinuumOriginGrowth γ (hcirc ω) := by
  have hgR : ∀ z, Gauss.ballCutoff z ≠ 0 → ‖z‖ + 1 ≤ 4 := fun z hz => by
    have : ‖z‖ < 2 := by
      by_contra hcon
      exact hz (Gauss.ballCutoff_eq_zero (not_lt.mp hcon))
    linarith
  obtain ⟨c₀, hc₀, hU2⟩ := hh.ae_eventually_grid_dilateRecentre hγ0 hγ2 Gauss.ballCutoff_continuous
    Gauss.ballCutoff_hasCompactSupport (R := 4) (by norm_num) hgR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he0 : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
  have ha0 : ∀ m : ℕ, 0 < min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) :=
    fun m => lt_min hc₀ (div_pos (he0 m) hlog2)
  have hac : ∀ m : ℕ, min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) / 2 < c₀ := fun m => by
    have := min_le_left c₀ (1 / ((m : ℝ) + 1) / Real.log 2)
    linarith [ha0 m]
  have hae : ∀ m : ℕ, min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) / 2 * Real.log 2 < 1 / ((m : ℝ) + 1) :=
    fun m => by
      have h1 : min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) * Real.log 2 ≤ 1 / ((m : ℝ) + 1) :=
        (le_div_iff₀ hlog2).mp (min_le_right _ _)
      have := mul_pos (ha0 m) hlog2
      linarith
  have hmodex : ∀ m : ℕ, ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ z : ℂ, ‖z‖ ≤ 2 → ∀ s s' : ℝ,
      dyadicScale k / 2 ≤ s → s ≤ dyadicScale k → dyadicScale k / 2 ≤ s' → s' ≤ dyadicScale k →
      |s - s'| < dyadicScale k * dyadicScale k ^ (min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) / 4) →
      |hcirc ω s z - hcirc ω s' z| ≤ dyadicScale k ^ β :=
    fun m => hh.ae_eventually_abs_circle_sub_le (div_pos (ha0 m) (by norm_num)) 2
  choose β hβ0 hβ using hmodex
  filter_upwards [ae_all_iff.mpr fun m : ℕ => hU2 _ _ (ha0 m).le (hac m) (hae m), ae_all_iff.mpr hβ,
    hh.ae_eventually_exp_circle_mul_maximal_dilated_le hγ0 hγ2,
    hh.ae_forall_eventually_exp_circle_dyadic_le γ, hh.ae_continuousOn_circle] with ω hA hM hX hY hcω
  intro η hη
  have hcont : ∀ s, 0 < s → Continuous (hcirc ω s) := fun s hs =>
    hcω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hs, Set.mem_univ _⟩
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < η / 4)
  set Cst := rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (2 ^ (γ * lqgQ γ) + 1) with hCst
  obtain ⟨J1, hJ1⟩ := eventually_atTop.mp (hA m)
  obtain ⟨J2, hJ2⟩ := eventually_atTop.mp (hM m)
  obtain ⟨J3, hJ3⟩ := eventually_atTop.mp (hX (η / 4) (by positivity))
  obtain ⟨J4, hJ4⟩ := eventually_atTop.mp (hY (η / 4) (by positivity))
  obtain ⟨J5, hJ5⟩ := eventually_atTop.mp ((Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hη))).eventually_ge_atTop Cst)
  refine eventually_atTop.mpr ⟨J1 + J2 + J3 + J4 + J5 + 2, fun j hj => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have hmod : ∀ k', k + 2 ≤ k' → ∀ z : ℂ, ‖z‖ ≤ 2 → ∀ s s' : ℝ,
      dyadicScale k' / 2 ≤ s → s ≤ dyadicScale k' → dyadicScale k' / 2 ≤ s' → s' ≤ dyadicScale k' →
      |s - s'| < dyadicScale k' * dyadicScale k' ^ (min c₀ (1 / ((m : ℝ) + 1) / Real.log 2) / 4) →
      |hcirc ω s z - hcirc ω s' z| ≤ 1 := by
    intro k' hk' z hz s s' h1 h2 h3 h4 h5
    exact (hJ2 k' (by omega) z hz s s' h1 h2 h3 h4 h5).trans
      (Real.rpow_le_one (pow_pos (by norm_num) k').le (pow_le_one₀ (by norm_num) (by norm_num)) (hβ0 m).le)
  refine (exp_mul_iSup_lqgApprox_le hγ0 (ha0 m) hcont (hJ1 (k + 2) (by omega)) hmod).trans ?_
  have hX' := hJ3 (k + 1) (by omega)
  have hY' := hJ4 k (by omega)
  have hC' : Cst ≤ rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) := hJ5 (k + 2) (by omega)
  have hB : ENNReal.ofReal (rexp (γ * hcirc ω (dyadicScale k) 0) * rexp (1 / ((m : ℝ) + 1) * ((k + 2 : ℕ) : ℝ))) ≤
      ENNReal.ofReal (rexp (η / 4 * k) * rexp (η / 4 * ((k + 2 : ℕ) : ℝ))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul hY' (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg _))) (Real.exp_pos _).le (Real.exp_pos _).le)
  have hec := Real.exp_pos (γ ^ 2 / 2 * Real.log 2 + γ)
  have h2γ : (0 : ℝ) ≤ 2 ^ (γ * lqgQ γ) := by positivity
  calc _ ≤ ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        (ENNReal.ofReal (2 ^ (γ * lqgQ γ)) * ENNReal.ofReal (rexp (η / 4 * ((k + 1 : ℕ) : ℝ))) +
          ENNReal.ofReal (rexp (η / 4 * k) * rexp (η / 4 * ((k + 2 : ℕ) : ℝ)))) :=
        mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hX') hB)
    _ = ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ) *
        (2 ^ (γ * lqgQ γ) * rexp (η / 4 * ((k + 1 : ℕ) : ℝ)) +
          rexp (η / 4 * k) * rexp (η / 4 * ((k + 2 : ℕ) : ℝ)))) := by
        rw [ENNReal.ofReal_mul hec.le, ENNReal.ofReal_add (mul_nonneg h2γ (Real.exp_pos _).le) (by positivity),
          ENNReal.ofReal_mul h2γ]
    _ ≤ ENNReal.ofReal (rexp (η * ((k + 2 : ℕ) : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hX0 := Real.exp_pos (η / 2 * ((k + 2 : ℕ) : ℝ))
        have hk0 : (0 : ℝ) ≤ η * k := mul_nonneg hη.le (Nat.cast_nonneg k)
        have h1 : rexp (η / 4 * ((k + 1 : ℕ) : ℝ)) ≤ rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) :=
          Real.exp_le_exp.mpr (by push_cast; nlinarith)
        have h2 : rexp (η / 4 * k) * rexp (η / 4 * ((k + 2 : ℕ) : ℝ)) ≤ rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
        have h3 : rexp (η * ((k + 2 : ℕ) : ℝ)) =
            rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) * rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [h3]
        calc rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (2 ^ (γ * lqgQ γ) * rexp (η / 4 * ((k + 1 : ℕ) : ℝ)) +
              rexp (η / 4 * k) * rexp (η / 4 * ((k + 2 : ℕ) : ℝ)))
            ≤ rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (2 ^ (γ * lqgQ γ) * rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) +
              rexp (η / 2 * ((k + 2 : ℕ) : ℝ))) := by gcongr
          _ = Cst * rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) := by rw [hCst]; ring
          _ ≤ rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) * rexp (η / 2 * ((k + 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hC' hX0.le

end LatticeProb.Gauss.IsWholePlaneGFF

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- **The coordinate change rule for complex affine maps, for every `α₀`.** `LQGMeasureCoordChangeLP P γ α₀ hC hcirc`
(Duplantier-Sheffield 2011, Proposition 2.1, for complex affine maps) holds for every `α₀`: by
`coordChangeLP_of_ae_continuumOriginGrowth` it reduces to the almost sure subexponential growth of the continuum
maximal masses at the origin, `IsWholePlaneGFF.ae_continuumOriginGrowth`. -/
theorem coordChangeLP_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    LQGMeasureCoordChangeLP P γ α₀ hC hcirc :=
  coordChangeLP_of_ae_continuumOriginGrowth P γ α₀ hC hcirc fun hh hγ0 hγ2 =>
    hh.ae_continuumOriginGrowth hγ0 hγ2

end LatticeProb.LQG
