/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P4_1Cov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P4_1GaussMain
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailBorell

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 4.1, Step 4: variances and covariances of `X_k = h_{ε𝕣}(z_k) - h_𝕣(0)`

Source: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, `lqg-metric-estimates-final.tex`,
(4.6)–(4.7) (T:2508–2516): "by the calculations in [DS11, Section 3.1] … `Var(X_k) =
log ε⁻¹ + O(1)` … `Cov(X_j, X_k) = log(𝕣/|z_j^ε - z_k^ε|) + O(1)`". We use only the bounds needed
by Step 4 (`Var X_k ≥ log ε⁻¹`, `Cov(X_j,X_k) ≤ log ε⁻¹ - log(|j-k|+1) + A₀`), computed from the
exact circle-average covariance `incCov` (`CircleAvg.covariance_cInc`, DS §3.1) and the mean value
formula `⨍_{∂B_ρ(z)} log|a - w| da = log max(ρ, |z - w|)` (mathlib).

`circVec_step4`: the hypotheses of `sumExp_lower` for the vector `X_k = h_{ε𝕣}(z_k) - h_𝕣(0)`,
when `|z_k| ≤ R𝕣`, `|z_j - z_k| ≥ 2ε𝕣` and `|z_j - z_k| ≥ c ε𝕣 (|j-k|+1)` for `j ≠ k`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped NNReal

namespace LQGMetric.DFGPS.P41

open CircleAvg

lemma circCov_self' {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : circCov z ρ z ρ = log ρ := by
  rw [circCov_center z hρ ρ hρ, inv_mul_cancel₀ hρ.ne']
  simp [Real.posLog_apply]

/-- `⨍⨍ log|a - b| = log|z - w|` for circles `∂B_ρ(z)`, `∂B_ρ(w)` with `|z - w| ≥ 2ρ` -/
lemma circCov_far {ρ : ℝ} (hρ : 0 < ρ) {z w : ℂ} (hzw : 2 * ρ ≤ ‖z - w‖) :
    circCov z ρ w ρ = log ‖z - w‖ := by
  have h1 : Real.circleAverage (circLog w ρ) z ρ =
      Real.circleAverage (fun a => log ‖a - w‖) z ρ := by
    refine Real.circleAverage_congr_sphere fun u hu => ?_
    rw [abs_of_pos hρ, mem_sphere_iff_norm] at hu
    rw [circLog_eq_log_max hρ, max_eq_right, norm_sub_rev]
    have := norm_sub_norm_le (z - w) (z - u)
    rw [show z - w - (z - u) = u - w by ring, norm_sub_rev z u, hu] at this
    rw [norm_sub_rev]; linarith
  rw [circCov, h1, _root_.circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hρ.ne',
    Real.posLog_eq_log_max_one (by positivity), max_eq_right, Real.log_mul (inv_ne_zero hρ.ne'),
    Real.log_inv]
  · ring
  · have : 0 < ‖z - w‖ := by linarith
    exact this.ne'
  · rw [le_inv_mul_iff₀ hρ]; linarith

/-- `log 𝕣 ≤ ⨍_{∂B_ρ(z)} log max(𝕣, |a|) ≤ log 𝕣 + log(R+1)` for `|z| ≤ R𝕣`, `ρ ≤ 𝕣` -/
lemma circCov_origin_bounds {ρ r R : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hR : 0 ≤ R) {z : ℂ}
    (hz : ‖z‖ ≤ R * r) :
    log r ≤ circCov z ρ 0 r ∧ circCov z ρ 0 r ≤ log r + log (R + 1) := by
  have hr : 0 < r := hρ.trans_le hρr
  have hci : CircleIntegrable (circLog 0 r) z ρ :=
    ((continuous_circLog hr.ne' 0).continuousOn).circleIntegrable'
  have hpt : ∀ u ∈ sphere z |ρ|, circLog 0 r u = log (max r ‖u‖) := by
    intro u _; rw [circLog_eq_log_max hr, zero_sub, norm_neg]
  refine ⟨?_, ?_⟩
  · rw [circCov, ← Real.circleAverage_const (log r) z ρ]
    refine Real.circleAverage_mono (circleIntegrable_const _ _ _) hci fun u hu => ?_
    rw [hpt u hu]
    exact log_le_log hr (le_max_left _ _)
  · refine Real.circleAverage_mono_on_of_le_circle hci fun u hu => ?_
    rw [hpt u hu, ← Real.log_mul hr.ne' (by linarith)]
    refine log_le_log (lt_max_of_lt_left hr) (max_le (by nlinarith) ?_)
    rw [abs_of_pos hρ, mem_sphere_iff_norm] at hu
    have := norm_le_norm_add_norm_sub' u z
    nlinarith

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {n : ℕ}

/-- the vector `X_k = h_ρ(z_k) - h_𝕣(0)` -/
def circVec (h : Ω → DistC) (ρ r : ℝ) (z : Fin n → ℂ) (ω : Ω) (k : Fin n) : ℝ :=
  cInc h ρ (z k) r 0 ω

/-- **The hypotheses of `sumExp_lower` for `X_k = h_{ε𝕣}(z_k) - h_𝕣(0)`** ((4.6)–(4.7),
T:2508–2516). -/
theorem circVec_step4 [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {ε r R c : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) (hR : 0 ≤ R) (hc : 0 < c) (z : Fin n → ℂ)
    (hz : ∀ k, ‖z k‖ ≤ R * r)
    (hsep : ∀ j k, j ≠ k → 2 * (ε * r) ≤ ‖z j - z k‖ ∧
      c * (ε * r) * ((dN j k : ℝ) + 1) ≤ ‖z j - z k‖) :
    Measurable (circVec h (ε * r) r z) ∧ HasGaussianLaw (circVec h (ε * r) r z) P ∧
      (∀ k, ∫ ω, circVec h (ε * r) r z ω k ∂P = 0) ∧
      (∀ k, log ε⁻¹ - 0 ≤ Var[fun ω => circVec h (ε * r) r z ω k; P]) ∧
      (∀ j k, cov[fun ω => circVec h (ε * r) r z ω j, fun ω => circVec h (ε * r) r z ω k; P] ≤
        log ε⁻¹ - log ((dN j k : ℝ) + 1) + (2 * log (R + 1) + |log c|)) := by
  set ρ := ε * r
  have hρ : 0 < ρ := mul_pos hε hr
  have hρr : ρ ≤ r := by simp only [ρ]; nlinarith
  have hlogρ : log ρ = log ε + log r := log_mul hε.ne' hr.ne'
  have hcen : circCov 0 r 0 r = log r := circCov_self' hr 0
  have hcovk : ∀ j k : Fin n, cov[fun ω => circVec h ρ r z ω j,
      fun ω => circVec h ρ r z ω k; P] = -circCov (z j) ρ (z k) ρ + circCov (z j) ρ 0 r +
        circCov (z k) ρ 0 r - log r := by
    intro j k
    have := covariance_cInc hh hρ hr hρ hr (z j) 0 (z k) 0
    simp only [circVec]
    rw [this, incCov, circCov_comm hr hρ 0 (z k), hcen]
  have hLR : 0 ≤ log (R + 1) := log_nonneg (by linarith)
  refine ⟨measurable_pi_iff.mpr fun k => measurable_cInc hh _ _ _ _, ?_, fun k =>
    integral_cInc hh hρ hr _ _, ?_, ?_⟩
  · exact SupTail.hasGaussianLaw_finVec (isGaussianProcess_incProc hh)
      (fun k : Fin n => ((⟨ρ, hρ⟩, z k), (⟨r, hr⟩, 0)))
  · intro k
    have hv := hcovk k k
    rw [covariance_self (X := fun ω => circVec h ρ r z ω k)
      (measurable_cInc hh _ _ _ _).aemeasurable, circCov_self' hρ] at hv
    rw [hv, hlogρ, log_inv]
    have := (circCov_origin_bounds hρ hρr hR (hz k)).1
    linarith
  · intro j k
    rw [hcovk]
    have hj := (circCov_origin_bounds hρ hρr hR (hz j)).2
    have hk := (circCov_origin_bounds hρ hρr hR (hz k)).2
    have hlc := neg_le_abs (log c)
    have hlc0 := abs_nonneg (log c)
    rw [log_inv]
    by_cases hjk : j = k
    · subst hjk
      rw [circCov_self' hρ, hlogρ]
      simp only [dN, Nat.sub_self, add_zero, CharP.cast_eq_zero, zero_add, log_one]
      linarith
    · obtain ⟨h2, hc'⟩ := hsep j k hjk
      rw [circCov_far hρ h2]
      have hd : (0 : ℝ) < (dN j k : ℝ) + 1 := by positivity
      have hlow := log_le_log (by positivity) hc'
      rw [log_mul (by positivity) hd.ne', log_mul hc.ne' hρ.ne', hlogρ] at hlow
      linarith

/-- **DFGPS (4.5)** (`eqn-line-path-sum-lower`, T:2496–2499, proved T:2507–2582): for fixed
points `z_0, …, z_{n-1}` with `n ≥ κ/ε`, `|z_k| ≤ R𝕣` and `|z_j - z_k| ≥ max(2ε𝕣, cε𝕣(|j-k|+1))`,
`P[∑_k e^{ξ h_{ε𝕣}(z_k)} < ε^{p-1-ξ²/2} e^{ξ h_𝕣(0)}] ≤ ε^{p²/(2ξ²) - ζ}` for `ε < ε₀`, with `ε₀`
depending only on `ξ, κ, R, c, p, ζ` (not on `𝕣`, the points, or the field). -/
theorem circSum_lower {ξ κ R c p ζ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hc : 0 < c) (hp : 0 < p) (hζ : 0 < ζ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ (n : ℕ) (z : Fin n → ℂ), κ / ε ≤ n →
        (∀ k, ‖z k‖ ≤ R * r) →
        (∀ j k, j ≠ k → 2 * (ε * r) ≤ ‖z j - z k‖ ∧
          c * (ε * r) * ((dN j k : ℝ) + 1) ≤ ‖z j - z k‖) →
        P.real {ω | ∑ k, exp (ξ * (circleAvg (h ω) (ε * r) (z k) - circleAvg (h ω) r 0)) <
          ε ^ (p - 1 - ξ ^ 2 / 2)} ≤ ε ^ (p ^ 2 / (2 * ξ ^ 2) - ζ) := by
  have hA0 : 0 ≤ 2 * log (R + 1) + |log c| :=
    add_nonneg (mul_nonneg zero_le_two (log_nonneg (by linarith))) (abs_nonneg _)
  obtain ⟨ε₀, hε₀, H⟩ := sumExp_lower (A0 := 2 * log (R + 1) + |log c|) hξ0 hξ1 hκ hA0 hp hζ
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun ε hε Ω _ P _ h hh r hr n z hn hz hsep => ?_⟩
  obtain ⟨hm, hG, h0, hv, hcv⟩ := circVec_step4 hh hε.1 (hε.2.le.trans (min_le_right _ _)) hr
    hR hc z hz hsep
  exact H ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ P n _ hm hG h0 hn
    (fun k => le_trans (by linarith) (hv k)) hcv

end LQGMetric.DFGPS.P41
