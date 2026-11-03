/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCSqCont at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPosGreen
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqLip

/-!
# Lower bound for the circle-average covariances of the square GFF (P2-KAHANE3)

For the zero-boundary GFF on `𝕍 = (0,1)²`:

* `GMCPos.exists_hS_lower` : the regular part `hS` of the Green function of `𝕍` is bounded below
  on `K × K` for every compact convex `K ⊆ 𝕍`;
* `circleCov_ge_log` : `Cov(h_r(z), h_s(w)) ≥ −log(r + s + ‖z − w‖) + hS z w`;
* `circleCov_two_sided` : on a compact convex `K ⊆ 𝕍`, for circles of equal radius `r` with
  discs in `K`, `|Cov(h_r(z), h_r(w)) + log max(r, ‖z − w‖)| ≤ c_K`.

This is the two-sided covariance comparison "encadr-cov" of Berestycki–Powell,
*Gaussian free field and Liouville quantum gravity* (arXiv:2404.16642), `GMCproperties.tex`
l. 1205–1210 (`c_ε(x,y) − a ≤ E h_ε(x) h_ε(y) ≤ c_ε(x,y) + b`), with `c_ε(x,y) = −log max(ε,|x−y|)`
up to `O(1)` (their eq. (roughcov) l. 287–330), restricted to a compact subset of the domain,
where the regular part of the Green function is bounded. The upper half is `circleCov_le_log`.
The lower half follows the same computation: the inner circle mean of the Green function is
`−log max(s, ‖w − x‖) + hS x w` (`integral_greenH_sqM_circle`), the outer mean of `hS · w` is
`hS z w` (harmonicity, `integral_hS_circle_left`), and `max(s, ‖w − x‖) ≤ r + s + ‖z − w‖`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

namespace GMCPos

/-- **`hS` is bounded below on compact convex subsets of `𝕍`** -/
theorem exists_hS_lower {K : Set ℂ} (hKU : K ⊆ openSquare) (hKc : Convex ℝ K)
    (hKk : IsCompact K) : ∃ c : ℝ, ∀ a ∈ K, ∀ b ∈ K, c ≤ hS a b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun x hx => hx.elim⟩
  obtain ⟨m, M, hm, hmM⟩ := exists_sqQuot_bounds hKU hKc hKk
  have hc : ContinuousOn (fun y => (sqM y).im) K :=
    Complex.continuous_im.comp_continuousOn (differentiableOn_sqM.continuousOn.mono hKU)
  obtain ⟨y₀, hy₀, hmin⟩ := hKk.exists_isMinOn hne hc
  set m₁ := (sqM y₀).im
  have hm₁ : 0 < m₁ := sqM_mem_H (hKU hy₀)
  refine ⟨Real.log m₁ - Real.log M, fun a ha b hb => ?_⟩
  have hlow : m₁ ≤ ‖sqM b - conj (sqM a)‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
    have h1 : m₁ ≤ (sqM b).im := hmin hb
    have h2 : 0 < (sqM a).im := sqM_mem_H (hKU ha)
    rw [abs_of_pos (by linarith)]; linarith
  rw [hS_eq, dslope_sqM_eq (hKU ha) (hKU hb)]
  have hq := hmM b hb a ha
  have e1 := Real.log_le_log hm₁ hlow
  have e2 := Real.log_le_log (hm.trans_le hq.1) hq.2
  linarith

end GMCPos

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **lower bound for circle-average covariances**:
`Cov(h_r(z), h_s(w)) ≥ −log(r + s + ‖z − w‖) + hS z w` -/
theorem circleCov_ge_log (hX : IsZeroBoundaryGFFOn openSquare X P) {z w : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hB₁ : closedBall z r ⊆ openSquare)
    (hB₂ : closedBall w s ⊆ openSquare) :
    -Real.log (r + s + ‖z - w‖) + hS z w ≤
      cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w s); P] := by
  rw [circleCov_eq_kernel hX hr hs hB₁ hB₂]
  have hw : w ∈ openSquare := hB₂ (mem_closedBall_self hs.le)
  have hcongr : (fun x => ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s) =ᵐ[circleUnif z r]
      fun x => -Real.log (max s ‖w - x‖) + hS x w := by
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    rw [integral_greenH_sqM_circle (hB₁ hx) hs hB₂]
  have hi0 : Integrable (fun x => -Real.log (max s ‖w - x‖)) (circleUnif z r) := by
    refine CoordReg.integrable_circleUnif_of_continuousOn ?_ hr.le ?_
    · exact (Real.measurable_log.comp (measurable_const.max
        (measurable_const.sub measurable_id).norm)).neg
    · refine (Continuous.continuousOn ?_)
      exact ((continuous_const.max (continuous_const.sub continuous_id).norm).log
        fun x => (lt_max_of_lt_left hs).ne').neg
  have hih : Integrable (fun x => hS x w) (circleUnif z r) := by
    simp_rw [hS_symm _ w]; exact integrable_hS_right hw hr.le hB₁
  rw [integral_congr_ae hcongr, integral_add hi0 hih, integral_hS_circle_left hw hr.le hB₁]
  have hpos : 0 < r + s + ‖z - w‖ := by positivity
  have hmono : -Real.log (r + s + ‖z - w‖) ≤ ∫ x, -Real.log (max s ‖w - x‖) ∂circleUnif z r := by
    have : ∫ _x, -Real.log (r + s + ‖z - w‖) ∂circleUnif z r = -Real.log (r + s + ‖z - w‖) := by
      simp
    rw [← this]
    refine integral_mono_ae (integrable_const _) hi0 ?_
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hle : max s ‖w - x‖ ≤ r + s + ‖z - w‖ := by
      refine max_le (by linarith [norm_nonneg (z - w)]) ?_
      have := norm_sub_le_norm_sub_add_norm_sub w z x
      rw [norm_sub_rev w z, norm_sub_rev z x] at this
      linarith
    have := Real.log_le_log (lt_max_of_lt_left hs) hle
    linarith
  linarith

/-- **two-sided covariance bound on a compact convex `K ⊆ 𝕍`** (equal radii):
`|Cov(h_r(z), h_r(w)) + log max(r, ‖z − w‖)| ≤ c` for all circles with discs in `K` -/
theorem circleCov_two_sided {K : Set ℂ} (hKU : K ⊆ openSquare) (hKc : Convex ℝ K)
    (hKk : IsCompact K) :
    ∃ c : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ},
      IsZeroBoundaryGFFOn openSquare X P → ∀ {z w : ℂ} {r : ℝ}, 0 < r →
      closedBall z r ⊆ K → closedBall w r ⊆ K →
      |cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w r); P] +
        Real.log (max r ‖z - w‖)| ≤ c := by
  obtain ⟨c₀, hc₀⟩ := GMCPos.exists_hS_lower hKU hKc hKk
  refine ⟨max (Real.log 3) (Real.log 3 - c₀), fun hX z w r hr hB₁ hB₂ => ?_⟩
  have hup := circleCov_le_log hX hr hr (hB₁.trans hKU) (hB₂.trans hKU)
  have hlo := circleCov_ge_log hX hr hr (hB₁.trans hKU) (hB₂.trans hKU)
  have hzK : z ∈ K := hB₁ (mem_closedBall_self hr.le)
  have hwK : w ∈ K := hB₂ (mem_closedBall_self hr.le)
  have hh := hc₀ z hzK w hwK
  have hm : 0 < max r ‖z - w‖ := lt_max_of_lt_left hr
  have h3 : r + r + ‖z - w‖ ≤ 3 * max r ‖z - w‖ := by
    have := le_max_left r ‖z - w‖; have := le_max_right r ‖z - w‖; linarith
  have hl3 : Real.log (r + r + ‖z - w‖) ≤ Real.log 3 + Real.log (max r ‖z - w‖) := by
    rw [← Real.log_mul (by norm_num) hm.ne']
    exact Real.log_le_log (by positivity) h3
  rw [abs_le]
  constructor
  · have := le_max_right (Real.log 3) (Real.log 3 - c₀); linarith
  · have := le_max_left (Real.log 3) (Real.log 3 - c₀); linarith

end LQGMetric
