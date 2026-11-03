/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPos2GFF at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentPos2Main
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCont
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqGauss
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqReg
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCTest

/-!
# The square GFF in the middle third is log-correlated (P2-KAHANE3)

The comparison family of Berestycki–Powell (arXiv:2404.16642, `GMCproperties.tex` l. 1205–1210)
for the zero-boundary GFF `h` on `𝕍 = (0,1)²`: the circle averages of `h` around the points of the
middle third, `Z_n(x) = γ h_{2^{-n}/6}((1 + i + x)/3)` (`DGMC.midZ`), for `x ∈ [0,1]²` (outside
`[0,1]²` the centre is clamped, which keeps every disc inside `sqIn (1/6)`).

`DGMC.logCorr_midZ`: `Z` is `γ²`-log-correlated on `[0,1]²` (`LogCorr`), from the two-sided bound
`circleCov_two_sided` on the compact convex set `sqIn (1/6)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric QuantumZipper
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

lemma convex_sqIn (s : ℝ) : Convex ℝ (sqIn s) := by
  have : sqIn s = Complex.reLm ⁻¹' Icc s (1 - s) ∩ Complex.imLm ⁻¹' Icc s (1 - s) := by
    ext z; simp only [sqIn, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Icc,
      Complex.reLm_coe, Complex.imLm_coe]; tauto
  rw [this]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

/-- clamp to `[0,1]` -/
def clampU (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clampU_mem (t : ℝ) : 0 ≤ clampU t ∧ clampU t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clampU_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clampU t = t := by
  rw [clampU, min_eq_right h1, max_eq_right h0]

/-- the point of the middle third corresponding to `x ∈ [0,1]²` -/
def midPt (x : ℂ) : ℂ := ⟨(1 + clampU x.re) / 3, (1 + clampU x.im) / 3⟩

/-- the radius `2^{-n}/6` -/
def midR (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n / 6

lemma midR_pos (n : ℕ) : 0 < midR n := by unfold midR; positivity

lemma midR_le (n : ℕ) : midR n ≤ 1 / 6 := by
  unfold midR
  have : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma closedBall_midPt_subset (x : ℂ) (n : ℕ) : closedBall (midPt x) (midR n) ⊆ sqIn (1 / 6) := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h1 := (Complex.abs_re_le_norm (z - midPt x)).trans hz
  have h2 := (Complex.abs_im_le_norm (z - midPt x)).trans hz
  rw [Complex.sub_re] at h1; rw [Complex.sub_im] at h2
  have hr := midR_le n
  obtain ⟨a0, a1⟩ := clampU_mem x.re
  obtain ⟨b0, b1⟩ := clampU_mem x.im
  simp only [midPt] at h1 h2
  have := abs_le.mp h1; have := abs_le.mp h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma sqIn_sixth_subset : sqIn (1 / 6) ⊆ openSquare := sqIn_subset_openSquare (by norm_num)

lemma midPt_sub {x y : ℂ} (hx : x ∈ unitSq) (hy : y ∈ unitSq) :
    ‖midPt x - midPt y‖ = ‖x - y‖ / 3 := by
  obtain ⟨x0, x1, x2, x3⟩ := hx
  obtain ⟨y0, y1, y2, y3⟩ := hy
  have e : midPt x - midPt y = (3 : ℂ)⁻¹ * (x - y) := by
    apply Complex.ext <;>
    simp [midPt, clampU_eq x0 x1, clampU_eq x2 x3, clampU_eq y0 y1, clampU_eq y2 y3] <;> ring
  rw [e, norm_mul, norm_inv, Complex.norm_ofNat]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- the comparison family: `γ ×` circle averages around the middle third -/
def midZ (γ : ℝ) (X : Ω → Measure ℂ → ℝ) (n : ℕ) (x : ℂ) (ω : Ω) : ℝ :=
  γ * X ω (foldedCircle (midPt x) (midR n))

/-- `log max(r/6, d/3)` versus `log max(r, d)` -/
lemma abs_log_max_sixth {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    |Real.log (max (r / 6) (d / 3)) - Real.log (max r d) + Real.log 6| ≤ Real.log 2 := by
  have e : max (r / 6) (d / 3) = max r (2 * d) / 6 := by
    rw [show d / 3 = (2 * d) / 6 by ring, max_div_div_right (by norm_num : (0 : ℝ) ≤ 6)]
  have hm : 0 < max r d := lt_max_of_lt_left hr
  have hm2 : 0 < max r (2 * d) := lt_max_of_lt_left hr
  rw [e, Real.log_div hm2.ne' (by norm_num)]
  have l1 : Real.log (max r d) ≤ Real.log (max r (2 * d)) :=
    Real.log_le_log hm (max_le_max le_rfl (by linarith))
  have l2 : Real.log (max r (2 * d)) ≤ Real.log 2 + Real.log (max r d) := by
    rw [← Real.log_mul (by norm_num) hm.ne']
    refine Real.log_le_log hm2 (max_le ?_ ?_)
    · have := le_max_left r d; linarith
    · have := le_max_right r d; linarith
  have l3 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [abs_le]; constructor <;> linarith

/-- **the middle-third circle averages are `γ²`-log-correlated** -/
theorem logCorr_midZ (hX : IsZeroBoundaryGFFOn openSquare X P) (γ : ℝ) :
    ∃ c : ℝ, LogCorr (midZ γ X) P (γ ^ 2) c := by
  obtain ⟨cK, hcK⟩ := circleCov_two_sided sqIn_sixth_subset (convex_sqIn _)
    (isCompact_sqIn (by norm_num))
  have hB : ∀ n x, closedBall (midPt x) (midR n) ⊆ openSquare := fun n x =>
    (closedBall_midPt_subset x n).trans sqIn_sixth_subset
  refine ⟨γ ^ 2 * (cK + Real.log 6 + Real.log 2), ⟨fun n => ?_, fun n x => ?_, fun n x => ?_,
    fun n x y hx hy => ?_⟩⟩
  · have h := (hX.gaussian.comp_right fun x : ℂ => admC (midR_pos n) (hB n x)).smul fun _ => γ
    exact h
  · exact (hX.measurable_coord _).const_mul γ
  · show ∫ ω, γ * X ω (foldedCircle (midPt x) (midR n)) ∂P = 0
    rw [integral_const_mul, integral_circle hX (midR_pos n) (hB n x), mul_zero]
  · show |cov[fun ω => γ * X ω (foldedCircle (midPt x) (midR n)),
      fun ω => γ * X ω (foldedCircle (midPt y) (midR n)); P] +
        γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ _
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have h := hcK hX (midR_pos n) (closedBall_midPt_subset x n) (closedBall_midPt_subset y n)
    rw [midPt_sub hx hy] at h
    have hl := abs_log_max_sixth (r := (2 : ℝ)⁻¹ ^ n) (d := ‖x - y‖) (by positivity) (norm_nonneg _)
    rw [show (2 : ℝ)⁻¹ ^ n / 6 = midR n from rfl] at hl
    have h6 : 0 ≤ Real.log 6 := (Real.log_pos (by norm_num)).le
    set C := cov[fun ω => X ω (foldedCircle (midPt x) (midR n)),
      fun ω => X ω (foldedCircle (midPt y) (midR n)); P]
    have : |C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)| ≤ cK + Real.log 6 + Real.log 2 := by
      rw [abs_le] at h hl ⊢; constructor <;> linarith
    rw [show γ * (γ * C) + γ ^ 2 * Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖) =
      γ ^ 2 * (C + Real.log (max ((2 : ℝ)⁻¹ ^ n) ‖x - y‖)) by ring, abs_mul,
      abs_of_nonneg (sq_nonneg γ)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg γ)

end DGMC

end LQGMetric
