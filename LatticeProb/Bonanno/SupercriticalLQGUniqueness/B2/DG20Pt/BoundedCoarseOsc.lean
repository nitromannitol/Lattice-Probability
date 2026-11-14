/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.BoundedCoarseOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.CoarseOsc

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

private theorem scaled_mem_center_box {B r : ℝ} (_hB : 0 < B) (hr : 0 < r)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    (r : ℂ) * z ∈
      ferniqueBox ⟨-(B * r), -(B * r)⟩ (2 * B * r) := by
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hre' := abs_le.mp (hre.trans hz)
  have him' := abs_le.mp (him.trans hz)
  have hrel := mul_le_mul_of_nonneg_left hre'.1 hr.le
  have hreu := mul_le_mul_of_nonneg_left hre'.2 hr.le
  have himl := mul_le_mul_of_nonneg_left him'.1 hr.le
  have himu := mul_le_mul_of_nonneg_left him'.2 hr.le
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc]
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  constructor <;> constructor <;> nlinarith

private theorem zero_mem_center_box {B r : ℝ} (hB : 0 < B) (hr : 0 < r) :
    (0 : ℂ) ∈ ferniqueBox ⟨-(B * r), -(B * r)⟩ (2 * B * r) := by
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc,
    Complex.zero_re, Complex.zero_im]
  constructor <;> constructor <;> nlinarith

 


theorem phiMN_center_osc_tail_bounded
    {U : Set ℂ} (hU : Bornology.IsBounded U) :
    ∃ B : ℝ, 0 < B ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ k : ℕ, ∀ x : ℝ, 0 ≤ x →
      let r : ℝ := (2 : ℝ)⁻¹ ^ k
      P.real {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
        2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * (2 * B))) * Real.log 2) +
          ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * (2 * B))) + x) ≤
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
        Real.exp (-x ^ 2 / (2 * (6 * (Real.sqrt 2 * (2 * B))))) := by
  obtain ⟨R, hUR⟩ := hU.subset_ball (0 : ℂ)
  let B : ℝ := max R 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hUB : ∀ z ∈ U, ‖z‖ ≤ B := by
    intro z hz
    have h := hUR hz
    rw [Metric.mem_ball, dist_zero_right] at h
    exact h.le.trans (le_max_left R 1)
  refine ⟨B, hB, ?_⟩
  intro Ω _ P _ W hW k x hx
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  let x₀ : ℂ := ⟨-(B * r), -(B * r)⟩
  have h₀ : (0 : ℂ) ∈ ferniqueBox x₀ ((2 * B) * r) := by
    simpa only [x₀, mul_assoc] using zero_mem_center_box hB hr
  have htail := phiMN_center_osc_tail P W hW (by positivity : 0 < 2 * B)
    k x₀ h₀ hx
  have hsub : {ω | ∃ z ∈ (fun z : ℂ => (r : ℂ) * z) '' U,
        2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * (2 * B))) * Real.log 2) +
          ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * (2 * B))) + x) ≤
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ⊆
      {ω | ∃ z ∈ ferniqueBox x₀ ((2 * B) * r),
        ‖z‖ ≤ (2 * B) * r ∧
        2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * (2 * B))) * Real.log 2) +
          ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * (2 * B))) + x) ≤
            |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} := by
    rintro ω ⟨z, ⟨v, hv, rfl⟩, hlarge⟩
    refine ⟨(r : ℂ) * v, ?_, ?_, hlarge⟩
    · exact scaled_mem_center_box hB hr (hUB v hv)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [hUB v hv]
  exact (MeasureTheory.measureReal_mono hsub).trans (by simpa only [r] using htail)

end SupercriticalLQGUniqueness.B2.DG20Pt
