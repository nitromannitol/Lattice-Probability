/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.CoarseOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem phiMN_center_osc_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) {C : ℝ} (hC : 0 < C) (k : ℕ)
    (x₀ : ℂ)
    (h₀ : (0 : ℂ) ∈ LQGMetric.SupTail.ferniqueBox x₀ (C * ((2 : ℝ)⁻¹ ^ k)))
    {x : ℝ} (hx : 0 ≤ x) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    P.real {ω | ∃ z ∈ LQGMetric.SupTail.ferniqueBox x₀ (C * r),
      ‖z‖ ≤ C * r ∧
      2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * C)) * Real.log 2) +
        LQGMetric.SupTail.ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C)) + x) ≤
          |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ≤
      Real.exp (-x ^ 2 / (2 * (6 * (Real.sqrt 2 * C)))) := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hCr : 0 < C * r := mul_pos hC hr
  have h := LQGMetric.DG.phiVer_osc_tail (P := P) hW hr hr1 hC x₀
    hCr hx (s := C * r)
  have hceil : (⌈(C * r) / (C * r)⌉₊ : ℝ) = 1 := by
    rw [div_self hCr.ne']
    norm_num
  have hsub : {ω | ∃ z ∈ LQGMetric.SupTail.ferniqueBox x₀ (C * r),
      ‖z‖ ≤ C * r ∧
      2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * C)) * Real.log 2) +
        LQGMetric.SupTail.ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C)) + x) ≤
          |phiMN W P 0 k z ω - phiMN W P 0 k 0 ω|} ⊆
      {ω | ∃ u ∈ LQGMetric.SupTail.ferniqueBox x₀ (C * r),
        ∃ v ∈ LQGMetric.SupTail.ferniqueBox x₀ (C * r),
          ‖u - v‖ ≤ C * r ∧
          2 * (Real.sqrt (2 * (6 * (Real.sqrt 2 * C)) *
            Real.log (2 * (⌈(C * r) / (C * r)⌉₊ : ℝ) ^ 2)) +
            LQGMetric.SupTail.ferniqueCF * Real.sqrt (3 * (Real.sqrt 2 * C)) + x) ≤
              |phiVer W P r 1 u ω - phiVer W P r 1 v ω|} := by
    rintro ω ⟨z, hz, hnorm, hlarge⟩
    refine ⟨z, hz, 0, h₀, ?_, ?_⟩
    · simpa only [sub_zero] using hnorm
    · simpa only [hceil, one_pow, mul_one, phiMN, pow_zero, sub_zero, r] using hlarge
  exact (MeasureTheory.measureReal_mono hsub).trans (by simpa only [r] using h)

end SupercriticalLQGUniqueness.B2.DG20Pt
