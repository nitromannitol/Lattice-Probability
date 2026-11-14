/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGoodSite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesInsideTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_good_site_near {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ) (hkn : k ≤ n)
    (F : ℕ → Finset ℂ) (V : Set ℂ) (R T : ℝ) (t : ℕ → ℝ)
    (hR : 1 / 4 ≤ R) (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T t)
    (hinside : ∀ x ∈ F k, x ∈ V)
    (hcover : ∀ z ∈ V, ∃ x ∈ F k,
      dist z x < ((2 : ℝ)⁻¹) ^ (k + 2))
    (z : ℂ) (hz : z ∈ V) :
    ∃ x ∈ F k,
      dist z x < ((2 : ℝ)⁻¹) ^ (k + 2) ∧
      ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T ∧
      |phiMN W P 0 k x ω - phiMN W P 0 k z ω| ≤ R * t k := by
  obtain ⟨x, hx, hzx⟩ := hcover z hz
  have hscale := hgood k (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
  have hsite : ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T := hscale.1 x hx
  have hr : ((2 : ℝ)⁻¹) ^ k > 0 := by positivity
  have hdist : dist x z ≤ R * ((2 : ℝ) ^ k)⁻¹ := by
    have hpow : ((2 : ℝ)⁻¹) ^ (k + 2) = ((2 : ℝ)⁻¹) ^ k / 4 := by
      rw [pow_add]
      norm_num
      ring
    have hrpow : ((2 : ℝ) ^ k)⁻¹ = ((2 : ℝ)⁻¹) ^ k := by
      rw [inv_pow]
    have hzx' : dist x z < ((2 : ℝ)⁻¹) ^ k / 4 := by
      rw [dist_comm, ← hpow]
      exact hzx
    rw [hrpow]
    nlinarith
  have hf := hscale.2 z hz x (hinside x hx) (by simpa [dist_comm] using hdist)
  rw [abs_sub_comm] at hf
  exact ⟨x, hx, hzx, hsite, hf⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
