/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBObigGaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPhiOscGaussianEvent

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

def j1NearbyBox : Set ℂ :=
  Icc (-1 : ℝ) 2 ×ℂ Icc (-1 : ℝ) 2

theorem j1_closedBall_nearby_subset_bigBox {v : ℂ}
    (hv : v ∈ j1NearbyBox) {r : ℝ} (hr : r ≤ 1) :
    closedBall v r ⊆ T20D.bigBox := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  simp only [j1NearbyBox, Complex.mem_reProdIm, mem_Icc] at hv
  have hre := (Complex.abs_re_le_norm (z - v)).trans hz
  have him := (Complex.abs_im_le_norm (z - v)).trans hz
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  simp only [T20D.bigBox, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨by linarith [hre.1, hv.1.1], by linarith [hre.2, hv.1.2]⟩,
    by linarith [him.1, hv.2.1], by linarith [him.2, hv.2.2]⟩

theorem j1_phiMN_nearby_oscillation_bad_event :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (K : ℕ) {ι : Type*} (A : ι → Set ℂ) (v : ι → ℂ) (r B x : ℝ),
      r ≤ 1 → 0 ≤ B → 0 ≤ x → r ≤ B * (2 : ℝ)⁻¹ ^ K →
      (∀ i, v i ∈ j1NearbyBox) →
      (∀ i, A i ⊆ closedBall (v i) r) →
      P.real {ω | ∃ i, ∃ z ∈ A i,
        B * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ :=
    laneB_phiMN_coarse_oscillation_gaussian_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K ι A v r B x hr hB hx hrB hv hA
  apply htail hW K A v B x hB hx
  · intro i z hz
    exact j1_closedBall_nearby_subset_bigBox (hv i) hr (hA i hz)
  · intro i
    exact j1_closedBall_nearby_subset_bigBox (hv i)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (mem_closedBall_self (by norm_num))
  · intro i z hz
    have hz' := hA i hz
    rw [mem_closedBall, dist_eq_norm] at hz'
    exact hz'.trans hrB

end SupercriticalLQGUniqueness.B2.DG20Conc
