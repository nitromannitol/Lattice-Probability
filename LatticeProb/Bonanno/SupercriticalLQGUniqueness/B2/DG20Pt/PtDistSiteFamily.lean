/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGoodSite
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem exists_pt_dist_good_site_family {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n : ℕ)
    (F : ℕ → Finset ℂ) (V : Set ℂ) (R T : ℝ) (t : ℕ → ℝ)
    (hR : 1 / 4 ≤ R) (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T t)
    (hinside : ∀ k ≤ n, ∀ x ∈ F k, x ∈ V)
    (hcover : ∀ k ≤ n, ∀ z ∈ V, ∃ x ∈ F k,
      dist z x < ((2 : ℝ)⁻¹) ^ (k + 2))
    (z : ℂ) (hz : z ∈ V) :
    ∃ x : ℕ → ℂ,
      (∀ k ≤ n,
        dist z (x k) < ((2 : ℝ)⁻¹) ^ k / 4 ∧
        ω ∈ ptDistSiteGood P W ξ Q ζ C n k (x k) T ∧
        |phiMN W P 0 k (x k) ω - phiMN W P 0 k z ω| ≤ R * t k) ∧
      ∀ k : ℕ, k + 1 ≤ n →
        dist (x (k + 1)) (x k) ≤
          3 * ((2 : ℝ)⁻¹ ^ (k + 1)) / 4 := by
  have hchoose (k : ℕ) : ∃ x : ℂ, k ≤ n →
      dist z x < ((2 : ℝ)⁻¹) ^ k / 4 ∧
      ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T ∧
      |phiMN W P 0 k x ω - phiMN W P 0 k z ω| ≤ R * t k := by
    by_cases hk : k ≤ n
    · obtain ⟨x, _, hdist, hsite, hfield⟩ :=
        pt_dist_good_site_near P W ξ Q ζ C n k hk F V R T t hR ω hgood
          (hinside k hk) (hcover k hk) z hz
      refine ⟨x, fun _ => ⟨?_, hsite, hfield⟩⟩
      have heq : ((2 : ℝ)⁻¹) ^ (k + 2) = ((2 : ℝ)⁻¹) ^ k / 4 := by
        rw [pow_add]
        norm_num
        ring
      rwa [heq] at hdist
    · exact ⟨z, fun h => False.elim (hk h)⟩
  let x (k : ℕ) : ℂ := Classical.choose (hchoose k)
  have hx (k : ℕ) (hk : k ≤ n) :
      dist z (x k) < ((2 : ℝ)⁻¹) ^ k / 4 ∧
      ω ∈ ptDistSiteGood P W ξ Q ζ C n k (x k) T ∧
      |phiMN W P 0 k (x k) ω - phiMN W P 0 k z ω| ≤ R * t k :=
    Classical.choose_spec (hchoose k) hk
  refine ⟨x, hx, ?_⟩
  intro k hk
  have hfat : dist z (x (k + 1)) < ((2 : ℝ)⁻¹) ^ (k + 1) / 4 :=
    (hx (k + 1) hk).1
  have hcoarse : dist z (x k) < ((2 : ℝ)⁻¹) ^ (k + 1) / 2 := by
    have hscale : ((2 : ℝ)⁻¹) ^ k = 2 * ((2 : ℝ)⁻¹) ^ (k + 1) := by
      rw [pow_succ]
      ring
    simpa only [hscale, show 2 * ((2 : ℝ)⁻¹) ^ (k + 1) / 4 =
      ((2 : ℝ)⁻¹) ^ (k + 1) / 2 by ring] using (hx k (by omega)).1
  exact pt_dist_adjacent_net_centers_close hfat hcoarse

end SupercriticalLQGUniqueness.B2.DG20Pt
