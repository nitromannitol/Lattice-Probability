/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1ROffSource at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupport
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSourceIdxVisited

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

universe u

theorem laneC1R_hoBlock_subset_dyBlock (K : ℕ) (b : ℤ × ℤ) :
    T20B.hoBlock K b ⊆ T20.dyBlock K b := by
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  have hinv : (2 : ℝ)⁻¹ ^ K = 1 / 2 ^ K := by rw [inv_pow, one_div]
  have hf1 := Int.floor_le (y.re * 2 ^ K)
  have hf2 := Int.lt_floor_add_one (y.re * 2 ^ K)
  have hg1 := Int.floor_le (y.im * 2 ^ K)
  have hg2 := Int.lt_floor_add_one (y.im * 2 ^ K)
  rw [h1] at hf1 hf2
  rw [h2] at hg1 hg2
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc, hinv]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [mul_one_div, div_le_iff₀ hp]; exact hf1
  · rw [mul_one_div, le_div_iff₀ hp]; exact hf2.le
  · rw [mul_one_div, div_le_iff₀ hp]; exact hg1
  · rw [mul_one_div, le_div_iff₀ hp]; exact hg2.le

 

theorem laneC_off_source_vanish.{v} (Q : PsiParams) (hR : Q.r₀ ≤ 1 / 100)
    (hε : Q.ε₀ ≤ 1 / 100) :
    ∃ K₀ : ℕ, ∀ {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ),
      IsWhiteNoise P W → ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
      ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K, b ∉ laneSourceIdx Q K →
        ∀ x ∈ (rectAB 1 1).toSet,
          T20B.blkKn Q W P K n b x z.1 = 0 ∧ T20B.blkKn Q W P K n b x z.2 = 0 := by
  obtain ⟨K₁, hK₁⟩ := laneC_eventually_two_le_K_pow Q.ε₀_pos
  refine ⟨max 6 K₁, ?_⟩
  intro Ω _ P W hW n K hK hKn
  have hK6 : 6 ≤ K := (le_max_left _ _).trans hK
  have hKe : 2 ≤ (K : ℝ) ^ Q.ε₀ := hK₁ K ((le_max_right _ _).trans hK)
  set s : ℝ := ((K : ℝ) ^ Q.ε₀ / 4) * (2 : ℝ)⁻¹ ^ K with hs
  have hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s :=
    fun t ht => laneC_sigma_le_quarter_source_scale Q hR hε (by omega)
      (lt_of_lt_of_le (by positivity) ht.1) ht.2
  filter_upwards [laneC_blocks_vanish_outside_support hW Q hKn hσ] with z hz b hb hbI x hx
  apply hz b hb x
  intro y hy
  have hδ := j1_source_radius_le_quarter Q K (by linarith) hK6
  have hnot : ¬ j1SourceSquarePred K (j1SourceRadius Q K) b := fun h =>
    hbI ((j1_mem_sourceIdx_iff hδ).mpr h)
  unfold j1SourceSquarePred at hnot
  rw [Set.not_subset] at hnot
  obtain ⟨y₀, hy₀, hy₀'⟩ := hnot
  have hxy₀ : j1SourceRadius Q K ≤ dist y₀ x := by
    by_contra h
    push Not at h
    exact hy₀' (Metric.mem_thickening_iff.mpr ⟨x, hx, h⟩)
  have hyy₀ : dist y y₀ ≤ 2 * (2 : ℝ)⁻¹ ^ K :=
    laneB_dyBlock_diameter_le_two (laneC1R_hoBlock_subset_dyBlock K b hy) hy₀
  have htri : dist y₀ x ≤ dist y₀ y + dist y x := dist_triangle _ _ _
  rw [dist_comm y₀ y] at htri
  rw [← dist_eq_norm, dist_comm]
  have hR' : j1SourceRadius Q K = 2 * (2 : ℝ)⁻¹ ^ K * (K : ℝ) ^ Q.ε₀ := rfl
  have hpow : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have : 2 * s ≤ j1SourceRadius Q K - 2 * (2 : ℝ)⁻¹ ^ K := by
    rw [hR', hs]; nlinarith
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
