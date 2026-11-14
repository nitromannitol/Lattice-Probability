/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupport at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.BlockReconstruction
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinCopy
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EMain

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

 

theorem laneC_blocks_vanish_outside_support
    (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    {s : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
        (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
        T20B.blkKn Q W P K n b x z.1 = 0 ∧
        T20B.blkKn Q W P K n b x z.2 = 0 := by
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hzero : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
      ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
        T20B.blkKn Q W P K n b x ω = 0 := by
    rw [eventually_all_finset]
    intro b _
    exact T20B.blkVer_eq_zero_far hW Q (by positivity)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn)
      (T20B.measurableSet_hoBlock K b) hσ
  have hfirst := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  have hsecond := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  filter_upwards [hfirst, hsecond] with z hz₁ hz₂ b hb x hx
  exact ⟨hz₁ b hb x hx, hz₂ b hb x hx⟩

 

theorem laneC_resampled_field_eq_outside_support
    (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    {s : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
        (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
        psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2 = psiMN Q W P 0 n x z.1 := by
  filter_upwards [laneC_blocks_vanish_outside_support hW Q hKn hσ]
    with z hz b hb x hx
  obtain ⟨h₁, h₂⟩ := hz b hb x hx
  rw [h₁, h₂]
  ring

end SupercriticalLQGUniqueness.B2.DG20Conc
