/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4REfronFactors at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3REfron
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RMax
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RHit
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RResampling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1ROffSource
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneB3PsiSource
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C17

 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise J2Defs

 

def LaneA4ExponentExists : Prop :=
  ∀ ξ : Ioi (0 : ℝ), ∃ Q : ℝ, IsLFPPExponent ξ Q

 
def laneA4RQψ : PsiParams where
  cut := Classical.choice exists_psiCutoff
  r₀ := 1 / 100
  ε₀ := 1 / 200
  r₀_pos := by norm_num
  ε₀_pos := by norm_num

theorem laneA4RQψ_psiSmall : PsiSmall laneA4RQψ := by
  intro t ht0 ht1
  refine le_trans ?_ (psiSmall_psiQ₀ t ht0 ht1)
  simp only [PsiParams.sigma, laneA4RQψ, psiQ₀, Real.rpow_one]
  have h1 : (1 : ℝ) ≤ 1 + |Real.log t| := le_add_of_nonneg_right (abs_nonneg _)
  have h2 : (1 + |Real.log t|) ^ (1 / 200 : ℝ) ≤ 1 + |Real.log t| := by
    calc (1 + |Real.log t|) ^ (1 / 200 : ℝ) ≤ (1 + |Real.log t|) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = 1 + |Real.log t| := Real.rpow_one _
  have hs : 0 ≤ √t := Real.sqrt_nonneg t
  have h3 : 0 ≤ (1 + |Real.log t|) ^ (1 / 200 : ℝ) := by positivity
  calc 1 / 100 * √t * (1 + |Real.log t|) ^ (1 / 200 : ℝ)
      ≤ 1 / 12 * √t * (1 + |Real.log t|) ^ (1 / 200 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ h3
        exact mul_le_mul_of_nonneg_right (by norm_num) hs
    _ ≤ 1 / 12 * √t * (1 + |Real.log t|) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem laneA4R_le_sq_of_rpow_half_le {x : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (h : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c) : x ≤ ENNReal.ofReal (c ^ 2) := by
  calc x = (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ (ENNReal.ofReal c) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (c ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two]

 

theorem laneA4R_efronDiff_eq_zero_of_vanish {Ω : Type*} [MeasurableSpace Ω] {ξ : ℝ}
    {Q : PsiParams} {W : WNSpace → Ω → ℝ} {P : Measure Ω} {K n : ℕ} (b : T20B.nearIdx K)
    {z : Ω × Ω} (h : ∀ x ∈ (rectAB 1 1).toSet,
      T20B.blkKn Q W P K n b x z.1 = 0 ∧ T20B.blkKn Q W P K n b x z.2 = 0) :
    efronDiff ξ Q W P K n b z = 0 := by
  have e : fineBlocks Q W P K n z.2 b = fineBlocks Q W P K n z.1 b := by
    funext c
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 c.2
    have hx : (c : ℂ) ∈ (rectAB 1 1).toSet := L23.grid_subset hk
    show T20B.blkKn Q W P K n b.1 c z.2 = T20B.blkKn Q W P K n b.1 c z.1
    rw [(h c hx).1, (h c hx).2]
  unfold efronDiff
  rw [e, Function.update_eq_self, sub_self]

 
theorem laneA4_efronFactors_of_exponent (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) (ξ : Ioi (0 : ℝ)) (Qe : ℝ) (hQe : IsLFPPExponent ξ Qe)
    (hQpos : 0 < Qe) :
    ∃ Qψ : PsiParams, PsiSmall Qψ ∧ ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧
      J2Inputs.EfronFactors ξ Qψ p := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hr : laneA4RQψ.r₀ ≤ 1 / 100 := by norm_num [laneA4RQψ]
  have hε : laneA4RQψ.ε₀ ≤ 1 / 100 := by norm_num [laneA4RQψ]
  have hε' : laneA4RQψ.ε₀ < 1 / 100 := by norm_num [laneA4RQψ]
  obtain ⟨p, hp, hp2, hunit, hJ⟩ :=
    j1_fixed_p_at.{0} hξ laneA4RQψ (by norm_num [laneA4RQψ])
  have hB3 := laneB3_fixedP_subadd_tails ξ Qe hQe laneA4RQψ hp hp2 hunit
  obtain ⟨Kc, hKc⟩ := laneC_eventual_hit_resampling.{0} laneA4RQψ hr hε (ξ : ℝ)
  obtain ⟨Kv, hKv⟩ := laneC_off_source_vanish.{0} laneA4RQψ hr hε
  refine ⟨laneA4RQψ, laneA4RQψ_psiSmall, p, hp, hp2, ?_⟩
  intro C hC
  obtain ⟨A, KA, hA, hA3⟩ :=
    laneA3_sum_condHit_L2_le.{0} laneA4RQψ hε' (ξ : ℝ) hξ p hp hp2 hJ C hC
  set α := hitExponent (ξ : ℝ) Qe with hαdef
  have hα : 0 < α := hitExponent_pos hξ hQpos
  obtain ⟨KM, hA4⟩ := laneA4_max_condHit_L2_le_of_inputs.{0} hC2 hInd laneA4RQψ hε' ξ Qe
    hQe p hp hp2 hJ hB3 (max C 1) (α / 2) (lt_of_lt_of_le one_pos (le_max_right _ _))
    (by positivity)
  refine ⟨A, 1, α / 2, max (max KA KM) (max Kc Kv), by positivity, ?_⟩
  intro Ω _ _ P _ W hW K n hK hKn hH
  have hKA : KA ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK
  have hKM : KM ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hK
  have hKc' : Kc ≤ K := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hKv' : Kv ≤ K := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  have hH' : LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
      Real.exp (max C 1 * Real.sqrt (K : ℝ)) :=
    hH.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  
  obtain ⟨γ, hγ, hhits⟩ := laneA3R_exists_field_selection hW laneA4RQψ (ξ : ℝ)
  have hhitsΩ : ∀ j : ℕ, ∀ b : ℤ × ℤ,
      MeasurableSet (laneCHits γ j n K (laneBCoarseIndex laneA4RQψ K) b) := fun j b =>
    laneA3RFieldSigma_le hW laneA4RQψ n _ (hhits j n K _ b)
  choose w hw hwae using fun b : ℤ × ℤ =>
    laneA3R_hitWeight_factor hW laneA4RQψ (ξ : ℝ) γ n K (fun j m b' => hhits j n K m b') b
  have hfieldm : Measurable (laneA3RField laneA4RQψ W P n) :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := laneA4RQψ) hW (Nat.zero_le n)).meas
  have hFkm : Measurable fun ω (x : ℂ) => psiMN laneA4RQψ W P K n x ω :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := laneA4RQψ) hW hKn).meas
  have hfine : MeasurableSpace.comap (fun ω (x : ℂ) => psiMN laneA4RQψ W P K n x ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ)) ≤ (inferInstance : MeasurableSpace Ω) :=
    hFkm.comap_le
  set I := laneSourceIdx laneA4RQψ K with hIdef
  let Y : ℤ × ℤ → Ω → ℝ≥0∞ := fun b =>
    if b ∈ I then fun ω => w b (laneA3RField laneA4RQψ W P n ω) else fun _ => 0
  have hYm : ∀ b, Measurable (Y b) := by
    intro b
    by_cases hb : b ∈ I
    · simp only [Y, if_pos hb]; exact (hw b).comp hfieldm
    · simp only [Y, if_neg hb]; exact measurable_const
  
  have hYae : ∀ b : ℤ × ℤ, ∀ᵐ ω ∂P,
      ∫⁻ x, Y b x ∂(J2Inputs.fineKernel laneA4RQψ W P K n ω) =
        if b ∈ I then ∫⁻ x, laneA3HitWeight P W hW laneA4RQψ (ξ : ℝ) γ n K b x
          ∂(condExpKernel P (laneFineStar laneA4RQψ W P K n) ω) else 0 := by
    intro b
    by_cases hb : b ∈ I
    · filter_upwards [laneA3R_kernel_transfer hInd P W hW laneA4RQψ hKn (hw b) (hwae b),
        laneC_conditional_lintegral_mono_ae P hfine (hwae b).le,
        laneC_conditional_lintegral_mono_ae P hfine (hwae b).symm.le] with ω h1 h2 h3
      simp only [Y, if_pos hb]
      rw [h1]
      exact le_antisymm h3 h2
    · exact Eventually.of_forall fun ω => by simp [Y, hb]
  have hYall := ae_all_iff.mpr hYae
  have hsub : I ⊆ T20B.nearIdx K := laneSourceIdx_subset_nearIdx laneA4RQψ K
  refine ⟨Y, hYm, ?_, ?_, ?_⟩
  · 
    intro b
    by_cases hb : b.1 ∈ I
    · have hC1 := hKc P W hW n K hKc' hKn γ hγ
      have h := laneA3R_efron_clause_i hInd P W hW laneA4RQψ laneA4RQψ_psiSmall (ξ : ℝ) hKn γ
        hC1 b (hw b.1) (hwae b.1)
      filter_upwards [h] with z hz
      simp only [Y, if_pos hb]
      exact hz
    · filter_upwards [hKv P W hW n K hKv' hKn] with z hz
      rw [laneA4R_efronDiff_eq_zero_of_vanish b (hz b.1 b.2 hb), ENNReal.ofReal_zero]
      exact bot_le
  · 
    have hsumae : ∀ᵐ ω ∂P,
        (∑ b ∈ T20B.nearIdx K, ∫⁻ x, Y b x ∂(J2Inputs.fineKernel laneA4RQψ W P K n ω)) =
          ∑ b ∈ I, ∫⁻ x, laneA3HitWeight P W hW laneA4RQψ (ξ : ℝ) γ n K b x
            ∂(condExpKernel P (laneFineStar laneA4RQψ W P K n) ω) := by
      filter_upwards [hYall] with ω hω
      rw [Finset.sum_congr rfl fun b _ => hω b, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr hsub]
    rw [lintegral_congr_ae (hsumae.mono fun ω h => by rw [h])]
    have hc : 0 ≤ A * (K : ℝ) * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)) := by positivity
    exact laneA4R_le_sq_of_rpow_half_le hc
      (hA3 P W hW n K hKA hKn hH γ hγ hhitsΩ)
  · 
    have hsupae : ∀ᵐ ω ∂P,
        (T20B.nearIdx K).sup' (nearIdx_nonempty K)
            (fun b => ∫⁻ x, Y b x ∂(J2Inputs.fineKernel laneA4RQψ W P K n ω)) =
          I.sup fun b => ∫⁻ x, laneA3HitWeight P W hW laneA4RQψ (ξ : ℝ) γ n K b x
            ∂(condExpKernel P (laneFineStar laneA4RQψ W P K n) ω) := by
      filter_upwards [hYall] with ω hω
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun b _ => ?_
        rw [hω b]
        split_ifs with hb
        · exact Finset.le_sup (f := fun b => ∫⁻ x, laneA3HitWeight P W hW laneA4RQψ (ξ : ℝ)
            γ n K b x ∂(condExpKernel P (laneFineStar laneA4RQψ W P K n) ω)) hb
        · exact bot_le
      · refine Finset.sup_le fun b hb => ?_
        refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (hsub hb))
        rw [hω b, if_pos hb]
    rw [lintegral_congr_ae (hsupae.mono fun ω h => by rw [h])]
    have hc : 0 ≤ (1 : ℝ) * (2 : ℝ) ^ (-(α / 2 * (K : ℝ))) := by positivity
    have e : (1 : ℝ) * (2 : ℝ) ^ (-(α / 2 * (K : ℝ))) =
        (2 : ℝ) ^ (-(hitExponent (ξ : ℝ) Qe - α / 2) * (K : ℝ)) := by
      rw [one_mul, ← hαdef]; congr 1; ring
    rw [e] at hc ⊢
    exact laneA4R_le_sq_of_rpow_half_le hc
      (hA4 P W hW n K hKM hKn hH' γ hγ hhitsΩ)

 

theorem laneA4_efronFactors_of_inputs (hC2 : LaneC2StarAt.{0})
    (hInd : LaneFineStarIndepCoarse.{0}) (hEx : LaneA4ExponentExists)
    (hPos : Iface.DG20ExponentPositive) :
    ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧ ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧
      J2Inputs.EfronFactors ξ Qψ p := by
  intro ξ
  obtain ⟨Qe, hQe⟩ := hEx ξ
  exact laneA4_efronFactors_of_exponent hC2 hInd ξ Qe hQe (hPos ξ Qe hQe)

end SupercriticalLQGUniqueness.B2.DG20Conc
