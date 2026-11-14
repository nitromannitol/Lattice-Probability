/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2VarCond at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2EfronStein
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BStep4

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise J2Defs J2Inputs

private theorem j2_two_holder : (2 : ℝ).HolderConjugate 2 :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

 
theorem j2_sum_sq_le_sup_mul_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ≥0∞) :
    ∑ b ∈ s, x b ^ (2 : ℝ) ≤ s.sup' hs x * ∑ b ∈ s, x b := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  rw [ENNReal.rpow_two, sq]
  exact mul_le_mul' (Finset.le_sup' x hb) le_rfl

 

theorem j2_var_condExp_le_of_efronFactorsAt
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (hQ : PsiSmall Qψ) (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : EfronFactorsAt ξ Qψ P W K n A B) :
    Var[P[L24.logLenPsi ξ Qψ W P n |
        (inferInstance : MeasurableSpace (T20B.dyD → ℝ)).comap
          (fun ω => T20B.restrD (fun x => psiMN Qψ W P K n x ω))]; P] ≤
      Real.sqrt B * Real.sqrt A := by
  classical
  obtain ⟨Y, hYm, hcmp, hsum, hmax⟩ := hE
  set κ := fineKernel Qψ W P K n with hκ
  
  have hle : MeasurableSpace.comap (fun ω z => psiMN Qψ W P K n z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ)) ≤ (inferInstance : MeasurableSpace Ω) :=
    (measurable_pi_iff.mpr fun z => (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas z).comap_le
  have hXm : ∀ b, Measurable fun ω => ∫⁻ x, Y b x ∂(κ ω) := fun b =>
    ((hYm b).lintegral_kernel (κ := κ)).mono hle le_rfl
  set X : ℤ × ℤ → Ω → ℝ≥0∞ := fun b ω => ∫⁻ x, Y b x ∂(κ ω) with hX
  set S := T20B.nearIdx K
  have hS := nearIdx_nonempty K
  
  have hES := j2_efron_stein hW Qψ hQ ξ hKn
  refine hES.trans ?_
  
  have hblock : ∀ b : S, ∫ z, max (efronDiff ξ Qψ W P K n b z) 0 ^ 2 ∂(P.prod P) ≤
      (∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P).toReal := by
    intro b
    refine (T20B.integral_le_toReal_lintegral (fun z => sq_nonneg _)).trans ?_
    have hfin : ∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P ≠ ⊤ := by
      have h1 : ∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P ≤
          ∫⁻ ω, (∑ c ∈ S, X c ω) ^ (2 : ℝ) ∂P := by
        refine lintegral_mono fun ω => ?_
        exact ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun c => X c ω)
          (fun c _ => bot_le) b.2) (by norm_num)
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h1.trans hsum)
    refine ENNReal.toReal_mono hfin ?_
    have hmarg : ∫⁻ z, X b.1 z.1 ^ (2 : ℝ) ∂(P.prod P) = ∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P := by
      have := (measurePreserving_fst (μ := P) (ν := P)).lintegral_comp
        (f := fun ω => X b.1 ω ^ (2 : ℝ)) ((hXm b.1).pow_const _)
      simpa using this
    rw [← hmarg]
    refine lintegral_mono_ae ?_
    filter_upwards [hcmp b] with z hz
    have h0 : ENNReal.ofReal (max (efronDiff ξ Qψ W P K n b z) 0 ^ 2) =
        ENNReal.ofReal (efronDiff ξ Qψ W P K n b z) ^ (2 : ℝ) := by
      rw [ENNReal.rpow_two, ENNReal.ofReal_pow (le_max_right _ _)]
      congr 1
      rcases le_total (efronDiff ξ Qψ W P K n b z) 0 with h | h
      · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
      · rw [max_eq_left h]
    rw [h0]
    exact ENNReal.rpow_le_rpow hz (by norm_num)
  
  have hsumE : ∑ b : S, (∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P) =
      ∫⁻ ω, ∑ b ∈ S, X b ω ^ (2 : ℝ) ∂P := by
    rw [lintegral_finsetSum _ fun b _ => ((hXm b).pow_const _)]
    exact Finset.sum_coe_sort S (fun b => ∫⁻ ω, X b ω ^ (2 : ℝ) ∂P)
  have hCS : ∫⁻ ω, ∑ b ∈ S, X b ω ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal B ^ (1 / 2 : ℝ) * ENNReal.ofReal A ^ (1 / 2 : ℝ) := by
    have hmaxm : Measurable fun ω => S.sup' hS (fun b => X b ω) := by
      have := Finset.measurable_sup' hS (f := fun b => X b) (fun b _ => hXm b)
      convert this using 1
      funext ω
      rw [Finset.sup'_apply]
    have hsumm : Measurable fun ω => ∑ b ∈ S, X b ω :=
      Finset.measurable_sum _ fun b _ => hXm b
    have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq P j2_two_holder
      hmaxm.aemeasurable hsumm.aemeasurable
    calc ∫⁻ ω, ∑ b ∈ S, X b ω ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ω, S.sup' hS (fun b => X b ω) * ∑ b ∈ S, X b ω ∂P :=
          lintegral_mono fun ω => j2_sum_sq_le_sup_mul_sum S hS (fun b => X b ω)
      _ ≤ (∫⁻ ω, (S.sup' hS (fun b => X b ω)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
            (∫⁻ ω, (∑ b ∈ S, X b ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
          simpa only [Pi.mul_apply] using hholder
      _ ≤ ENNReal.ofReal B ^ (1 / 2 : ℝ) * ENNReal.ofReal A ^ (1 / 2 : ℝ) := by
          gcongr
  have hRHS : ENNReal.ofReal B ^ (1 / 2 : ℝ) * ENNReal.ofReal A ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt B * Real.sqrt A) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [hRHS] at hCS
  have hfinAll : ∀ b : S, ∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P ≠ ⊤ := by
    intro b
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ (hsumE ▸ hCS))
    exact Finset.single_le_sum (f := fun c : S => ∫⁻ ω, X c.1 ω ^ (2 : ℝ) ∂P)
      (fun c _ => bot_le) (Finset.mem_univ b)
  calc ∑ b : S, ∫ z, max (efronDiff ξ Qψ W P K n b z) 0 ^ 2 ∂(P.prod P)
      ≤ ∑ b : S, (∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P).toReal := Finset.sum_le_sum fun b _ => hblock b
    _ = (∑ b : S, ∫⁻ ω, X b.1 ω ^ (2 : ℝ) ∂P).toReal :=
        (ENNReal.toReal_sum fun b _ => hfinAll b).symm
    _ ≤ (ENNReal.ofReal (Real.sqrt B * Real.sqrt A)).toReal := by
        refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
        rw [hsumE]; exact hCS
    _ = Real.sqrt B * Real.sqrt A := ENNReal.toReal_ofReal (by positivity)

end SupercriticalLQGUniqueness.B2.DG20Conc
