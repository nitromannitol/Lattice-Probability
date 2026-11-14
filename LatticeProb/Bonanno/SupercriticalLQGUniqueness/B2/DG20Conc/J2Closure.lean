/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2Closure at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Step
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2Induction
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.QuantileVariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.B4ExponentRelation
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20

 










set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise J2Defs J2Inputs

 

theorem j2_psi_ratio_facts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Qψ : PsiParams) (ξ : ℝ) {q : ℝ}
    (hq0 : 0 < q) (hq : q < 1 / 2) (k : ℕ) :
    0 ≤ ellBarQ ξ P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal q) /
        ellQ ξ P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal q) ∧
    ellBarQ ξ P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal q) /
        ellQ ξ P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal q) ≤
      Real.exp (Real.sqrt 2 / q * Real.sqrt (Var[L24.logLenPsi ξ Qψ W P k; P])) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hv := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le k)
  have hq1 : ENNReal.ofReal q < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  have hpos := T20.ellQ_pos (P := P) (ξ := ξ) hv.cont hv.meas (ENNReal.ofReal_pos.mpr hq0) hq1
  have hle := T20.ellQ_le_ellBarQ (P := P) (ξ := ξ) (Y := psiMN Qψ W P 0 k) hq0 hq
  refine ⟨div_nonneg (hpos.le.trans hle) hpos.le, ?_⟩
  refine (truncated_quantile_ratio_le hW Qψ ξ hq0 hq k).trans (le_of_eq ?_)
  congr 1
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

 
theorem j2_variance_bounded_of_efronFactors {Ω : Type} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (ξ : Ioi (0 : ℝ)) (Qψ : PsiParams)
    (hQ : PsiSmall Qψ) {p : ℝ} (hp0 : 0 < p) (hp : p < 2⁻¹) (hEF : EfronFactors ξ Qψ p) :
    ∃ M : ℝ, ∀ k, Var[L24.logLenPsi (ξ : ℝ) Qψ W P k; P] ≤ M := by
  have hp' : p < 1 / 2 := by linarith
  obtain ⟨Ccmp, hCcmp, hcmp⟩ := LambdaN_le_LambdaNPsi hW Qψ (ξ : ℝ) hp0 hp'
  obtain ⟨Cv, hCv0, hCv⟩ := L24.psi_memLp_variance hW Qψ (ξ : ℝ)
  have hq0 : 0 < p / 2 := by positivity
  have hq : p / 2 < 1 / 2 := by linarith
  have hfacts := j2_psi_ratio_facts hW Qψ (ξ : ℝ) hq0 hq
  obtain ⟨K, -, hV, -⟩ := j2_abstract_induction
    (Λ := fun n => LambdaN (ξ : ℝ) W P n (ENNReal.ofReal p))
    (r := fun k => ellBarQ (ξ : ℝ) P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
      ellQ (ξ : ℝ) P (psiMN Qψ W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)))
    (V := fun k => Var[L24.logLenPsi (ξ : ℝ) Qψ W P k; P])
    (Ccmp := Ccmp) (cq := Real.sqrt 2 / (p / 2)) (Cv := Cv) (s := (ξ : ℝ) ^ 2 * Real.log 2)
    hCcmp (by positivity) hCv0 (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num)))
    (fun n => hcmp n) (fun k => (hfacts k).1) (fun k => (hfacts k).2) (fun k => (hCv k).2)
    (fun C hC => by
      obtain ⟨K₁, hK₁⟩ := j2_step_of_efronFactors ξ Qψ hQ hEF C hC
      exact ⟨K₁, fun K hK k hk hH => hK₁ K hK P W hW k hk hH⟩)
  exact ⟨_, hV⟩

 
theorem j2_quantileRatioAllP_of_efronFactors
    (hJ : ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧
      ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ EfronFactors ξ Qψ p) :
    QuantileRatioAllP := by
  intro ξ p' hp'0 hp'
  obtain ⟨Qψ, hQ, p, hp0, hp, hEF⟩ := hJ ξ
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  haveI : IsProbabilityMeasure LQGDimension.ExistAsm.stdP := hW₀.isProbabilityMeasure
  obtain ⟨M, hM⟩ := j2_variance_bounded_of_efronFactors LQGDimension.ExistAsm.stdP W₀ hW₀ ξ
    Qψ hQ hp0 hp hEF
  have hp'' : p' < 1 / 2 := by linarith
  obtain ⟨C', hC', hcmp'⟩ := LambdaN_le_LambdaNPsi hW₀ Qψ (ξ : ℝ) hp'0 hp''
  have hq0 : 0 < p' / 2 := by positivity
  have hq : p' / 2 < 1 / 2 := by linarith
  have hfacts := j2_psi_ratio_facts hW₀ Qψ (ξ : ℝ) hq0 hq
  refine ⟨C' * Real.exp (Real.sqrt 2 / (p' / 2) * Real.sqrt (max M 0)), ?_⟩
  intro Ω _ P W hW n
  rw [laneA_LambdaN_eq hW hW₀]
  refine (hcmp' n).trans (mul_le_mul_of_nonneg_left ?_ hC'.le)
  refine Finset.sup'_le _ _ fun k _ => (hfacts k).2.trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((hM k).trans (le_max_left _ _)))
    (by positivity)

 
theorem j2_dg20QuantileRatio_of_efronFactors
    (hJ : ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧
      ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ EfronFactors ξ Qψ p) :
    Iface.DG20QuantileRatio :=
  dg20QuantileRatio_of_allP (j2_quantileRatioAllP_of_efronFactors hJ)

 
theorem j2_dg20ExponentRelation_of_efronFactors
    (hJ : ∀ ξ : Ioi (0 : ℝ), ∃ Qψ : PsiParams, PsiSmall Qψ ∧
      ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ EfronFactors ξ Qψ p) :
    Iface.DG20ExponentRelation :=
  b4_exponentRelation_of_quantileRatioAllP (j2_quantileRatioAllP_of_efronFactors hJ)

end SupercriticalLQGUniqueness.B2.DG20Conc
