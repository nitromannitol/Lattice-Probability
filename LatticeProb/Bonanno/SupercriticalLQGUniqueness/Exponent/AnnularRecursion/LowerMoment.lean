/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.LowerMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Law
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Inputs.Gaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRatio




 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

theorem image_add_reProdIm (c : ℂ) (s t : Set ℝ) :
    (fun x : ℂ => x + c) '' (s ×ℂ t) =
      ((fun r => r + c.re) '' s) ×ℂ ((fun r => r + c.im) '' t) := by
  ext z
  simp only [mem_image, Complex.mem_reProdIm]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨⟨x.re, hx1, by simp⟩, ⟨x.im, hx2, by simp⟩⟩
  · rintro ⟨⟨a, ha, hare⟩, ⟨b, hb, hbim⟩⟩
    refine ⟨⟨a, b⟩, ⟨ha, hb⟩, ?_⟩
    apply Complex.ext
    · simpa using hare
    · simpa using hbim

private theorem motion_I_eq : (fun x : ℂ => ((1 : Circle) : ℂ) * x + Complex.I) =
    fun x : ℂ => x + Complex.I := by
  funext x; simp

theorem centralRect0_toSet :
    (fun x : ℂ => ((1 : Circle) : ℂ) * x + Complex.I) '' (rectAB 1 1).toSet =
      (Exponent.PaidDuality.centralRect 0).toSet := by
  rw [motion_I_eq]
  simp only [MarkedRect.toSet, rectAB, Exponent.PaidDuality.centralRect, image_add_reProdIm,
    image_add_const_Icc, Complex.I_re, Complex.I_im]
  norm_num

theorem centralRect0_side₁ :
    (fun x : ℂ => ((1 : Circle) : ℂ) * x + Complex.I) '' (rectAB 1 1).side₁ =
      (Exponent.PaidDuality.centralRect 0).side₁ := by
  rw [motion_I_eq]
  simp only [MarkedRect.side₁, rectAB, Exponent.PaidDuality.centralRect, ite_true, image_add_reProdIm,
    image_add_const_Icc, image_singleton, Complex.I_re, Complex.I_im]
  norm_num

theorem centralRect0_side₂ :
    (fun x : ℂ => ((1 : Circle) : ℂ) * x + Complex.I) '' (rectAB 1 1).side₂ =
      (Exponent.PaidDuality.centralRect 0).side₂ := by
  rw [motion_I_eq]
  simp only [MarkedRect.side₂, rectAB, Exponent.PaidDuality.centralRect, ite_true, image_add_reProdIm,
    image_add_const_Icc, image_singleton, Complex.I_re, Complex.I_im]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem map_lenObs_centralRect0 (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) :
    P.map (lenObs ξ (phiMN W P 0 n) (Exponent.PaidDuality.centralRect 0)) =
      P.map (lenObs ξ (phiMN W P 0 n) (rectAB 1 1)) := by
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  ext S hS
  rw [Measure.map_apply (measurable_lenObs hφ.cont hφ.meas _) hS,
    Measure.map_apply (measurable_lenObs hφ.cont hφ.meas _) hS]
  have hS' : MeasurableSet (ENNReal.toReal ⁻¹' S) := ENNReal.measurable_toReal hS
  have h := measure_crossLenIn_phiMN_motion (ξ := ξ) hW (Nat.zero_le n) 1 Complex.I
    (K := (rectAB 1 1).toSet) (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂)
    (rectAB 1 1).isCompact_toSet hS'
  rw [centralRect0_toSet, centralRect0_side₁, centralRect0_side₂] at h
  exact h

 
theorem ellQ_centralRect0 (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ) (p : ℝ≥0∞) :
    ellQ ξ P (phiMN W P 0 n) (Exponent.PaidDuality.centralRect 0) p = ellN ξ W P n p := by
  simp only [ellN, ellQ, map_lenObs_centralRect0 hW ξ n]

 
theorem lintegral_pow_ge_ellN (hW : IsWhiteNoise P W) (ξ : ℝ) {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) (n j : ℕ) :
    (1 - p) * (ENNReal.ofReal (ellN ξ W P n p)) ^ j ≤
      ∫⁻ ω, (Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω)) ^ j ∂P := by
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have h := Exponent.PolygonalCost.lintegral_polyAnnularCost_pow_ge_quantile (P := P) hφ.cont hφ.meas ξ 0
    hp0 hp1 j
  rwa [ellQ_centralRect0 hW ξ n p] at h

 
theorem lambdaN_mul_exp_le_ellN (hW : IsWhiteNoise P W) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) (n : ℕ) :
    lambdaN ξ W P n * Real.exp (-(Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p * Real.sqrt n)) ≤
      ellN ξ W P n (ENNReal.ofReal p) := by
  have := hW.isProbabilityMeasure
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp0
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := by
    rw [← ofReal_half_eq']
    exact ENNReal.ofReal_le_ofReal hp.le
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hΛn : ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) /
      ellN ξ W P k (ENNReal.ofReal p)) (Finset.self_mem_range_succ n)
  have hlam : lambdaN ξ W P n ≤ ellBarN ξ W P n (ENNReal.ofReal p) :=
    T20B.lambdaN_le_ellBarN hpq0 hpq n
  have hratio := Inputs.Gaussian.quantile_ratio_sqrt hW ξ hp0 hp n
  set C : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / p * Real.sqrt n
  have h1 : lambdaN ξ W P n ≤ Real.exp C * ellN ξ W P n (ENNReal.ofReal p) := by
    calc lambdaN ξ W P n ≤ ellBarN ξ W P n (ENNReal.ofReal p) := hlam
      _ = ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) *
          ellN ξ W P n (ENNReal.ofReal p) := (div_mul_cancel₀ _ hℓ0.ne').symm
      _ ≤ LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) :=
          mul_le_mul_of_nonneg_right hΛn hℓ0.le
      _ ≤ Real.exp C * ellN ξ W P n (ENNReal.ofReal p) :=
          mul_le_mul_of_nonneg_right hratio hℓ0.le
  calc lambdaN ξ W P n * Real.exp (-C) ≤
      Real.exp C * ellN ξ W P n (ENNReal.ofReal p) * Real.exp (-C) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ellN ξ W P n (ENNReal.ofReal p) := by
        rw [mul_comm (Real.exp C), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
          mul_one]

 

theorem lower_moment (hW : IsWhiteNoise P W) (ξ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ENNReal.ofReal (Real.exp (-(C * Real.sqrt n + C)) * lambdaN ξ W P n) ≤
        ∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P := by
  have := hW.isProbabilityMeasure
  set C₁ : ℝ := Real.sqrt (2 * ξ ^ 2 * Real.log 2) / (1 / 4)
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨C₁ + 1, by positivity, fun n => ?_⟩
  have hp0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hp : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hlow := lambdaN_mul_exp_le_ellN hW ξ hp0 hp n
  have hmom := lintegral_pow_ge_ellN hW ξ (p := ENNReal.ofReal (1 / 4))
    (ENNReal.ofReal_pos.2 hp0) (by rw [ENNReal.ofReal_lt_one]; norm_num) n 1
  simp only [pow_one] at hmom
  have hlam0 : 0 ≤ lambdaN ξ W P n := by
    have hpq0 : 0 < ENNReal.ofReal (1 / 4 : ℝ) := ENNReal.ofReal_pos.2 hp0
    have hpq : ENNReal.ofReal (1 / 4 : ℝ) ≤ 2⁻¹ := by
      rw [← ofReal_half_eq']; exact ENNReal.ofReal_le_ofReal (by norm_num)
    exact (T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n).le.trans
      (T20B.ellN_le_lambdaN hpq0 hpq n)
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4) = ENNReal.ofReal (3 / 4) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  rw [hone, ← ENNReal.ofReal_mul (by norm_num)] at hmom
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmom
  have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have he1 : Real.exp (-(1 : ℝ)) ≤ 3 / 4 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hsplit : Real.exp (-((C₁ + 1) * Real.sqrt n + (C₁ + 1))) ≤
      3 / 4 * Real.exp (-(C₁ * Real.sqrt n)) := by
    have h2 : -((C₁ + 1) * Real.sqrt n + (C₁ + 1)) ≤ -(1 : ℝ) + -(C₁ * Real.sqrt n) := by
      nlinarith
    calc Real.exp (-((C₁ + 1) * Real.sqrt n + (C₁ + 1))) ≤
        Real.exp (-(1 : ℝ) + -(C₁ * Real.sqrt n)) := Real.exp_le_exp.2 h2
      _ = Real.exp (-(1 : ℝ)) * Real.exp (-(C₁ * Real.sqrt n)) := Real.exp_add _ _
      _ ≤ 3 / 4 * Real.exp (-(C₁ * Real.sqrt n)) :=
          mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
  calc Real.exp (-((C₁ + 1) * Real.sqrt n + (C₁ + 1))) * lambdaN ξ W P n ≤
      3 / 4 * Real.exp (-(C₁ * Real.sqrt n)) * lambdaN ξ W P n :=
        mul_le_mul_of_nonneg_right hsplit hlam0
    _ = 3 / 4 * (lambdaN ξ W P n * Real.exp (-(C₁ * Real.sqrt n))) := by ring
    _ ≤ 3 / 4 * ellN ξ W P n (ENNReal.ofReal (1 / 4)) :=
        mul_le_mul_of_nonneg_left hlow (by norm_num)



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
