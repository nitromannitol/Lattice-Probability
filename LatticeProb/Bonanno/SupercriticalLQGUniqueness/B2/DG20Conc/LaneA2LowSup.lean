/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LowSup at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CoarseSup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

theorem laneA2_low_sup :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (hm0 : 1 ≤ m) (hm2 : m ≤ 2)
        (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
        (ha1 : a ≤ 1) (hb1 : b ≤ 1) (M : ℝ) (hM : 0 < M),
        P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-(M / A)^2 / Real.log 4)) := by
  obtain ⟨C₀, hC₀, htail⟩ := prop2_tail
  let A : ℝ := 3 + C₀ * Real.sqrt 3
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨16 * C₀, A, by positivity, hA, ?_⟩
  intro Ω _ P W hW m hm0 hm2 a b ha hb ha1 hb1 M hM
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have : Nonempty (rectAB a b).toSet := ⟨⟨0, by
    simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm,
      Complex.zero_re, Complex.zero_im, mem_Icc, zero_add]
    exact ⟨⟨le_rfl, ha⟩, ⟨le_rfl, hb⟩⟩⟩⟩
  have hY := isPhiVersion_phiMN hW (Nat.zero_le m)
  have hYae : ∀ x, (fun ω => phiMN W P 0 m x ω) =ᵐ[P]
      phi W ((2 : ℝ) ^ m)⁻¹ 1 x := by
    intro x
    simpa only [inv_pow, pow_zero, inv_one] using hY.ae_eq x
  have ht := htail hW m (phiMN W P 0 m) hYae hY.cont (M / A)
    (div_pos hM hA)
  have hsub := LQGMetric.DDDF.S6AB.rectAB_toSet_sub ha1 hb1
  have hle (ω : Ω) :
      (⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|) ≤
      ⨆ z : ferniqueBox 0 1, |phiMN W P 0 m z ω| := by
    apply ciSup_le
    intro z
    exact le_ciSup
      (LQGMetric.SupTail.bddAbove_abs_of_compact (isCompact_ferniqueBox 0 1) (hY.cont ω))
      (⟨z.1, hsub z.2⟩ : ferniqueBox 0 1)
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt 3 :=
    Real.sqrt_le_sqrt (by exact_mod_cast (show m ≤ 3 by omega))
  have hcoef : (m : ℝ) + C₀ * Real.sqrt m ≤ A := by
    dsimp [A]
    have hm : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    nlinarith
  have hsup : (M / A) * ((m : ℝ) + C₀ * Real.sqrt m) ≤ M := by
    calc
      _ ≤ (M / A) * A := mul_le_mul_of_nonneg_left hcoef (div_pos hM hA).le
      _ = M := by field_simp
  have hset :
      {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ⊆
      {ω | (M / A) * ((m : ℝ) + C₀ * Real.sqrt m) ≤
        ⨆ z : ferniqueBox 0 1, |phiMN W P 0 m z ω|} := by
    intro ω hω
    exact hsup.trans (hω.le.trans (hle ω))
  have hreal := (measureReal_mono hset).trans ht
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  have hm4 : (4 : ℝ)^m ≤ 16 := by
    interval_cases m <;> norm_num at *
  have hr : -(M / A)^2 * (m : ℝ) / Real.log 4 ≤
      -(M / A)^2 / Real.log 4 := by
    apply (div_le_div_iff_of_pos_right hlog4).2
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    nlinarith [sq_nonneg (M / A)]
  have he := Real.exp_le_exp.mpr hr
  have hbound : C₀ * 4^m * Real.exp (-(M / A)^2 * m / Real.log 4) ≤
      16 * C₀ * Real.exp (-(M / A)^2 / Real.log 4) := by
    have hc : 0 ≤ C₀ * 4^m := by positivity
    have hh : C₀ * 4^m ≤ 16 * C₀ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm4 hC₀.le
    exact (mul_le_mul_of_nonneg_left he hc).trans
      (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le)
  exact hreal.trans (by simpa only [Nat.cast_ofNat, mul_div_assoc] using hbound)

 
theorem laneA2_low_sup_all :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (hm2 : m ≤ 2)
        (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
        (ha1 : a ≤ 1) (hb1 : b ≤ 1) (M : ℝ) (hM : 0 < M),
        P {ω | M < ⨆ z : (rectAB a b).toSet, |phiMN W P 0 m z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-(M / A)^2 / Real.log 4)) := by
  obtain ⟨C, A, hC, hA, ht⟩ := laneA2_low_sup
  refine ⟨C, A, hC, hA, ?_⟩
  intro Ω _ P W hW m hm2 a b ha hb ha1 hb1 M hM
  by_cases hm : m = 0
  · subst m
    have hz := ae_phiMN_zero_zero hW
    have hevent : P {ω | M < ⨆ z : (rectAB a b).toSet,
        |phiMN W P 0 0 z ω|} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hz] with ω hω hmem
      have hh : (⨆ z : (rectAB a b).toSet, |phiMN W P 0 0 z ω|) = 0 := by
        simp [hω]
      exact (not_lt.mpr hM.le) (hh ▸ hmem)
    rw [hevent]
    exact bot_le
  · exact ht P W hW m (Nat.one_le_iff_ne_zero.mpr hm) hm2
      a b ha hb ha1 hb1 M hM

end SupercriticalLQGUniqueness.B2.DG20Conc
