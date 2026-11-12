/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.C8High at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C8

/-!
# DDDF Corollary 8 (`Cor:RSWpsi`), high quantiles: RSW for `ψ`

Task P2-DDDFRSW2. DDDF arXiv:1904.08021, `tightness.tex` l. 664–676, (3.39):
`ℓ̄^{(n)}_{a',b'}(ψ, 3ε^{1/C}) ≤ C ℓ̄^{(n)}_{a,b}(ψ, ε) e^{C√|log(ε/C)|}` (reading D-DDDF-8, stated
for `3ε^{1/C} < 1` as (3.37)). Proof as for (3.38) (`psi_rsw_low_quantile`): (2.27) from `ψ` to
`φ` at level shift `u = ε^{1/C}`, Prop 7 (3.37) for `φ` at `ε' = 2ε`, (2.27) back at level shift
`ε`. The level bookkeeping `3(2ε)^{1/C₀} + u ≤ 3u` (own elementary step) uses `C ≥ 2C₀`,
`C₀ ≥ 1` and `u < 1/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

theorem one_sub_ofReal' {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ≥0∞) - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub _ hx, ENNReal.ofReal_one]

/-- the level bookkeeping of (3.39) (own elementary step) -/
theorem level_le {ε C₀ C : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hC₀ : 1 ≤ C₀) (hC : 2 * C₀ ≤ C)
    (hu : ε ^ (1 / C) < 1 / 3) : 3 * (2 * ε) ^ (1 / C₀) ≤ 2 * ε ^ (1 / C) := by
  have hC₀0 : 0 < C₀ := by linarith
  set v := ε ^ (1 / (2 * C₀))
  have hv0 : 0 ≤ v := Real.rpow_nonneg hε.le _
  have hvu : v ≤ ε ^ (1 / C) := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
    (one_div_le_one_div_of_le (by linarith) hC)
  have e1 : (2 * ε) ^ (1 / C₀) = 2 ^ (1 / C₀) * v ^ 2 := by
    rw [Real.mul_rpow (by norm_num) hε.le, ← Real.rpow_two, ← Real.rpow_mul hε.le]
    congr 2; field_simp
  have h2 : (2 : ℝ) ^ (1 / C₀) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / C₀) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by rw [div_le_one hC₀0]; exact hC₀)
      _ = 2 := Real.rpow_one 2
  rw [e1]
  have hv2 : v ^ 2 ≤ ε ^ (1 / C) / 3 := by nlinarith
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / C₀)
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **DDDF Corollary 8, (3.39)** (`Cor:RSWpsi`, l. 672–675; high quantiles for `ψ`, uniform over
`(a,b), (a',b') ∈ [A,B]²`; reading D-DDDF-8), from Prop 5 and Prop 7 (3.37). -/
theorem psi_rsw_high_quantile (hW : IsWhiteNoise P W) (hξ : 0 ≤ ξ) (Q : PsiParams)
    (h10 : Prop10 ξ P W) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₀, hC₀, hR, hC₀1⟩ := rsw_high_quantile (ξ := ξ) hW hξ h10 hA hAB
  obtain ⟨C', c, hC', hc, htail⟩ := exists_tail_XAB_unif hW Q B
  set k : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log 1
  set k₃ : ℝ := 1 + 2 * |Real.log C₀|
  set s : ℝ := |ξ| * √(k / c) + |ξ| * √(k / c) + C₀ * √k₃ with hs
  have hs0 : 0 ≤ s := by positivity
  set C : ℝ := 2 * C₀ + 2 + s with hCdef
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun a b a' b' ha hb ha' hb' n ε hε hε2 h3u => ?_⟩
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha0 : 0 ≤ a := hA.le.trans ha.1
  have hb0 : 0 ≤ b := hA.le.trans hb.1
  have ha'0 : 0 ≤ a' := hA.le.trans ha'.1
  have hb'0 : 0 ≤ b' := hA.le.trans hb'.1
  have hε1 : ε < 1 := by linarith
  set u := ε ^ (1 / C) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hε _
  have hu3 : u < 1 / 3 := by linarith
  have hεu : ε ≤ u := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ u := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by rw [div_le_one hC0]; exact hC1)
  -- `ε < 1/9`
  have hε9 : ε < 1 / 9 := by
    have h1 : ε ^ (1 / 2 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
      (one_div_le_one_div_of_le (by norm_num) (by linarith))
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 := Real.sq_sqrt hε.le
    nlinarith [Real.sqrt_nonneg ε]
  set w := (2 * ε) ^ (1 / C₀) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have hlev : 3 * w ≤ 2 * u := level_le hε hε1 hC₀1 (by linarith) hu3
  set L := |Real.log (ε / C)|
  set M₁ : ℝ := √(max 1 (Real.log (C' / u)) / c)
  set M₂ : ℝ := √(max 1 (Real.log (C' / ε)) / c)
  -- step 1: from `ψ` to `φ` on `R_{a',b'}`
  have h1 := ellQ_psi_le_of_tail (ξ := ξ) hW Q ha'0 hb'0 (M := M₁) (Real.sqrt_nonneg _)
    (htail a' b' ha'.2 hb'.2 u hu0) (p := ENNReal.ofReal (1 - 3 * u))
    (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [← ENNReal.ofReal_add (by linarith) hu0.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add (by linarith) hu0.le] at h1
  -- monotonicity of the quantile
  have hm : ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * u + u)) ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * w)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 (by linarith))
      (by rw [ENNReal.ofReal_lt_one]; linarith) (ENNReal.ofReal_le_ofReal (by linarith))
  -- step 2: Prop 7 (3.37) for `φ` at `2ε`
  have h2 := hR a b a' b' ha hb ha' hb' n (2 * ε) (by positivity) (by linarith) (by linarith)
  unfold ellBarQ at h2
  rw [one_sub_ofReal' (by positivity), one_sub_ofReal' (by positivity)] at h2
  -- step 3: from `φ` back to `ψ` on `R_{a,b}`
  have h3 := ellQ_phi_le_of_tail (ξ := ξ) hW Q ha0 hb0 (M := M₂) (Real.sqrt_nonneg _)
    (htail a b ha.2 hb.2 ε hε) (p := ENNReal.ofReal (1 - 2 * ε))
    (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [← ENNReal.ofReal_add (by linarith) hε.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add (by linarith) hε.le,
    show 1 - 2 * ε + ε = 1 - ε by ring] at h3
  have hℓ := ellQ_nonneg (ξ := ξ) (P := P) hψ.cont hψ.meas (rectAB a b)
    (p := ENNReal.ofReal (1 - ε)) (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [ENNReal.ofReal_lt_one]; linarith)
  unfold ellBarQ
  rw [one_sub_ofReal' (by positivity), one_sub_ofReal' hε.le]
  set ℓ := ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal (1 - ε))
  -- the exponents
  have hM : M₁ ≤ M₂ := by
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (max_le_max le_rfl ?_) hc.le)
    exact Real.log_le_log (div_pos hC' hu0) (div_le_div_of_nonneg_left hC'.le hε hεu)
  have x2 : |ξ| * M₂ ≤ |ξ| * √(k / c) * √L := by
    have := tailExp_le (ξ := ξ) hC' hc (le_refl (1 : ℝ)) hε hε2 hC1
    rwa [div_one] at this
  have x1 : |ξ| * M₁ ≤ |ξ| * √(k / c) * √L :=
    (mul_le_mul_of_nonneg_left hM (abs_nonneg _)).trans x2
  have x3 : C₀ * √|Real.log (2 * ε / C₀)| ≤ C₀ * √k₃ * √L := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ((abs_log_div_le (by positivity) (by linarith) hC₀ hC1).trans ?_)
    exact mul_le_mul_of_nonneg_left (abs_log_div_mono hε (by linarith) (by linarith) hC1)
      (by positivity)
  have hsum : |ξ| * M₁ + |ξ| * M₂ + C₀ * √|Real.log (2 * ε / C₀)| ≤ C * √L := by
    have : s * √L ≤ C * √L := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have : s * √L = |ξ| * √(k / c) * √L + |ξ| * √(k / c) * √L + C₀ * √k₃ * √L := by ring
    linarith
  set E₁ := Real.exp (|ξ| * M₁)
  set E₂ := Real.exp (|ξ| * M₂)
  set E₃ := Real.exp (C₀ * √|Real.log (2 * ε / C₀)|)
  have hE : E₁ * E₂ * E₃ ≤ Real.exp (C * √L) := by
    simp only [E₁, E₂, E₃, ← Real.exp_add]; exact Real.exp_le_exp.2 hsum
  calc _ ≤ _ := h1
    _ ≤ E₁ * ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * w)) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal (1 - 2 * ε)) * E₃) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * (E₂ * ℓ) * E₃) := by
        gcongr
    _ = C₀ * ℓ * (E₁ * E₂ * E₃) := by ring
    _ ≤ C * ℓ * Real.exp (C * √L) := by
        gcongr
        linarith

end DDDF
end LQGMetric
