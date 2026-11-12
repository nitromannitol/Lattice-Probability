/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.C8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUnifQ
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiQuantile

/-!
# DDDF Corollary 8 (`Cor:RSWpsi`), small quantiles: RSW for `ψ`

Task P2-DDDFRSW2. DDDF arXiv:1904.08021, `tightness.tex` l. 664–676: "The following corollary
then follows from Propositions 5 and 7": under the assumptions of Prop 7,
(3.38) `ℓ^{(n)}_{a',b'}(ψ, ε/C) ≤ C ℓ^{(n)}_{a,b}(ψ, ε) e^{C√|log(ε/C)|}`.
Proof (DDDF's one line, written out): the comparison (2.27) (`ellQ_psi_le_of_tail`,
`ellQ_phi_le_of_tail`, from Prop 5 by a union bound, DDDF l. 482–490) moves from `ψ` to `φ` and
back, at the cost of shifting the probability level by `ε/2` resp. `ε/(4C₀)` and a factor
`e^{|ξ|M}` with `M = √(max 1 (log(C'/η))/c)`; Prop 7 (3.36) (`rsw_low_quantile`) is used in
between. Uniformity over `[A,B]²` of the Prop 5 tail: `X_{a,b} ≤ X_{B,B}` (`XAB_mono`). The
constants are collected with `max 1 (log(C'd/ε)) ≤ (2 + 2|log C'| + 2 log d)|log(ε/C)|`
(own elementary step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

theorem XAB_mono (φ ψ : ℕ → ℂ → ℝ) {a b a₂ b₂ : ℝ} (ha : a ≤ a₂) (hb : b ≤ b₂) :
    XAB φ ψ a b ≤ XAB φ ψ a₂ b₂ := by
  unfold XAB
  refine iSup_mono fun n => biSup_mono fun x hx => ?_
  simp only [rectAB, MarkedRect.toSet, Complex.mem_reProdIm, zero_add] at hx ⊢
  exact ⟨⟨hx.1.1, hx.1.2.trans ha⟩, hx.2.1, hx.2.2.trans hb⟩

/-- the constant bookkeeping for the Prop 5 tail level (own elementary step) -/
theorem max_log_le {C' d ε C : ℝ} (hC' : 0 < C') (hd : 1 ≤ d) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hC : 1 ≤ C) :
    max 1 (Real.log (C' / (ε / d))) ≤
      (2 + 2 * |Real.log C'| + 2 * Real.log d) * |Real.log (ε / C)| := by
  have hl2 := Real.log_two_gt_d9
  have hlogε : Real.log ε < -Real.log 2 := by
    rw [← Real.log_inv]; exact Real.log_lt_log hε (by norm_num; linarith)
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hL : |Real.log (ε / C)| = Real.log C - Real.log ε := by
    rw [Real.log_div hε.ne' (by linarith), abs_of_neg (by linarith)]; ring
  rw [hL]
  have hL1 : 1 / 2 ≤ Real.log C - Real.log ε := by linarith
  have e : Real.log (C' / (ε / d)) = Real.log C' + Real.log d - Real.log ε := by
    rw [Real.log_div hC'.ne' (by positivity), Real.log_div hε.ne' (by linarith)]; ring
  rw [e]
  have h1 := le_abs_self (Real.log C')
  have h2 : 0 ≤ |Real.log C'| := abs_nonneg _
  refine max_le (by nlinarith) (by nlinarith)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- quantiles of crossing lengths at levels in `(0,1)` are nonnegative -/
theorem ellQ_nonneg [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) (R : MarkedRect)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ ellQ ξ P Y R p := by
  by_contra hlt
  push Not at hlt
  have h := prob_le_ellQ (ξ := ξ) (P := P) hYc hYm R hp0 hp1
  have he : {ω | lenObs ξ Y R ω ≤ ellQ ξ P Y R p} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact hlt.trans_le ENNReal.toReal_nonneg
  rw [he, measure_empty] at h
  exact hp0.ne' (le_antisymm h bot_le)

/-- the Prop 5 tail of `X_{a,b}`, uniformly over `a, b ∈ [0, B]` -/
theorem exists_tail_XAB_unif (hW : IsWhiteNoise P W) (Q : PsiParams) (B : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a b : ℝ, a ≤ B → b ≤ B → ∀ η : ℝ, 0 < η →
      P {ω | ENNReal.ofReal (√(max 1 (Real.log (C / η)) / c)) <
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) a b} ≤
        ENNReal.ofReal η := by
  obtain ⟨C, c, hC, hc, htail⟩ := dddf_prop5_XAB hW Q B B
  refine ⟨C, c, hC, hc, fun a b ha hb η hη => ?_⟩
  set M : ℝ := √(max 1 (Real.log (C / η)) / c)
  have hM0 : 0 < M := Real.sqrt_pos.mpr (by positivity)
  have hM2 : M ^ 2 = max 1 (Real.log (C / η)) / c := Real.sq_sqrt (by positivity)
  refine (measure_mono fun ω (hω : ENNReal.ofReal M < _) =>
    (show ENNReal.ofReal M ≤ _ from hω.le.trans (XAB_mono _ _ ha hb))).trans
    ((htail M hM0).trans (ENNReal.ofReal_le_ofReal ?_))
  have hlog : Real.log (C / η) ≤ c * M ^ 2 := by
    rw [hM2, mul_div_cancel₀ _ hc.ne']; exact le_max_right _ _
  have h1 : C * exp (-(c * M ^ 2)) ≤ C * exp (-Real.log (C / η)) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hC.le
  have e : exp (-Real.log (C / η)) = (C / η)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (div_pos hC hη)]
  rw [e] at h1
  calc C * exp (-(c * M ^ 2)) ≤ C * (C / η)⁻¹ := h1
    _ = η := by field_simp

/-- `|ξ| √(max 1 (log(C'd/ε))/c) ≤ |ξ| √(k/c) √|log(ε/C)|` -/
theorem tailExp_le {C' c d ε C : ℝ} (hC' : 0 < C') (hc : 0 < c) (hd : 1 ≤ d) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (hC : 1 ≤ C) :
    |ξ| * √(max 1 (Real.log (C' / (ε / d))) / c) ≤
      |ξ| * √((2 + 2 * |Real.log C'| + 2 * Real.log d) / c) * √|Real.log (ε / C)| := by
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← Real.sqrt_mul (div_nonneg (by have := Real.log_nonneg hd; positivity) hc.le)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (max_log_le hC' hd hε hε2 hC) hc.le

/-- **DDDF Corollary 8, (3.38)** (`Cor:RSWpsi`, l. 666–671; small quantiles for `ψ`, uniform over
`(a,b), (a',b') ∈ [A,B]²`), from Prop 5 and Prop 7 (3.36). -/
theorem psi_rsw_low_quantile (hW : IsWhiteNoise P W) (Q : PsiParams) (h10 : Prop10 ξ P W)
    {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B →
      b' ∈ Icc A B → ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₀, hC₀, hC₀2, hR⟩ := rsw_low_quantile (ξ := ξ) hW h10 hA hAB
  obtain ⟨C', c, hC', hc, htail⟩ := exists_tail_XAB_unif hW Q B
  set d₁ : ℝ := 4 * C₀ with hd₁
  have hd₁1 : 1 ≤ d₁ := by linarith
  set k₁ : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log d₁
  set k₂ : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log 2
  set k₃ : ℝ := 1 + 2 * |Real.log (2 * C₀)|
  set s : ℝ := |ξ| * √(k₁ / c) + |ξ| * √(k₂ / c) + C₀ * √k₃ with hs
  have hs0 : 0 ≤ s := by positivity
  set C : ℝ := d₁ + 1 + s with hCdef
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun a b a' b' ha hb ha' hb' n ε hε hε2 => ?_⟩
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha0 : 0 ≤ a := hA.le.trans ha.1
  have hb0 : 0 ≤ b := hA.le.trans hb.1
  have ha'0 : 0 ≤ a' := hA.le.trans ha'.1
  have hb'0 : 0 ≤ b' := hA.le.trans hb'.1
  set L := |Real.log (ε / C)|
  set M₁ : ℝ := √(max 1 (Real.log (C' / (ε / d₁))) / c)
  set M₂ : ℝ := √(max 1 (Real.log (C' / (ε / 2))) / c)
  -- step 1: `ℓ_{a,b}(φ, ε/2) ≤ e^{|ξ|M₂} ℓ_{a,b}(ψ, ε)`
  have h1 := ellQ_phi_le_of_tail (ξ := ξ) hW Q ha0 hb0 (M := M₂) (Real.sqrt_nonneg _)
    (htail a b ha.2 hb.2 (ε / 2) (by positivity)) (p := ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
    (by rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_one]
        linarith) n
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at h1
  -- step 2: Prop 7 (3.36) for `φ` at level `ε/2`
  have h2 := hR a b a' b' ha hb ha' hb' n (ε / 2) (by positivity) (by linarith)
  -- step 3: `ℓ_{a',b'}(ψ, ε/d₁) ≤ e^{|ξ|M₁} ℓ_{a',b'}(φ, ε/(2C₀))`
  have e3 : ENNReal.ofReal (ε / d₁) + ENNReal.ofReal (ε / d₁) = ENNReal.ofReal (ε / 2 / C₀) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; rw [hd₁]; field_simp; ring
  have hlt3 : ε / 2 / C₀ < 1 := by rw [div_lt_one hC₀]; linarith
  have h3 := ellQ_psi_le_of_tail (ξ := ξ) hW Q ha'0 hb'0 (M := M₁) (Real.sqrt_nonneg _)
    (htail a' b' ha'.2 hb'.2 (ε / d₁) (by positivity)) (p := ENNReal.ofReal (ε / d₁))
    (ENNReal.ofReal_pos.2 (by positivity))
    (by rw [e3, ENNReal.ofReal_lt_one]; exact hlt3) n
  rw [e3] at h3
  -- step 4: monotonicity of the quantile
  have h4 : ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / d₁)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 (by positivity))
      (by rw [ENNReal.ofReal_lt_one, div_lt_one (by linarith)]; linarith)
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hε.le (by linarith) (by linarith)))
  have hℓ := ellQ_nonneg (ξ := ξ) (P := P) hψ.cont hψ.meas (rectAB a b) (p := ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε) (by rw [ENNReal.ofReal_lt_one]; linarith)
  set ℓ := ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε)
  -- the exponents
  have x1 : |ξ| * M₁ ≤ |ξ| * √(k₁ / c) * √L := tailExp_le hC' hc hd₁1 hε hε2 hC1
  have x2 : |ξ| * M₂ ≤ |ξ| * √(k₂ / c) * √L := tailExp_le hC' hc (by norm_num) hε hε2 hC1
  have x3 : C₀ * √|Real.log (ε / 2 / C₀)| ≤ C₀ * √k₃ * √L := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    rw [← Real.sqrt_mul (by positivity), div_div]
    exact Real.sqrt_le_sqrt (abs_log_div_le hε hε2 (by positivity) hC1)
  have hsum : |ξ| * M₁ + |ξ| * M₂ + C₀ * √|Real.log (ε / 2 / C₀)| ≤ C * √L := by
    have : s * √L ≤ C * √L := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have : s * √L = |ξ| * √(k₁ / c) * √L + |ξ| * √(k₂ / c) * √L + C₀ * √k₃ * √L := by ring
    linarith
  set E₁ := Real.exp (|ξ| * M₁)
  set E₂ := Real.exp (|ξ| * M₂)
  set E₃ := Real.exp (C₀ * √|Real.log (ε / 2 / C₀)|)
  have hE : E₁ * E₂ * E₃ ≤ Real.exp (C * √L) := by
    simp only [E₁, E₂, E₃, ← Real.exp_add]; exact Real.exp_le_exp.2 hsum
  calc _ ≤ _ := h4
    _ ≤ E₁ * ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / 2 / C₀)) := h3
    _ ≤ E₁ * (C₀ * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal (ε / 2)) * E₃) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * (E₂ * ℓ) * E₃) := by
        gcongr
    _ = C₀ * ℓ * (E₁ * E₂ * E₃) := by ring
    _ ≤ C * ℓ * Real.exp (C * √L) := by
        gcongr
        linarith

end DDDF
end LQGMetric
