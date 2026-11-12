/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsAB4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB3

/-!
# Left tail of `λ_n^{-1} L^{(n)}_{x,y}`, uniformly over shapes (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1644–1646 along `2^{-n}`: for `x, y ∈ [A₀, B₀]`,
`P(L^{(n)}_{x,y} ≤ e^{-s} λ_n) ≤ C e^{-c s²}`. Source of the shape change: DDDF Prop 7 (small
quantiles, l. 653–662; `rsw_low_unif`) applied with `ε = e^{-κ s²}` against the left tail of
`L^{(n)}_{1,3}` (Cor 17, `dddf_cor17`), `Λ_n` bounded (`hΛ`). The choice of `ε` and the
bookkeeping of constants are own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6AB

open WhiteNoise SupTail S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **Left tail of `λ_n^{-1} L^{(n)}_{x,y}`, uniformly in `x, y ∈ [A₀, B₀]`** (DDDF l. 1644–1646
along `2^{-n}`; Cor 17 + Prop 7 small quantiles). -/
theorem dyadic_left_AB (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    {A₀ B₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Icc A₀ B₀, ∀ y ∈ Icc A₀ B₀, ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB x y) ω ≤ Real.exp (-s) * lambdaN ξ W P n} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨p₁, hp₁, h17⟩ := dddf_cor17 (P := P) hW hξ
  obtain ⟨p₀, hp₀, hΛp⟩ := hΛ
  set p : ℝ := min p₁ (min p₀ (1 / 2))
  have hp : 0 < p := lt_min hp₁ (lt_min hp₀ (by norm_num))
  have hp1 : p ≤ p₁ := min_le_left _ _
  have hp0 : p ≤ p₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₇, c₇, hC₇, hc₇, t17⟩ := h17 p hp hp1
  obtain ⟨B₀', hB₀'⟩ := hΛp p hp hp0
  set B := max B₀' 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B :=
    fun n => (hB₀' n).trans (le_max_left _ _)
  set A := min A₀ 1
  set Bb := max B₀ 3 + 1
  have hA : 0 < A := lt_min hA₀ one_pos
  have hABb : A < Bb := by
    have : A ≤ 1 := min_le_right _ _
    have : (3 : ℝ) ≤ max B₀ 3 := le_max_right _ _
    linarith
  obtain ⟨CL, hCL0, hL⟩ := rsw_low_unif (ξ := ξ) hW (prop10 hW hξ) hA hABb
  have h3 : (3 : ℝ) ∈ Icc A Bb := ⟨(min_le_right _ _).trans (by norm_num),
    by have : (3 : ℝ) ≤ max B₀ 3 := le_max_right _ _; linarith⟩
  have h1 : (1 : ℝ) ∈ Icc A Bb := ⟨min_le_right _ _,
    by have : (3 : ℝ) ≤ max B₀ 3 := le_max_right _ _; linarith⟩
  have hmem : ∀ x ∈ Icc A₀ B₀, x ∈ Icc A Bb := fun x hx => ⟨(min_le_left _ _).trans hx.1,
    by have : B₀ ≤ max B₀ 3 := le_max_left _ _; linarith [hx.2]⟩
  set κ : ℝ := min (1 / (8 * CL ^ 2)) (c₇ / 32)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκL : κ ≤ 1 / (8 * CL ^ 2) := min_le_left _ _
  have hκ7 : κ ≤ c₇ / 32 := min_le_right _ _
  set K : ℝ := |Real.log CL|
  have hK : 0 ≤ K := abs_nonneg _
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  set S₀ : ℝ := max 1 (max (Real.log 2 / κ + 1) (max (8 * CL ^ 2 * K + 1)
    (max (4 * (K + Real.log B) + 1) (32 * |Real.log (CL * C₇)| / c₇ + 1))))
  have hS1 : 1 ≤ S₀ := le_max_left _ _
  have hSa : Real.log 2 / κ + 1 ≤ S₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hSb : 8 * CL ^ 2 * K + 1 ≤ S₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hSc : 4 * (K + Real.log B) + 1 ≤ S₀ := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hSd : 32 * |Real.log (CL * C₇)| / c₇ + 1 ≤ S₀ := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨κ, max 1 (Real.exp (κ * max S₀ 2 ^ 2)), hκ, lt_max_of_lt_left one_pos,
    fun x hx y hy n => absorb_sq (P := P) hκ fun s hs => ?_⟩
  have hs1 : 1 < s := lt_of_le_of_lt hS1 hs
  have hss : s ≤ s ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs1.le (by linarith : (0 : ℝ) ≤ s)
    rw [mul_one] at this; rw [sq]; exact this
  have hZ := isPhiVersion_phiMN hW (Nat.zero_le n)
  obtain ⟨hℓ0, hℓlam, hlamB, -⟩ := quantile_facts hW hp hph hB1 hB n
  set ℓ := ellN ξ W P n (ENNReal.ofReal p)
  have hlam0 : 0 < lambdaN ξ W P n := hℓ0.trans_le hℓlam
  set T : ℝ := Real.exp (-κ * s ^ 2)
  by_contra hcon
  rw [not_le] at hcon
  have hT : ENNReal.ofReal T ≤
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB x y) ω ≤ Real.exp (-s) * lambdaN ξ W P n} :=
    by rw [one_mul] at hcon; exact hcon.le
  have hT0 : 0 < T := Real.exp_pos _
  have hT2 : T < 1 / 2 := by
    have hk : Real.log 2 < κ * s ^ 2 := by
      have := (div_lt_iff₀ hκ).1 (by linarith : Real.log 2 / κ < s)
      have := mul_le_mul_of_nonneg_left hss hκ.le
      linarith
    have := Real.exp_lt_exp.2 (neg_lt_neg hk)
    rw [Real.exp_neg (Real.log 2), Real.exp_log (by norm_num)] at this
    simp only [T, neg_mul]; linarith
  set l : ℝ := Real.exp (-s) * lambdaN ξ W P n
  have hc := hL x y 1 3 (hmem x hx) (hmem y hy) h1 h3 n l T hT0 hT2 hT
  set l' : ℝ := CL * l * Real.exp (CL * Real.sqrt |Real.log (T / CL)|)
  have hsq : Real.sqrt |Real.log (T / CL)| ≤ s / (2 * CL) := by
    have hlog : Real.log (T / CL) = -κ * s ^ 2 - Real.log CL := by
      rw [Real.log_div hT0.ne' hCL0.ne', Real.log_exp]
    have habs : |Real.log (T / CL)| ≤ κ * s ^ 2 + K := by
      rw [hlog]
      calc |-κ * s ^ 2 - Real.log CL| ≤ |-κ * s ^ 2| + |Real.log CL| := abs_sub _ _
        _ = κ * s ^ 2 + K := by
          rw [neg_mul, abs_neg, abs_of_nonneg (by positivity)]
    have hK' : K ≤ s ^ 2 / (8 * CL ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : 8 * CL ^ 2 * K + 1 ≤ s := hSb.trans hs.le
      calc K * (8 * CL ^ 2) = 8 * CL ^ 2 * K := by ring
        _ ≤ s := by linarith
        _ ≤ s ^ 2 := hss
    have hy' : κ * s ^ 2 ≤ s ^ 2 / (8 * CL ^ 2) := by
      rw [div_eq_mul_one_div, mul_comm (s ^ 2)]
      exact mul_le_mul_of_nonneg_right hκL (sq_nonneg _)
    have : |Real.log (T / CL)| ≤ (s / (2 * CL)) ^ 2 := by
      have e : (s / (2 * CL)) ^ 2 = s ^ 2 / (8 * CL ^ 2) + s ^ 2 / (8 * CL ^ 2) := by
        field_simp; ring
      linarith
    calc Real.sqrt |Real.log (T / CL)| ≤ Real.sqrt ((s / (2 * CL)) ^ 2) := Real.sqrt_le_sqrt this
      _ = s / (2 * CL) := Real.sqrt_sq (by positivity)
  have hl' : l' ≤ Real.exp (-(s / 4)) * ℓ := by
    have e1 : Real.exp (CL * Real.sqrt |Real.log (T / CL)|) ≤ Real.exp (s / 2) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hsq hCL0.le
      have e : CL * (s / (2 * CL)) = s / 2 := by field_simp
      linarith
    have e2 : l ≤ Real.exp (-s) * (B * ℓ) := mul_le_mul_of_nonneg_left hlamB (Real.exp_pos _).le
    have e3 : l' ≤ CL * (Real.exp (-s) * (B * ℓ)) * Real.exp (s / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left e2 hCL0.le) e1 (Real.exp_pos _).le (by positivity)
    have e4 : CL * (Real.exp (-s) * (B * ℓ)) * Real.exp (s / 2) =
        Real.exp (Real.log CL + Real.log B + -s + s / 2) * ℓ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hCL0, Real.exp_log (by linarith)]
      ring
    have e5 : Real.log CL + Real.log B + -s + s / 2 ≤ -(s / 4) := by
      have : 4 * (K + Real.log B) + 1 ≤ s := hSc.trans hs.le
      have := le_abs_self (Real.log CL)
      linarith
    calc l' ≤ _ := e3
      _ = _ := e4
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 e5) hℓ0.le
  have h17' := t17 n (s / 4) (by linarith)
  have hchain : ENNReal.ofReal (T / CL) ≤ ENNReal.ofReal (C₇ * Real.exp (-c₇ * (s / 4) ^ 2)) :=
    hc.trans ((measure_mono fun ω (hω : _ ≤ l') => (show _ ≤ Real.exp (-(s / 4)) * ℓ from
      hω.trans hl')).trans h17')
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  -- contradiction: `e^{-κ s²} > CL C₇ e^{-c₇ s²/16}` for large `s`
  have hd : Real.log (CL * C₇) < c₇ * s ^ 2 / 32 := by
    have : 32 * |Real.log (CL * C₇)| / c₇ + 1 ≤ s := hSd.trans hs.le
    have h' : 32 * |Real.log (CL * C₇)| < c₇ * s := by
      have := (div_lt_iff₀ hc₇).1 (by linarith : 32 * |Real.log (CL * C₇)| / c₇ < s)
      linarith
    have := le_abs_self (Real.log (CL * C₇))
    have := mul_le_mul_of_nonneg_left hss hc₇.le
    linarith
  have hT' : Real.exp (-(c₇ / 32) * s ^ 2) ≤ T :=
    Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_right hκ7 (sq_nonneg s)
      rw [neg_mul, neg_mul]; linarith)
  have : CL * C₇ * Real.exp (-c₇ * (s / 4) ^ 2) < Real.exp (-(c₇ / 32) * s ^ 2) := by
    have e : Real.exp (-(c₇ / 32) * s ^ 2) =
        Real.exp (c₇ * s ^ 2 / 32) * Real.exp (-c₇ * (s / 4) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    refine mul_lt_mul_of_pos_right ?_ (Real.exp_pos _)
    calc CL * C₇ = Real.exp (Real.log (CL * C₇)) := (Real.exp_log (by positivity)).symm
      _ < _ := Real.exp_lt_exp.2 hd
  have h' := (div_le_iff₀ hCL0).1 hchain
  have e : C₇ * Real.exp (-c₇ * (s / 4) ^ 2) * CL = CL * C₇ * Real.exp (-c₇ * (s / 4) ^ 2) := by
    ring
  linarith

end S6AB
end DDDF
end LQGMetric
