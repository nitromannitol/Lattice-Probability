/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsAB3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUnif
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Main

/-!
# Right tail of `λ_n^{-1} L^{(n)}_{x,y}`, uniformly over shapes (task P2-DDDF6e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1639–1643 ("the tail estimates obtained along the
sequence `2^{-n}`"): for `x, y ∈ [A₀, B₀]`,
`P(e^s λ_n ≤ L^{(n)}_{x,y}) ≤ C e^{-c s²/log s}` for `s > 2`. Source of the shape change: DDDF
Prop 7 (`RSW`, l. 653–662, high quantiles; `rsw_high_unif`) applied to the right tail of
`L^{(n)}_{3,1}` (Prop 18, `dddf_prop18`) with `Λ_n` bounded (`hΛ`, Theorem 20).
The choice of `ε` in Prop 7 and the bookkeeping of constants are own elementary arguments.
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

/-- absorbing small `s` into the constant (`s²/log s` form) -/
lemma absorb_log [IsProbabilityMeasure P] {E : ℝ → Set Ω} {c C S₀ : ℝ} (hc : 0 < c)
    (h : ∀ s, S₀ < s → P (E s) ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) :
    ∀ s, 2 < s → P (E s) ≤ ENNReal.ofReal (max C (Real.exp (c * max S₀ 2 ^ 2 / Real.log 2)) *
      Real.exp (-c * s ^ 2 / Real.log s)) := by
  set S := max S₀ 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro s hs
  by_cases hsS : S₀ < s
  · exact (h s hsS).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_pos _).le))
  · rw [not_lt] at hsS
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsS' : s ≤ S := hsS.trans (le_max_left _ _)
    have hls : 0 < Real.log s := Real.log_pos (by linarith)
    have h1 : c * s ^ 2 / Real.log s ≤ c * S ^ 2 / Real.log 2 := by
      rw [mul_div_assoc, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      exact div_le_div₀ (by positivity) (by nlinarith) hl2 (Real.log_le_log (by norm_num) hs.le)
    calc (1 : ℝ) ≤ Real.exp (c * S ^ 2 / Real.log 2) * Real.exp (-c * s ^ 2 / Real.log s) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by rw [neg_mul, neg_div]; linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- absorbing small `s` into the constant (`s²` form) -/
lemma absorb_sq [IsProbabilityMeasure P] {E : ℝ → Set Ω} {c C S₀ : ℝ} (hc : 0 < c)
    (h : ∀ s, S₀ < s → P (E s) ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) :
    ∀ s, 2 < s → P (E s) ≤ ENNReal.ofReal (max C (Real.exp (c * max S₀ 2 ^ 2)) *
      Real.exp (-c * s ^ 2)) := by
  set S := max S₀ 2
  intro s hs
  by_cases hsS : S₀ < s
  · exact (h s hsS).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_pos _).le))
  · rw [not_lt] at hsS
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsS' : s ≤ S := hsS.trans (le_max_left _ _)
    have h1 : c * s ^ 2 ≤ c * S ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hc.le
    calc (1 : ℝ) ≤ Real.exp (c * S ^ 2) * Real.exp (-c * s ^ 2) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by rw [neg_mul]; linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- the quantile facts used with `Λ` bounded: `ℓ_n > 0`, `ℓ_n ≤ λ_n ≤ B ℓ_n`, `Λ_n ℓ_n ≤ B λ_n` -/
lemma quantile_facts (hW : IsWhiteNoise P W) {p B : ℝ} (hp : 0 < p) (hph : p ≤ 1 / 2)
    (hB1 : 1 ≤ B) (hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) (n : ℕ) :
    0 < ellN ξ W P n (ENNReal.ofReal p) ∧
      ellN ξ W P n (ENNReal.ofReal p) ≤ lambdaN ξ W P n ∧
      lambdaN ξ W P n ≤ B * ellN ξ W P n (ENNReal.ofReal p) ∧
      LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
        B * lambdaN ξ W P n := by
  have := hW.isProbabilityMeasure
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := (ENNReal.ofReal_le_ofReal hph).trans_eq ofReal_half_eq'
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) :=
    T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hℓlam := T20B.ellN_le_lambdaN (ξ := ξ) (W := W) (P := P) hpq0 hpq n
  have hlam_ℓb := T20B.lambdaN_le_ellBarN (ξ := ξ) (W := W) (P := P) hpq0 hpq n
  have hΛn : ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p))
      (Finset.self_mem_range_succ n)
  refine ⟨hℓ0, hℓlam, ?_, ?_⟩
  · have := (div_le_iff₀ hℓ0).1 (hΛn.trans (hB n)); linarith
  · exact mul_le_mul (hB n) hℓlam hℓ0.le (by linarith)

/-- `1 - ofReal (1 - z) ≤ ofReal z` -/
lemma one_sub_ofReal_le (z : ℝ) : 1 - ENNReal.ofReal (1 - z) ≤ ENNReal.ofReal z := by
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal (z + (1 - z)) := by rw [add_sub_cancel, ENNReal.ofReal_one]
    _ ≤ _ := ENNReal.ofReal_add_le

/-- **Right tail of `λ_n^{-1} L^{(n)}_{x,y}`, uniformly in `x, y ∈ [A₀, B₀]`** (DDDF l. 1641–1643
along `2^{-n}`; Prop 18 + Prop 7 high quantiles). -/
theorem dyadic_right_AB (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B)
    {A₀ B₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Icc A₀ B₀, ∀ y ∈ Icc A₀ B₀, ∀ (n : ℕ) (s : ℝ), 2 < s →
      P {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB x y) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨p₂, hp₂, h18⟩ := dddf_prop18 (P := P) hW hξ
  obtain ⟨p₀, hp₀, hΛp⟩ := hΛ
  set p : ℝ := min p₂ (min p₀ (1 / 2))
  have hp : 0 < p := lt_min hp₂ (lt_min hp₀ (by norm_num))
  have hp2 : p ≤ p₂ := min_le_left _ _
  have hp0 : p ≤ p₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₈, c₈, hC₈, hc₈, t18⟩ := h18 p hp hp2
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
  obtain ⟨CR, hCR0, hR, hCR1⟩ := rsw_high_unif (ξ := ξ) hW hξ.le (prop10 hW hξ) hA hABb
  have h3 : (3 : ℝ) ∈ Icc A Bb := ⟨(min_le_right _ _).trans (by norm_num),
    by have : (3 : ℝ) ≤ max B₀ 3 := le_max_right _ _; linarith⟩
  have h1 : (1 : ℝ) ∈ Icc A Bb := ⟨min_le_right _ _,
    by have : (3 : ℝ) ≤ max B₀ 3 := le_max_right _ _; linarith⟩
  have hmem : ∀ x ∈ Icc A₀ B₀, x ∈ Icc A Bb := fun x hx => ⟨(min_le_left _ _).trans hx.1,
    by have : B₀ ≤ max B₀ 3 := le_max_left _ _; linarith [hx.2]⟩
  set κ : ℝ := min c₈ (1 / (32 * CR ^ 2))
  have hκ : 0 < κ := lt_min hc₈ (by positivity)
  have hκ8 : κ ≤ c₈ := min_le_left _ _
  have hκR : κ ≤ 1 / (32 * CR ^ 2) := min_le_right _ _
  set K : ℝ := |Real.log C₈| + |Real.log CR|
  have hK : 0 ≤ K := by positivity
  have hlCR : 0 ≤ Real.log CR := Real.log_nonneg hCR1
  have hlB : 0 ≤ Real.log B := Real.log_nonneg hB1
  set σ₀ : ℝ := max (Real.exp 1) (max (|Real.log (2 * C₈)| / κ + 1)
    (max (32 * CR ^ 2 * K + 1) (2 * (Real.log CR + Real.log B) + 1)))
  have hσe : Real.exp 1 ≤ σ₀ := le_max_left _ _
  have hσ1 : |Real.log (2 * C₈)| / κ + 1 ≤ σ₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hσ2 : 32 * CR ^ 2 * K + 1 ≤ σ₀ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hσ3 : 2 * (Real.log CR + Real.log B) + 1 ≤ σ₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨κ / (4 * CR), max (3 * C₈ ^ (1 / CR))
    (Real.exp (κ / (4 * CR) * max (2 * σ₀) 2 ^ 2 / Real.log 2)), by positivity,
    lt_max_of_lt_left (by positivity), fun x hx y hy n => absorb_log (P := P) (by positivity)
    fun s hs => ?_⟩
  have hZ := isPhiVersion_phiMN hW (Nat.zero_le n)
  obtain ⟨hℓ0, hℓlam, -, hΛℓ⟩ := quantile_facts hW hp hph hB1 hB n
  have hlam0 : 0 < lambdaN ξ W P n := hℓ0.trans_le hℓlam
  set σ : ℝ := s / 2
  have hσ : σ₀ < σ := by simp only [σ]; linarith
  have hσe' : Real.exp 1 < σ := lt_of_le_of_lt hσe hσ
  have hσ0 : 0 < σ := (Real.exp_pos 1).trans hσe'
  have hlσ : 1 ≤ Real.log σ := by
    rw [← Real.exp_le_exp, Real.exp_log hσ0]; exact hσe'.le
  have hlσσ : Real.log σ ≤ σ := (Real.log_le_sub_one_of_pos hσ0).trans (by linarith)
  have hσtwo : 2 < σ := lt_trans (by linarith [Real.exp_one_gt_d9]) hσe'
  set yy : ℝ := κ * σ ^ 2 / Real.log σ
  have hyσ : κ * σ ≤ yy := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hlσσ (by positivity : 0 ≤ κ * σ)
    nlinarith
  have hyle : yy ≤ κ * σ ^ 2 := div_le_self (by positivity) hlσ
  set ε : ℝ := C₈ * Real.exp (-yy)
  have hε0 : 0 < ε := by positivity
  have hε2 : ε < 1 / 2 := by
    have hy : Real.log (2 * C₈) < yy := by
      have : |Real.log (2 * C₈)| < κ * σ := by
        have := (div_lt_iff₀ hκ).1 (by linarith : |Real.log (2 * C₈)| / κ < σ)
        linarith
      linarith [le_abs_self (Real.log (2 * C₈))]
    have := Real.exp_lt_exp.2 (neg_lt_neg hy)
    rw [Real.exp_neg (Real.log (2 * C₈)), Real.exp_log (by positivity)] at this
    calc ε = C₈ * Real.exp (-yy) := rfl
      _ < C₈ * (2 * C₈)⁻¹ := mul_lt_mul_of_pos_left this hC₈
      _ = 1 / 2 := by field_simp
  set l : ℝ := Real.exp σ * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)
  have hmeas : ∀ (u v : ℝ), Measurable (lenObs ξ (phiMN W P 0 n) (rectAB u v)) :=
    fun u v => measurable_lenObs hZ.cont hZ.meas _
  -- the hypothesis of Prop 7
  have hhyp : ENNReal.ofReal (1 - ε) ≤
      P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ≤ l} := by
    have t := t18 n σ hσtwo
    have t' : P {ω | l ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤ ENNReal.ofReal ε := by
      refine t.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 ?_) hC₈.le))
      simp only [yy]
      rw [neg_mul, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hκ8 (sq_nonneg _))
        (by linarith)
    have hcov : (univ : Set Ω) ⊆ {ω | lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ≤ l} ∪
        {ω | l ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} := fun ω _ => by
      simp only [mem_union, mem_ofPred_eq]; exact le_total _ _
    have h1 : (1 : ℝ≥0∞) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ≤ l} +
        ENNReal.ofReal ε := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono hcov).trans ((measure_union_le _ _).trans (add_le_add le_rfl t'))
    rw [ENNReal.ofReal_sub _ hε0.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.2 h1
  have hcon := hR 3 1 x y h3 h1 (hmem x hx) (hmem y hy) n l ε hε0 hε2 hhyp
  set l' : ℝ := CR * l * Real.exp (CR * Real.sqrt |Real.log (ε / CR)|)
  -- `l' < e^s λ_n`
  have hsq : Real.sqrt |Real.log (ε / CR)| ≤ σ / (4 * CR) := by
    have hlog : Real.log (ε / CR) = Real.log C₈ + -yy - Real.log CR := by
      rw [Real.log_div hε0.ne' hCR0.ne', Real.log_mul hC₈.ne' (Real.exp_pos _).ne',
        Real.log_exp]
    have habs : |Real.log (ε / CR)| ≤ K + yy := by
      rw [hlog]
      have hy0 : 0 ≤ yy := by positivity
      calc |Real.log C₈ + -yy - Real.log CR| ≤ |Real.log C₈ + -yy| + |Real.log CR| := abs_sub _ _
        _ ≤ |Real.log C₈| + |-yy| + |Real.log CR| := by gcongr; exact abs_add_le _ _
        _ = K + yy := by rw [abs_neg, abs_of_nonneg hy0]; ring
    have hK' : K ≤ σ ^ 2 / (32 * CR ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : 32 * CR ^ 2 * K + 1 ≤ σ := hσ2.trans hσ.le
      nlinarith
    have hy' : yy ≤ σ ^ 2 / (32 * CR ^ 2) := by
      refine hyle.trans ?_
      rw [div_eq_mul_one_div, mul_comm (σ ^ 2)]
      exact mul_le_mul_of_nonneg_right hκR (sq_nonneg _)
    have : |Real.log (ε / CR)| ≤ (σ / (4 * CR)) ^ 2 := by
      have e : (σ / (4 * CR)) ^ 2 = σ ^ 2 / (32 * CR ^ 2) + σ ^ 2 / (32 * CR ^ 2) := by
        field_simp; ring
      linarith
    calc Real.sqrt |Real.log (ε / CR)| ≤ Real.sqrt ((σ / (4 * CR)) ^ 2) := Real.sqrt_le_sqrt this
      _ = σ / (4 * CR) := Real.sqrt_sq (by positivity)
  have hl'lt : l' < Real.exp s * lambdaN ξ W P n := by
    have e1 : Real.exp (CR * Real.sqrt |Real.log (ε / CR)|) ≤ Real.exp (σ / 4) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hsq hCR0.le
      have e : CR * (σ / (4 * CR)) = σ / 4 := by field_simp
      linarith
    have e2 : l ≤ Real.exp σ * (B * lambdaN ξ W P n) := by
      simp only [l]; rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hΛℓ (Real.exp_pos _).le
    have e3 : l' ≤ CR * (Real.exp σ * (B * lambdaN ξ W P n)) * Real.exp (σ / 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left e2 hCR0.le) e1 (Real.exp_pos _).le
        (by positivity)
    have e4 : CR * (Real.exp σ * (B * lambdaN ξ W P n)) * Real.exp (σ / 4) =
        Real.exp (Real.log CR + Real.log B + 5 * σ / 4) * lambdaN ξ W P n := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hCR0, Real.exp_log (by linarith),
        show 5 * σ / 4 = σ + σ / 4 by ring, Real.exp_add]; ring
    have e5 : Real.log CR + Real.log B + 5 * σ / 4 < s := by
      have : 2 * (Real.log CR + Real.log B) + 1 < σ := lt_of_le_of_lt hσ3 hσ
      simp only [σ] at this ⊢; linarith
    calc l' ≤ _ := e3
      _ = _ := e4
      _ < Real.exp s * lambdaN ξ W P n :=
          mul_lt_mul_of_pos_right (Real.exp_lt_exp.2 e5) hlam0
  -- conclusion
  have hG : MeasurableSet {ω | lenObs ξ (phiMN W P 0 n) (rectAB x y) ω ≤ l'} :=
    measurableSet_le (hmeas x y) measurable_const
  have hsub : {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB x y) ω} ⊆
      {ω | lenObs ξ (phiMN W P 0 n) (rectAB x y) ω ≤ l'}ᶜ := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_le]
    exact lt_of_lt_of_le hl'lt hω
  refine (measure_mono (μ := P) hsub).trans ?_
  rw [prob_compl_eq_one_sub hG]
  refine (tsub_le_tsub_left hcon _).trans ((one_sub_ofReal_le _).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  -- `3 ε^{1/CR} ≤ 3 C₈^{1/CR} e^{-(κ/(4CR)) s²/log s}`
  have hpow : ε ^ (1 / CR) = C₈ ^ (1 / CR) * Real.exp (-yy / CR) := by
    rw [Real.mul_rpow hC₈.le (Real.exp_pos _).le, ← Real.exp_mul]; ring_nf
  rw [hpow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hls : Real.log σ ≤ Real.log s := Real.log_le_log hσ0 (by simp only [σ]; linarith)
  have hls0 : 0 < Real.log σ := by linarith
  have : κ / (4 * CR) * s ^ 2 / Real.log s ≤ yy / CR := by
    simp only [yy]
    have e : κ / (4 * CR) * s ^ 2 = κ * σ ^ 2 / CR := by simp only [σ]; field_simp; ring
    rw [e, div_div, div_div, mul_comm (Real.log σ) CR]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hls hCR0.le)
  rw [neg_mul, neg_div, neg_div]; linarith

end S6AB
end DDDF
end LQGMetric
