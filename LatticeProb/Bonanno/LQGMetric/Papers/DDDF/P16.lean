/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P16 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Indep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Real
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWUncond

/-!
# DDDF Proposition 16: lower tail of `L^{(n)}_{1,3}(ψ)` (task P2-DDDF16)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 822–870
(`Prop:LowerTail`... the proposition "Lower tail estimates for ψ", (4.42) =
`eq:LowerTailsPsi`): for `p` small enough but fixed there are `C, c` with
`P(L^{(n)}_{1,3}(ψ) ≤ e^{-s} ℓ_n(ψ,p)) ≤ C e^{-cs²}` for all `s > 0` (and all `n`).

Proof, following DDDF:
* (4.43) = `eq:RSWreUse` is Cor 8 (3.38) (`psi_rsw_low_quantile'`), used in quantile form
  (`p16_step13`): `P(L_{1,3} ≤ m) ≥ Cq ⇒ ℓ_{3,3}(q) ≤ C m e^{C√|log q|}`;
* (4.44) = `decaysquare` is `prob_33_le_sq` (independence for `r₀` small, `PsiSmall`);
* the recursion (4.45)–(4.47) with `p_{i+1} = (C p_i)²`: here `q_i = θ^{2^i}/C²`
  (`θ = min(1/4, C²/4, C³/4)` plays the role of DDDF's `p₀C²`), proved in quantile form
  `ℓ_{3,3}(q_i) ≤ C e^{C√|log q_i|} ℓ_{3,3}(q_{i+1})` (`p16_step`; DDDF state it as
  `P(L_{3,3} ≤ r_i) ≤ p_i`, which needs atomless laws; the quantile form does not);
* the product of the factors is `≤ e^{4M(2^{i/2} − 1)}` (`p16_iter`; DDDF l. 862);
* "using again the RSW estimates": Cor 8 from `ℓ_{3,3}(q₀)` to `ℓ_{1,1}(q₀/C)`, and the choice
  of `i` from `s` (`tail_of_levels`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

lemma ellQ_le_of_prob [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x)) (R : MarkedRect)
    {p m : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : ENNReal.ofReal p ≤ P {ω | lenObs ξ Y R ω ≤ m}) :
    ellQ ξ P Y R (ENNReal.ofReal p) ≤ m := by
  unfold ellQ
  refine (le_measure_Iic_iff_lowerQuantile_le (ENNReal.ofReal_pos.2 hp0)
    (by rw [ENNReal.ofReal_lt_one]; exact hp1)).1 ?_
  rw [Measure.map_apply (measurable_lenObs hYc hYm R) measurableSet_Iic]
  exact h

lemma ofReal_le_of_sq_le {c : ℝ} (hc : 0 ≤ c) {x : ℝ≥0∞} (hx : x ≤ 1)
    (h : ENNReal.ofReal (c ^ 2) ≤ x ^ 2) : ENNReal.ofReal c ≤ x := by
  obtain ⟨y, hy0, rfl⟩ : ∃ y : ℝ, 0 ≤ y ∧ x = ENNReal.ofReal y :=
    ⟨x.toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx)).symm⟩
  rw [← ENNReal.ofReal_pow hy0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact ENNReal.ofReal_le_ofReal ((pow_le_pow_iff_left₀ hc hy0 two_ne_zero).1 h)

/-- Cor 8 (3.38) for one field `Y`, shapes in `[1,3]²`, constant `C₀` -/
def C8At (ξ : ℝ) (P : Measure Ω) (Y : ℂ → Ω → ℝ) (C₀ : ℝ) : Prop :=
  ∀ a b a' b' : ℝ, a ∈ Icc (1 : ℝ) 3 → b ∈ Icc (1 : ℝ) 3 → a' ∈ Icc (1 : ℝ) 3 →
    b' ∈ Icc (1 : ℝ) 3 → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ellQ ξ P Y (rectAB a' b') (ENNReal.ofReal (ε / C₀)) ≤
      C₀ * ellQ ξ P Y (rectAB a b) (ENNReal.ofReal ε) * Real.exp (C₀ * √|Real.log (ε / C₀)|)

section generic

variable [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) {C₀ : ℝ} (hC₀ : 0 < C₀) (hC8 : C8At ξ P Y C₀)
include hYc hYm hC₀ hC8

/-- DDDF (4.43) in quantile form -/
lemma p16_step13 {q m : ℝ} (hq : 0 < q) (hq2 : C₀ * q < 1 / 2)
    (h : ENNReal.ofReal (C₀ * q) ≤ P {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m}) :
    ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal q) ≤ C₀ * m * Real.exp (C₀ * √|Real.log q|) := by
  have h1 := ellQ_le_of_prob hYc hYm (rectAB 1 3) (by positivity) (by linarith) h
  have h3 : (3 : ℝ) ∈ Icc (1 : ℝ) 3 := ⟨by norm_num, le_rfl⟩
  have h1' : (1 : ℝ) ∈ Icc (1 : ℝ) 3 := ⟨le_rfl, by norm_num⟩
  have h2 := hC8 1 3 3 3 h1' h3 h3 h3 (C₀ * q) (by positivity) hq2
  rw [mul_div_cancel_left₀ q hC₀.ne'] at h2
  refine h2.trans ?_
  gcongr

/-- one step of DDDF's recursion (4.45)–(4.47), quantile form -/
lemma p16_step (hsq : ∀ m : ℝ, P {ω | lenObs ξ Y (rectAB 3 3) ω ≤ m} ≤
      P {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m} ^ 2) {q : ℝ} (hq : 0 < q) (hq2 : C₀ * q < 1 / 2) :
    ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal q) ≤
      C₀ * ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal ((C₀ * q) ^ 2)) *
        Real.exp (C₀ * √|Real.log q|) := by
  have hp0 : 0 < (C₀ * q) ^ 2 := by positivity
  have hp1 : (C₀ * q) ^ 2 < 1 := by have := mul_pos hC₀ hq; nlinarith
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) hYc hYm (rectAB 3 3) (ENNReal.ofReal_pos.2 hp0)
    (by rw [ENNReal.ofReal_lt_one]; exact hp1)
  have h2 := ofReal_le_of_sq_le (by positivity) prob_le_one (h1.trans (hsq _))
  exact p16_step13 hYc hYm hC₀ hC8 hq hq2 h2

end generic

/-- DDDF's levels: `θ` and `q_i = θ^{2^i}/C²` -/
def p16Theta (C₀ : ℝ) : ℝ := min (1 / 4) (min (C₀ ^ 2 / 4) (C₀ ^ 3 / 4))

def p16Q (C₀ : ℝ) (i : ℕ) : ℝ := p16Theta C₀ ^ (2 ^ i) / C₀ ^ 2

lemma p16Theta_facts {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < p16Theta C₀ ∧ p16Theta C₀ ≤ 4⁻¹ ∧ p16Theta C₀ ≤ C₀ / 4 ∧ p16Theta C₀ ≤ C₀ ^ 2 / 4 ∧
      p16Theta C₀ ≤ C₀ ^ 3 / 4 := by
  have h1 : p16Theta C₀ ≤ 1 / 4 := min_le_left _ _
  have h2 : p16Theta C₀ ≤ C₀ ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : p16Theta C₀ ≤ C₀ ^ 3 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨lt_min (by norm_num) (lt_min (by positivity) (by positivity)), by linarith, ?_, h2, h3⟩
  rcases le_or_gt C₀ 1 with h | h
  · nlinarith
  · linarith

lemma p16Q_facts {C₀ : ℝ} (hC₀ : 0 < C₀) (i : ℕ) :
    0 < p16Q C₀ i ∧ C₀ * p16Q C₀ i ≤ 1 / 4 ∧ (C₀ * p16Q C₀ i) ^ 2 = p16Q C₀ (i + 1) ∧
      C₀ * p16Q C₀ i = C₀⁻¹ * p16Theta C₀ ^ (2 ^ i) := by
  obtain ⟨hθ0, hθ4, hθ1, -, -⟩ := p16Theta_facts hC₀
  have hpow : p16Theta C₀ ^ (2 ^ i) ≤ p16Theta C₀ :=
    pow_le_of_le_one hθ0.le (by linarith) (by positivity)
  have e : C₀ * p16Q C₀ i = C₀⁻¹ * p16Theta C₀ ^ (2 ^ i) := by
    unfold p16Q; field_simp
  refine ⟨by unfold p16Q; positivity, ?_, ?_, e⟩
  · rw [e, inv_mul_le_iff₀ hC₀]; linarith
  · rw [e]; unfold p16Q; rw [show 2 ^ (i + 1) = 2 ^ i * 2 from pow_succ 2 i, pow_mul]
    field_simp

/-- the constants: `κ = √(|log θ| + 2|log C|)`, `M = |log C| + Cκ` -/
def p16M (C₀ : ℝ) : ℝ :=
  |Real.log C₀| + C₀ * √(|Real.log (p16Theta C₀)| + 2 * |Real.log C₀|)

lemma p16M_pos {C₀ : ℝ} (hC₀ : 0 < C₀) : 0 < p16M C₀ := by
  obtain ⟨hθ0, hθ4, -⟩ := p16Theta_facts hC₀
  have hl : Real.log (p16Theta C₀) < 0 := Real.log_neg hθ0 (by linarith)
  unfold p16M
  have : 0 < √(|Real.log (p16Theta C₀)| + 2 * |Real.log C₀|) :=
    Real.sqrt_pos.2 (by have := abs_pos.2 hl.ne; positivity)
  exact add_pos_of_nonneg_of_pos (abs_nonneg _) (mul_pos hC₀ this)

lemma p16_factor_le {C₀ : ℝ} (hC₀ : 0 < C₀) (i : ℕ) :
    C₀ * Real.exp (C₀ * √|Real.log (p16Q C₀ i)|) ≤ Real.exp (p16M C₀ * √2 ^ i) := by
  obtain ⟨hθ0, -⟩ := p16Theta_facts hC₀
  have h1 := sqrt_abs_log_q_le hθ0 hC₀ i
  have hr := one_le_sqrt_two_pow i
  have hlog : Real.log C₀ ≤ |Real.log C₀| * √2 ^ i :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hr)
  rw [show C₀ * Real.exp (C₀ * √|Real.log (p16Q C₀ i)|) =
    Real.exp (Real.log C₀ + C₀ * √|Real.log (p16Q C₀ i)|) by
      rw [Real.exp_add, Real.exp_log hC₀]]
  refine Real.exp_le_exp.2 ?_
  unfold p16M
  have := mul_le_mul_of_nonneg_left h1 hC₀.le
  unfold p16Q
  nlinarith

lemma p16Q_le {C₀ : ℝ} (hC₀ : 0 < C₀) (i : ℕ) : p16Q C₀ i ≤ 1 / 4 := by
  obtain ⟨hθ0, hθ4, -, hθ2, -⟩ := p16Theta_facts hC₀
  have hpow : p16Theta C₀ ^ (2 ^ i) ≤ p16Theta C₀ :=
    pow_le_of_le_one hθ0.le (by linarith) (by positivity)
  unfold p16Q
  rw [div_le_iff₀ (by positivity)]
  linarith

lemma p16Q_zero_div_le {C₀ : ℝ} (hC₀ : 0 < C₀) : p16Q C₀ 0 / C₀ ≤ 1 / 4 := by
  obtain ⟨hθ0, -, -, -, hθ3⟩ := p16Theta_facts hC₀
  have e : p16Q C₀ 0 / C₀ = p16Theta C₀ / C₀ ^ 3 := by
    unfold p16Q; rw [pow_zero, pow_one, div_div]; ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

/-- the RSW factor from `ℓ_{3,3}(q₀)` to `ℓ_{1,1}(q₀/C)` -/
def p16K (C₀ : ℝ) : ℝ := C₀ * Real.exp (C₀ * √|Real.log (p16Q C₀ 0 / C₀)|)

section generic2

variable [IsProbabilityMeasure P] {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
  (hYm : ∀ x, Measurable (Y x)) {C₀ : ℝ} (hC₀ : 0 < C₀) (hC8 : C8At ξ P Y C₀)
  (hsq : ∀ m : ℝ, P {ω | lenObs ξ Y (rectAB 3 3) ω ≤ m} ≤
      P {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m} ^ 2)
include hYc hYm hC₀ hC8 hsq

/-- DDDF l. 862: `ℓ_{3,3}(q₀) ≤ e^{4M(2^{i/2} − 1)} ℓ_{3,3}(q_i)` -/
lemma p16_iter (i : ℕ) :
    ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ 0)) ≤
      Real.exp (4 * p16M C₀ * (√2 ^ i - 1)) *
        ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ i)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨hq0, hq1, hq2, -⟩ := p16Q_facts hC₀ i
    have hs := p16_step hYc hYm hC₀ hC8 hsq hq0 (by linarith)
    rw [hq2] at hs
    have hf := p16_factor_le hC₀ i
    have hn : 0 ≤ ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ (i + 1))) :=
      ellQ_nonneg hYc hYm _ (ENNReal.ofReal_pos.2 (p16Q_facts hC₀ (i + 1)).1)
        (by rw [ENNReal.ofReal_lt_one]; linarith [p16Q_le hC₀ (i + 1)])
    set ℓ := ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ (i + 1)))
    have h1 : ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ i)) ≤
        Real.exp (p16M C₀ * √2 ^ i) * ℓ := by
      refine hs.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_right hf hn))
    have h2 := four_mul_step (p16M_pos hC₀).le i
    calc _ ≤ _ := ih
      _ ≤ Real.exp (4 * p16M C₀ * (√2 ^ i - 1)) * (Real.exp (p16M C₀ * √2 ^ i) * ℓ) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (4 * p16M C₀ * (√2 ^ i - 1) + p16M C₀ * √2 ^ i) * ℓ := by
          rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h2) hn

/-- the tail at level `i` -/
lemma p16_level {p : ℝ} (hp : 0 < p) (hpp : p ≤ p16Q C₀ 0 / C₀) {s : ℝ} {i : ℕ}
    (hi : Real.log (p16K C₀) + 5 * p16M C₀ * √2 ^ i < s) :
    P {ω | lenObs ξ Y (rectAB 1 3) ω ≤
        Real.exp (-s) * ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p)} ≤
      ENNReal.ofReal (C₀⁻¹ * p16Theta C₀ ^ (2 ^ i)) := by
  set m := Real.exp (-s) * ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p)
  by_cases hm : m ≤ 0
  · have e : {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact hm.trans_lt (lenObs_pos hYc (rectAB 1 3) (by norm_num [rectAB])
        (by norm_num [rectAB]) (by norm_num [rectAB, MarkedRect.crossWidth]) ω)
    rw [e, measure_empty]; exact bot_le
  push Not at hm
  by_contra hcon
  push Not at hcon
  obtain ⟨hq0, hq1, -, hqe⟩ := p16Q_facts hC₀ i
  rw [← hqe] at hcon
  have hA := p16_step13 hYc hYm hC₀ hC8 hq0 (by linarith) hcon.le
  have hf := p16_factor_le hC₀ i
  have hB : ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ i)) ≤
      Real.exp (p16M C₀ * √2 ^ i) * m :=
    hA.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_right hf hm.le))
  have hI := p16_iter hYc hYm hC₀ hC8 hsq i
  have h3 : (3 : ℝ) ∈ Icc (1 : ℝ) 3 := ⟨by norm_num, le_rfl⟩
  have h1 : (1 : ℝ) ∈ Icc (1 : ℝ) 3 := ⟨le_rfl, by norm_num⟩
  have hR := hC8 3 3 1 1 h3 h3 h1 h1 (p16Q C₀ 0) (p16Q_facts hC₀ 0).1
    (by linarith [p16Q_le hC₀ 0])
  have hmono : ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p) ≤
      ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal (p16Q C₀ 0 / C₀)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 hp)
      (by rw [ENNReal.ofReal_lt_one]; linarith [p16Q_zero_div_le hC₀])
      (ENNReal.ofReal_le_ofReal hpp)
  set ℓ := ellQ ξ P Y (rectAB 3 3) (ENNReal.ofReal (p16Q C₀ 0))
  have hK : 0 < p16K C₀ := by unfold p16K; positivity
  have hm2 : m ≤ Real.exp (-s) * (p16K C₀ * ℓ) :=
    mul_le_mul_of_nonneg_left (hmono.trans (hR.trans_eq (by unfold p16K; ring)))
      (Real.exp_pos _).le
  have hℓ : 0 < ℓ := by
    by_contra h
    push Not at h
    have : Real.exp (-s) * (p16K C₀ * ℓ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (mul_nonpos_of_nonneg_of_nonpos hK.le h)
    linarith
  have key : ℓ ≤ Real.exp (4 * p16M C₀ * (√2 ^ i - 1) + p16M C₀ * √2 ^ i + -s +
      Real.log (p16K C₀)) * ℓ := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hK]
    calc ℓ ≤ _ := hI
      _ ≤ Real.exp (4 * p16M C₀ * (√2 ^ i - 1)) * (Real.exp (p16M C₀ * √2 ^ i) * m) :=
          mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
      _ ≤ Real.exp (4 * p16M C₀ * (√2 ^ i - 1)) * (Real.exp (p16M C₀ * √2 ^ i) *
          (Real.exp (-s) * (p16K C₀ * ℓ))) := by gcongr
      _ = _ := by ring
  have hlt : Real.exp (4 * p16M C₀ * (√2 ^ i - 1) + p16M C₀ * √2 ^ i + -s +
      Real.log (p16K C₀)) < 1 :=
    Real.exp_lt_one_iff.2 (by nlinarith [p16M_pos hC₀, one_le_sqrt_two_pow i])
  nlinarith

end generic2

/-- DDDF Prop 16 for one field satisfying Cor 8 (with constant `C₀`) and (4.44); the
constants depend only on `C₀`. -/
theorem p16_generic [IsProbabilityMeasure P] {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧ ∀ Y : ℂ → Ω → ℝ,
      (∀ ω, Continuous fun x => Y x ω) → (∀ x, Measurable (Y x)) → C8At ξ P Y C₀ →
      (∀ m : ℝ, P {ω | lenObs ξ Y (rectAB 3 3) ω ≤ m} ≤
        P {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m} ^ 2) →
      ∀ p s : ℝ, 0 < p → p ≤ p₀ → 0 < s →
      P {ω | lenObs ξ Y (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨hθ0, hθ4, -⟩ := p16Theta_facts hC₀
  obtain ⟨C, c, hC, hc, ht⟩ := tail_of_levels (L := Real.log (p16K C₀)) (B := C₀⁻¹)
    (p16M_pos hC₀) (inv_nonneg.2 hC₀.le) hθ0.le hθ4
  exact ⟨p16Q C₀ 0 / C₀, C, c, div_pos (p16Q_facts hC₀ 0).1 hC₀, hC, hc,
    fun Y hYc hYm hC8 hsq p s hp hpp hs => ht s _ hs prob_le_one fun i hi =>
      p16_level hYc hYm hC₀ hC8 hsq hp hpp hi⟩

/-- **DDDF Proposition 16** (`tightness.tex` l. 824–831, (4.42)): for `r₀` small enough
(`PsiSmall Q`) there is `p₀ > 0` such that for `p ∈ (0, p₀]` (DDDF: "`p` small enough, but
fixed"), with `C, c` independent of `n`, `s` and `p`:
`P(L^{(n)}_{1,3}(ψ) ≤ e^{-s} ℓ_n(ψ, p)) ≤ C e^{-cs²}` for all `s > 0`, `n ≥ 0`,
where `ℓ_n(ψ, p) = ℓ^{(n)}_{1,1}(ψ, p)` (DDDF (2.22) = `DefQuant`). -/
theorem dddf_prop16 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (Q : PsiParams) (hQ : PsiSmall Q) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧ ∀ (n : ℕ) (p s : ℝ), 0 < p → p ≤ p₀ → 0 < s →
      P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₀, hC₀, hC8⟩ := psi_rsw_low_quantile' (A := 1) (B := 3) hW hξ Q one_pos
    (by norm_num)
  obtain ⟨p₀, C, c, hp₀, hC, hc, h⟩ := p16_generic (P := P) (ξ := ξ) hC₀
  refine ⟨p₀, C, c, hp₀, hC, hc, fun n p s hp hpp hs => ?_⟩
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  exact h (psiMN Q W P 0 n) hψ.cont hψ.meas
    (fun a b a' b' ha hb ha' hb' ε hε hε2 => hC8 a b a' b' ha hb ha' hb' n ε hε hε2)
    (prob_33_le_sq hW Q hQ n) p s hp hpp hs

end DDDF
end LQGMetric
