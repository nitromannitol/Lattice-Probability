/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Mom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldExpTail

/-!
# DDDF l. 1218: moments of `L^{(n)}_{3,1}` are comparable to `λ_n^q` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1218: "with the tail estimates, `E(L^{(n)}_{3,1}) ≤ C E(L^{(n)}_{1,3})`. All these characteristic
lengths are uniformly comparable." We prove the form used in Prop 26, Step 1 (l. 1307–1309:
`E L^{(n)}_{3,1}`, `E (L^{(k)}_{1,1})²`) and Prop 27 (l. 1360–1368): for `q ≥ 1`,
`E (L^{(n)}_{3,1})^q ≤ C λ_n^q`, from Prop 18 (`dddf_prop18`) and `Λ_∞ < ∞` by integrating the
tail (`integral_exp_le_of_tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise S6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- **Moments of `L^{(n)}_{3,1}`** (DDDF l. 1218): `E (L^{(n)}_{3,1})^q ≤ C λ_n^q`. -/
theorem s6_moment_L31 (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    (hΛ : ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
      ∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ n : ℕ,
      Integrable (fun ω => lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ^ q) P ∧
        ∫ ω, lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω ^ q ∂P ≤ C * lambdaN ξ W P n ^ q := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨p₂, hp₂, h18⟩ := dddf_prop18 (P := P) hW hξ
  obtain ⟨p₀, hp₀, hΛp⟩ := hΛ
  set p : ℝ := min p₂ (min p₀ (1 / 2))
  have hp : 0 < p := lt_min hp₂ (lt_min hp₀ (by norm_num))
  have hp2 : p ≤ p₂ := min_le_left _ _
  have hp0 : p ≤ p₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hph : p ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C₈, c₈, hC₈, hc₈, t18⟩ := h18 p hp hp2
  obtain ⟨B₀, hB₀⟩ := hΛp p hp hp0
  set B := max B₀ 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B :=
    fun n => (hB₀ n).trans (le_max_left _ _)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set x₀ : ℝ := max 2 ((2 * (q + 1) / c₈) ^ 2)
  have hx₀ : 2 ≤ x₀ := le_max_left _ _
  set K₀ : ℝ := Real.exp (q * x₀) + q * C₈ * Real.exp (-1 * x₀) / 1
  refine ⟨B ^ q * K₀, fun n => ?_⟩
  have hpq0 : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp
  have hpq : ENNReal.ofReal p ≤ 2⁻¹ := (ENNReal.ofReal_le_ofReal hph).trans_eq ofReal_half_eq'
  set ℓ := ellN ξ W P n (ENNReal.ofReal p)
  set Λn := LambdaN ξ W P n (ENNReal.ofReal p)
  have hℓ0 : 0 < ℓ := T20B.ellN_pos hW hpq0 (lt_of_le_of_lt hpq inv_two_lt_one') n
  have hℓlam : ℓ ≤ lambdaN ξ W P n := T20B.ellN_le_lambdaN hpq0 hpq n
  have hΛn : ellBarN ξ W P n (ENNReal.ofReal p) / ℓ ≤ Λn :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p))
      (Finset.self_mem_range_succ n)
  have hΛ1 : 1 ≤ Λn := by
    refine le_trans ?_ hΛn
    rw [le_div_iff₀ hℓ0, one_mul]
    exact hℓlam.trans (T20B.lambdaN_le_ellBarN hpq0 hpq n)
  set a := Λn * ℓ
  have ha0 : 0 < a := by positivity
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set L := lenObs ξ (phiMN W P 0 n) (rectAB 3 1)
  have hLm : Measurable L := measurable_lenObs hφ.cont hφ.meas _
  have hL0 : ∀ ω, 0 ≤ L ω := fun ω => ENNReal.toReal_nonneg
  set X : Ω → ℝ := fun ω => max 0 (Real.log (L ω / a))
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => le_max_left _ _
  have hXm : Measurable X :=
    measurable_const.max (Real.measurable_log.comp (hLm.div_const a))
  -- `L ≤ a e^X`
  have hLX : ∀ ω, L ω ≤ a * Real.exp (X ω) := by
    intro ω
    rcases le_or_gt (L ω) a with h | h
    · exact h.trans (le_mul_of_one_le_right ha0.le (Real.one_le_exp (hX0 ω)))
    · have hpos : 0 < L ω / a := div_pos (ha0.trans h) ha0
      have : Real.log (L ω / a) ≤ X ω := le_max_right _ _
      have h2 := Real.exp_le_exp.2 this
      rw [Real.exp_log hpos] at h2
      rw [div_le_iff₀ ha0] at h2; linarith
  -- tail of `X`
  have htail : ∀ t, x₀ < t → (q : ℝ) * Real.exp (q * t) * P.real {ω | t ≤ X ω} ≤
      (q * C₈) * Real.exp (-1 * t) := by
    intro t ht
    have ht2 : 2 < t := lt_of_le_of_lt hx₀ ht
    have hsub : {ω | t ≤ X ω} ⊆ {ω | Real.exp t * Λn * ℓ ≤ L ω} := by
      intro ω hω
      have hω' : t ≤ X ω := hω
      have hXpos : 0 < X ω := by linarith
      have hX : X ω = Real.log (L ω / a) := by
        rcases max_choice 0 (Real.log (L ω / a)) with h | h
        · exact absurd (h ▸ hXpos : (0 : ℝ) < 0) (lt_irrefl 0)
        · exact h
      have hLa : 0 < L ω / a := by
        by_contra hc
        rw [not_lt] at hc
        rw [hX] at hXpos
        rcases eq_or_lt_of_le hc with h0 | h0
        · rw [h0, Real.log_zero] at hXpos; exact lt_irrefl 0 hXpos
        · have : L ω / a ≥ 0 := div_nonneg (hL0 ω) ha0.le
          linarith
      have h1 : Real.exp t ≤ L ω / a := by
        rw [← Real.exp_log hLa]; exact Real.exp_le_exp.2 (hX ▸ hω')
      show Real.exp t * Λn * ℓ ≤ L ω
      rw [le_div_iff₀ ha0] at h1; simp only [a] at h1; linarith
    have hP1 : P.real {ω | t ≤ X ω} ≤ C₈ * Real.exp (-c₈ * t ^ 2 / Real.log t) := by
      have := (measure_mono (μ := P) hsub).trans (t18 n t ht2)
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hsq : 2 * (q + 1) / c₈ ≤ √t := by
      have h1 : (2 * (q + 1) / c₈) ^ 2 < t := lt_of_le_of_lt (le_max_right _ _) ht
      exact (Real.lt_sqrt (by positivity)).2 h1 |>.le
    -- `q t − c₈ t² / log t ≤ −t`
    have hkey : (q : ℝ) * t + -c₈ * t ^ 2 / Real.log t ≤ -1 * t := by
      have hl := log_le_two_sqrt (show 0 < t by linarith)
      have hst : 0 < √t := Real.sqrt_pos.2 (by linarith)
      have hss : √t * √t = t := Real.mul_self_sqrt (by linarith)
      have h3 : (q + 1) * Real.log t ≤ c₈ * t := by
        have h4 : 2 * (q + 1) ≤ √t * c₈ := (div_le_iff₀ hc₈).1 hsq
        nlinarith
      rw [neg_mul, neg_div, ← sub_eq_add_neg, sub_le_iff_le_add, div_eq_mul_inv]
      have : (q + 1) * t ≤ c₈ * t ^ 2 * (Real.log t)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hlt]; nlinarith
      linarith
    calc (q : ℝ) * Real.exp (q * t) * P.real {ω | t ≤ X ω}
        ≤ (q : ℝ) * Real.exp (q * t) * (C₈ * Real.exp (-c₈ * t ^ 2 / Real.log t)) := by gcongr
      _ = (q * C₈) * Real.exp (q * t + -c₈ * t ^ 2 / Real.log t) := by rw [Real.exp_add]; ring
      _ ≤ (q * C₈) * Real.exp (-1 * t) := by gcongr
  obtain ⟨hint, hbd⟩ := integral_exp_le_of_tail hX0 hXm.aemeasurable hq0 (by linarith)
    one_pos (by positivity) htail
  have hdom : ∀ ω, L ω ^ q ≤ a ^ q * Real.exp (q * X ω) := by
    intro ω
    calc L ω ^ q ≤ (a * Real.exp (X ω)) ^ q := pow_le_pow_left₀ (hL0 ω) (hLX ω) q
      _ = a ^ q * Real.exp (q * X ω) := by rw [mul_pow, ← Real.exp_nat_mul]
  have hintL : Integrable (fun ω => L ω ^ q) P := by
    refine (hint.const_mul (a ^ q)).mono' ((hLm.pow_const q).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hL0 ω) q)]; exact hdom ω
  refine ⟨hintL, ?_⟩
  have haB : a ≤ B * lambdaN ξ W P n := mul_le_mul (hB n) hℓlam hℓ0.le (by linarith)
  calc ∫ ω, L ω ^ q ∂P ≤ ∫ ω, a ^ q * Real.exp (q * X ω) ∂P :=
        integral_mono hintL (hint.const_mul _) hdom
    _ = a ^ q * ∫ ω, Real.exp (q * X ω) ∂P := integral_const_mul _ _
    _ ≤ (B * lambdaN ξ W P n) ^ q * K₀ := by
        apply mul_le_mul (pow_le_pow_left₀ ha0.le haB q) hbd (integral_nonneg fun ω => (Real.exp_pos _).le)
        exact pow_nonneg (mul_nonneg (by linarith) (hℓ0.le.trans hℓlam)) q
    _ = B ^ q * K₀ * lambdaN ξ W P n ^ q := by ring

end DDDF
end LQGMetric
