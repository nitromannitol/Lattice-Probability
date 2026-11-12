/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L24 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24Psi
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L22

/-!
# DDDF Lemma 24 (a priori bound on the quantile ratios): `Λ_n(ψ, p) ≤ e^{C_p √n}`

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1058–1067 (`Lem:Apriori`; blueprint node DDDF.L24). DDDF's proof: Lemma 23 gives
`Var log L^{(k)}_{1,1}(φ) ≤ C k`, Proposition 5 transfers it to `ψ` (`L24Psi.lean`), and Lemma 22
with `Z_k = log L^{(k)}_{1,1}(ψ)` bounds `ℓ̄_k(ψ,p) / ℓ_k(ψ,p) ≤ e^{C_p √n}` for `k ≤ n`.

* `LambdaNPsi ξ Q W P n p = Λ_n(ψ, p) = max_{k ≤ n} ℓ̄_k(ψ,p) / ℓ_k(ψ,p)` (DDDF (2.22) =
  `DefQuant`, l. 468–470, for `ψ`; same convention as `LambdaN` for `φ`).
* `L24.ratio_le_of_variance`: `ℓ̄(p) / ℓ(p) ≤ e^{√(2 Var log L) / p}` (Lemma 22 applied to
  `log L`).
* `dddf_lemma24`: the statement, for `p ∈ (0, 1/2)`: `∃ C_p, ∀ n ≥ 1, Λ_n(ψ, p) ≤ e^{C_p √n}`.
  (`C_p` is chosen after the white noise `W`; all white noises have the same law.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `Λ_n(ψ, p) := max_{k ≤ n} ℓ̄_k(ψ, p) / ℓ_k(ψ, p)` (DDDF (2.22) = `DefQuant`, for `ψ`) -/
def LambdaNPsi (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (n : ℕ)
    (p : ℝ≥0∞) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k =>
    ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) p / ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) p

namespace L24

/-- **Lemma 22 for `log L`**: `ℓ̄(p) / ℓ(p) ≤ e^{√(2 Var log L) / p}` -/
theorem ratio_le_of_variance [IsProbabilityMeasure P] {ξ : ℝ} {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hZ : MemLp (fun ω => Real.log (lenObs ξ Y (rectAB 1 1) ω)) 2 P) {p : ℝ} (hp0 : 0 < p)
    (hp : p < 1 / 2) :
    ellBarQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p) / ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p) ≤
      exp (√(2 * Var[fun ω => Real.log (lenObs ξ Y (rectAB 1 1) ω); P]) / p) := by
  set R := rectAB 1 1
  set q := ENNReal.ofReal p
  set L := lenObs ξ Y R
  set l := ellQ ξ P Y R q
  set lb := ellBarQ ξ P Y R q
  have hLpos : ∀ ω, 0 < L ω := lenObs_pos hYc R (by simp [R, rectAB]) (by simp [R, rectAB])
    (by simp [R, rectAB, MarkedRect.crossWidth])
  have hq0 : 0 < q := ENNReal.ofReal_pos.2 hp0
  have hq1 : q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have hq2 : q ≤ 1 - q := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h1q0 : 0 < 1 - q := hq0.trans_le hq2
  have h1q1 : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne'
  have hlo : q ≤ P {ω | L ω ≤ l} := prob_le_ellQ hYc hYm R hq0 hq1
  have hhi0 := prob_ge_ellQ (ξ := ξ) (P := P) hYc hYm R h1q0 h1q1
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1.le] at hhi0
  have hhi : q ≤ P {ω | lb ≤ L ω} := hhi0
  have hll : l ≤ lb := ellQ_mono R hq0 h1q1 hq2
  -- `ℓ > 0`
  have hl0 : 0 < l := by
    by_contra hneg
    push_neg at hneg
    have : {ω | L ω ≤ l} = ∅ := eq_empty_of_forall_notMem fun ω (h : L ω ≤ l) =>
      absurd ((hLpos ω).trans_le h) (not_lt.2 hneg)
    rw [this, measure_empty] at hlo
    exact absurd hlo (not_le.2 hq0)
  have hlb0 : 0 < lb := hl0.trans_le hll
  have h22 := dddf_lemma22 hZ hp0 hp (Real.log_le_log hl0 hll)
    (hhi.trans (measure_mono fun ω (h : lb ≤ L ω) => Real.log_le_log hlb0 h))
    (hlo.trans (measure_mono fun ω (h : L ω ≤ l) => Real.log_le_log (hLpos ω) h))
  set V := Var[fun ω => Real.log (L ω); P]
  have hV : 0 ≤ V := variance_nonneg _ _
  have hd : Real.log lb - Real.log l ≤ √(2 * V) / p := by
    have hsq : (Real.log lb - Real.log l) ^ 2 ≤ (√(2 * V) / p) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      calc (Real.log lb - Real.log l) ^ 2 ≤ 2 / p ^ 2 * V := h22
        _ = 2 * V / p ^ 2 := by ring
    exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
  rw [← Real.exp_log (div_pos hlb0 hl0), Real.log_div hlb0.ne' hl0.ne']
  exact Real.exp_le_exp.2 hd

variable {W : WNSpace → Ω → ℝ}

/-- **`Var log L^{(k)}_{1,1}(ψ) ≤ C max(k, 1)`** (DDDF l. 1064–1065) -/
theorem psi_memLp_variance (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, MemLp (logLenPsi ξ Q W P k) 2 P ∧
      Var[logLenPsi ξ Q W P k; P] ≤ C * max (k : ℝ) 1 := by
  have := hW.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := integral_sq_sub_le hW Q ξ
  refine ⟨2 * ξ ^ 2 * Real.log 2 + 2 * M, by positivity, fun k => ?_⟩
  have hmψ : Measurable (logLenPsi ξ Q W P k) :=
    (measurable_lenObs (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont
      (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).meas _).log
  obtain ⟨hB, hBv⟩ := dddf_lemma23_sharp hW ξ k
  obtain ⟨hA, hAv⟩ := variance_le_two_mul hmψ hB (hM k).1
  refine ⟨hA, hAv.trans ?_⟩
  have h1 : (1 : ℝ) ≤ max (k : ℝ) 1 := le_max_right _ _
  have h2 : (k : ℝ) ≤ max (k : ℝ) 1 := le_max_left _ _
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have e1 : 2 * (ξ ^ 2 * (k * Real.log 2)) ≤ 2 * ξ ^ 2 * Real.log 2 * max (k : ℝ) 1 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * ξ ^ 2 * Real.log 2)
    nlinarith
  have e2 : 2 * M ≤ 2 * M * max (k : ℝ) 1 := by nlinarith
  nlinarith [(hM k).2]

end L24

open L24

/-- **DDDF Lemma 24** (`Lem:Apriori`, tightness.tex l. 1058–1067): for `p ∈ (0, 1/2)` there is
`C_p` with `Λ_n(ψ, p) ≤ e^{C_p √n}` for all `n ≥ 1`. -/
theorem dddf_lemma24 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    ∃ Cp : ℝ, ∀ n : ℕ, 1 ≤ n →
      LambdaNPsi ξ Q W P n (ENNReal.ofReal p) ≤ exp (Cp * √(n : ℝ)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := psi_memLp_variance hW Q ξ
  refine ⟨√(2 * C) / p, fun n hn => ?_⟩
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)
  refine (ratio_le_of_variance hv.cont hv.meas (hC k).1 hp0 hp).trans
    (Real.exp_le_exp.2 ?_)
  have hV : Var[fun ω => Real.log (lenObs ξ (psiMN Q W P 0 k) (rectAB 1 1) ω); P] ≤ C * n :=
    (hC k).2.trans (mul_le_mul_of_nonneg_left (max_le hkn hn1) hC0)
  rw [div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity)]
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) hp0.le
  nlinarith

end DDDF
end LQGMetric
