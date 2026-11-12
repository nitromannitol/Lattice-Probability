/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Step4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Ell

/-!
# DDDF Proposition 18, Step 4: large tails (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 930–936, proof of Prop 18, Step 4): for
`s ≥ 2^{n/2}`,
`P(L^{(n)}(φ) ≥ ℓ_n(φ,p) Λ_n(φ,p) e^{s}) ≤ P(L^{(n)}(φ) ≥ ℓ_n(φ,p) e^{s}) ≤ e^{Cs} e^{-c s²/log s}`,
using `Λ_n ≥ 1`, the a priori bound `ℓ_n(φ,p) ≥ 2^{-ξ(2n + C√n)}` (`dddf_p18_ell_lower`) and the
straight-path moment bound (`dddf_p18_straight`). DDDF write the step for `L_{1,1}`; Prop 18 is
about `L_{3,1}`, for which the straight path has length `3` (same proof). We state it for the
range `n ≥ 1`, `s > 2`, `2^n ≤ s²` (i.e. `s ≥ 2^{n/2}`), with the bound in the form
`C e^{-c s²/log s}` of (4.49) (reading D-DDDF-9 of the sign). The elementary bookkeeping
(`log s ≤ 2√s`, `n log 2 ≤ 2 log s`) is our own.
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

/-- `Λ_n(φ,p) ℓ_n(φ,p) ≥ ℓ_n(φ,p)` for `p ≤ 1/2` and `ℓ_n(φ,p) > 0` -/
lemma ellN_le_LambdaN_mul [IsProbabilityMeasure P] {W : WNSpace → Ω → ℝ} {n : ℕ}
    {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) (hℓ : 0 < ellN ξ W P n (ENNReal.ofReal p)) :
    ellN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) := by
  have h1 : ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      LambdaN ξ W P n (ENNReal.ofReal p) :=
    Finset.le_sup' (fun k => ellBarN ξ W P k (ENNReal.ofReal p) / ellN ξ W P k (ENNReal.ofReal p))
      (Finset.mem_range.2 (Nat.lt_succ_self n))
  have h2 : ellN ξ W P n (ENNReal.ofReal p) ≤ ellBarN ξ W P n (ENNReal.ofReal p) := by
    unfold ellN ellBarN ellBarQ
    refine ellQ_mono _ (ENNReal.ofReal_pos.2 hp0)
      (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.2 hp0).ne') ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ellN ξ W P n (ENNReal.ofReal p) ≤ ellBarN ξ W P n (ENNReal.ofReal p) := h2
    _ = ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p) := (div_mul_cancel₀ _ hℓ.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 hℓ.le

lemma log_le_two_sqrt {s : ℝ} (hs : 0 < s) : Real.log s ≤ 2 * √s - 2 := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hs)
  rw [Real.log_sqrt hs.le] at h
  linarith

/-- **DDDF Prop 18, Step 4** (large tails `s ≥ 2^{n/2}`). -/
theorem dddf_p18_step4 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (hξ : 0 < ξ)
    {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n : ℕ) (s : ℝ), 1 ≤ n → 2 < s → (2 : ℝ) ^ n ≤ s ^ 2 →
      P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₁, hC₁, hell⟩ := dddf_p18_ell_lower hW hξ hp0 (by linarith : p < 1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set K : ℝ := ξ * (Real.log 4 + C₁)
  have hK : 0 < K := by positivity
  set D₀ : ℝ := Real.log 3 + 1
  set A : ℝ := 8 * K / Real.log 2 + 2 * D₀ + 8 * ξ ^ 2 + 1
  have hAdef : A = 8 * K / Real.log 2 + 2 * D₀ + 8 * ξ ^ 2 + 1 := rfl
  have hA : 1 ≤ A := by have : 0 ≤ 8 * K / Real.log 2 := by positivity
                        nlinarith [sq_nonneg ξ]
  set s₀ : ℝ := A ^ 2
  set c : ℝ := 1 / (16 * ξ ^ 2)
  have hc : 0 < c := by positivity
  set C : ℝ := Real.exp (c * s₀ ^ 2 / Real.log 2)
  have hC1 : 1 ≤ C := Real.one_le_exp (by positivity)
  refine ⟨C, c, by positivity, hc, fun n s hn hs2 hns => ?_⟩
  have hs0 : 0 < s := by linarith
  have hls : Real.log 2 < Real.log s := Real.log_lt_log (by norm_num) hs2
  have hls0 : 0 < Real.log s := hl2.trans hls
  by_cases hss : s < s₀
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : c * s ^ 2 / Real.log s ≤ c * s₀ ^ 2 / Real.log 2 := by
      have hsq : s ^ 2 ≤ s₀ ^ 2 := pow_le_pow_left₀ hs0.le hss.le 2
      calc c * s ^ 2 / Real.log s ≤ c * s₀ ^ 2 / Real.log s :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc.le) hls0.le
        _ ≤ c * s₀ ^ 2 / Real.log 2 :=
            div_le_div_of_nonneg_left (by positivity) hl2 hls.le
    calc (1 : ℝ) ≤ Real.exp (c * s₀ ^ 2 / Real.log 2 + -c * s ^ 2 / Real.log s) :=
          Real.one_le_exp (by rw [neg_mul, neg_div]; linarith)
      _ ≤ C * Real.exp (-c * s ^ 2 / Real.log s) := by rw [Real.exp_add]
  push Not at hss
  -- large `s`: `√s ≥ A`
  have hsA : A ≤ √s := by
    rw [show A = √(A ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt hss
  have hsq1 : 1 ≤ √s := hA.trans hsA
  have hss2 : √s * √s = s := Real.mul_self_sqrt hs0.le
  have hlog := log_le_two_sqrt hs0
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnl : n * Real.log 2 ≤ 2 * Real.log s := by
    have := Real.log_le_log (by positivity) hns
    rwa [Real.log_pow, Real.log_pow] at this
  have hsqn : √(n : ℝ) ≤ n := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hKn : ξ * (n * Real.log 4 + C₁ * √n) ≤ K * n := by
    simp only [K]; nlinarith [mul_le_mul_of_nonneg_left hsqn (by positivity : (0 : ℝ) ≤ ξ * C₁)]
  have hnK : K * n ≤ 4 * K / Real.log 2 * √s := by
    have h1 : n ≤ 2 * Real.log s / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    have h2 : 2 * Real.log s / Real.log 2 ≤ 4 * √s / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hl2.le
    calc K * n ≤ K * (4 * √s / Real.log 2) := mul_le_mul_of_nonneg_left (h1.trans h2) hK.le
      _ = 4 * K / Real.log 2 * √s := by ring
  set s'' : ℝ := s - K * n - D₀
  have hs'' : s / 2 ≤ s'' := by
    have : (8 * K / Real.log 2 + 2 * D₀) * √s ≤ s :=
      calc (8 * K / Real.log 2 + 2 * D₀) * √s ≤ √s * √s :=
            mul_le_mul_of_nonneg_right (by linarith [hAdef, sq_nonneg ξ, hsA])
              (Real.sqrt_nonneg _)
        _ = s := hss2
    have h8 : 8 * K / Real.log 2 * √s = 2 * (4 * K / Real.log 2 * √s) := by ring
    nlinarith
  set s' : ℝ := s'' / ξ
  have hs'ξ : ξ * s' = s'' := by simp only [s']; field_simp
  have hlev : ξ * (n * Real.log 2) < s' := by
    rw [lt_div_iff₀ hξ]
    have : 8 * ξ ^ 2 * √s ≤ s :=
      calc 8 * ξ ^ 2 * √s ≤ √s * √s :=
            mul_le_mul_of_nonneg_right (by
              have : 0 ≤ 8 * K / Real.log 2 + 2 * D₀ := by positivity
              linarith [hAdef, hsA]) (Real.sqrt_nonneg _)
        _ = s := hss2
    have e1 : ξ * (n * Real.log 2) * ξ = ξ ^ 2 * (n * Real.log 2) := by ring
    have e2 := mul_le_mul_of_nonneg_left hnl (sq_nonneg ξ)
    have e3 := mul_le_mul_of_nonneg_left hlog (sq_nonneg ξ)
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [e1]
    nlinarith
  have hstr := dddf_p18_straight hW hξ (a := 3) (b := 1) (by norm_num) zero_le_one hn hlev
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hℓ := hell n hn
  have hℓ0 : 0 < ellN ξ W P n (ENNReal.ofReal p) := lt_of_lt_of_le (Real.exp_pos _) hℓ
  have hΛ := ellN_le_LambdaN_mul (ξ := ξ) (P := P) (W := W) hp0 hp hℓ0
  refine le_trans (measure_mono fun ω hω => ?_) (hstr.trans (ENNReal.ofReal_le_ofReal ?_))
  · have hω' : Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
        ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := hω
    have hlt : 3 * Real.exp (ξ * s') < lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := by
      rw [hs'ξ]
      have e3 : 3 * Real.exp s'' = Real.exp (s - K * n - 1) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]; congr 1
        simp only [s'', D₀]; ring
      rw [e3]
      calc Real.exp (s - K * n - 1) < Real.exp (s - K * n) := Real.exp_lt_exp.2 (by linarith)
        _ ≤ Real.exp s * Real.exp (-(ξ * (n * Real.log 4 + C₁ * √n))) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
        _ ≤ Real.exp s * ellN ξ W P n (ENNReal.ofReal p) :=
          mul_le_mul_of_nonneg_left hℓ (Real.exp_pos _).le
        _ ≤ Real.exp s * (LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p)) :=
          mul_le_mul_of_nonneg_left hΛ (Real.exp_pos _).le
        _ ≤ _ := by rw [← mul_assoc]; exact hω'
    have hne := rectLen_ne_top (ξ := ξ) (rectAB 3 1) (by norm_num [rectAB])
      (by norm_num [rectAB]) (hφ.cont ω)
    show ENNReal.ofReal (3 * Real.exp (ξ * s')) < rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB 3 1)
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hlt)).2 hlt
  · have hs'2 : s ^ 2 / (4 * ξ ^ 2) ≤ s' ^ 2 := by
      have : (s / 2) ^ 2 ≤ s'' ^ 2 := pow_le_pow_left₀ (by positivity) hs'' 2
      simp only [s']
      rw [div_pow, le_div_iff₀ (by positivity)]
      have e : s ^ 2 / (4 * ξ ^ 2) * ξ ^ 2 = (s / 2) ^ 2 := by field_simp; ring
      rw [e]; exact this
    have hden : 0 < 2 * (n * Real.log 2) := by positivity
    have hkey : c * s ^ 2 / Real.log s ≤ s' ^ 2 / (2 * (n * Real.log 2)) := by
      calc c * s ^ 2 / Real.log s = s ^ 2 / (4 * ξ ^ 2) / (4 * Real.log s) := by
            simp only [c]; field_simp; ring
        _ ≤ s' ^ 2 / (4 * Real.log s) := div_le_div_of_nonneg_right hs'2 (by positivity)
        _ ≤ s' ^ 2 / (2 * (n * Real.log 2)) :=
            div_le_div_of_nonneg_left (sq_nonneg _) hden (by linarith)
    calc Real.exp (-(s' ^ 2 / (2 * (n * Real.log 2)))) ≤ Real.exp (-c * s ^ 2 / Real.log s) := by
          refine Real.exp_le_exp.2 ?_
          rw [neg_mul, neg_div]; linarith
      _ ≤ C * Real.exp (-c * s ^ 2 / Real.log s) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hC1

end DDDF
end LQGMetric
