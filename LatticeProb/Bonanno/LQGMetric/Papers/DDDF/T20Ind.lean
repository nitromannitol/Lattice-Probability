/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20Ind at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DDDF Theorem 20, Step 5: the induction on the quantile ratios

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1176–1213 (proof of `thm:AssTthm`, Step 5; blueprint node DDDF.T20). This file is the purely
deterministic part of Step 5: from

* (5.71) = `Fin:ind`: `r_n ≤ e^{C_p √(V_n)}` (Step 1, `eq:Step1`, Lemma 22),
* (5.70) = `eq:RecursiveIneq`: `V_n ≤ C₁ K + e^{-C₂ K} Λ_{n-K}²` for `K` large and `n ≥ K`
  (Steps 2–4),
* (5.72) = `Fin:ap`: `Λ_K ≤ e^{C̃_p √K}` (Lemma 24),

where `r_n = ℓ̄_n(ψ,p/2)/ℓ_n(ψ,p/2)`, `Λ_n = max_{k ≤ n} r_k`, `V_n = Var log L^{(n)}_{1,1}(ψ)`,
DDDF fix `K` with (5.73) = `Fin:fixK`: `e^{-C₂K}(e^{C̃_p√K} + e^{C_p√(2C₁K)})² ≤ C₁K` and show by
induction `Λ_n ≤ Λ_Rec := Λ_K ∨ e^{C_p √(2C₁K)}` for all `n`.

* `t20_exists_K`: existence of such a `K` beyond any `K₀` (DDDF: "we take `K` large enough").
  Own elementary proof (`2√K ≤ εK + 1/ε`).
* `t20_step5`: `sup_n Λ_n < ∞`, following DDDF l. 1191–1210 (monotonicity of `Λ` replaces
  DDDF's `Λ_{n-K} ≤ Λ_{n-1}`, which is the same remark).
* `t20_step5_var`: then also `sup_n V_n < ∞` (DDDF l. 1185, "and then that
  `sup_n Var log L^{(n)}_{1,1}(ψ) < ∞`"), given an a priori bound on `V_n` for `n < K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real

namespace LQGMetric
namespace DDDF
namespace T20

/-- `2 c √K - C₂ K ≤ -D` for all large `K` (own elementary argument). -/
lemma eventually_sqrt_sub_le {c C₂ : ℝ} (hc : 0 ≤ c) (hC₂ : 0 < C₂) (D : ℝ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 2 * c * √(K : ℝ) - C₂ * K ≤ -D := by
  set ε := C₂ / (2 * c + 1) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨⌈2 * (|D| + c / ε) / C₂⌉₊, fun K hK => ?_⟩
  have hK' : 2 * (|D| + c / ε) / C₂ ≤ K := (Nat.ceil_le.1 hK)
  have hs := Real.sq_sqrt (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
  have hs0 := Real.sqrt_nonneg (K : ℝ)
  -- `2 √K ≤ ε K + 1/ε`
  have hamgm : 2 * √(K : ℝ) ≤ ε * K + 1 / ε := by
    have h1 : 0 ≤ (ε * √(K : ℝ) - 1) ^ 2 := sq_nonneg _
    have h2 : ε * (2 * √(K : ℝ)) ≤ ε * (ε * K + 1 / ε) := by
      have he : (ε * √(K : ℝ) - 1) ^ 2 = ε * (ε * K) + 1 - ε * (2 * √(K : ℝ)) := by
        linear_combination ε ^ 2 * hs
      rw [mul_add, mul_one_div_cancel hε0.ne']; linarith
    exact le_of_mul_le_mul_left h2 hε0
  have hcε : c * ε ≤ C₂ / 2 := by
    rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : 2 * c * √(K : ℝ) ≤ C₂ / 2 * K + c / ε := by
    have := mul_le_mul_of_nonneg_left hamgm hc
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc 2 * c * √(K : ℝ) = c * (2 * √(K : ℝ)) := by ring
      _ ≤ c * (ε * K + 1 / ε) := this
      _ = (c * ε) * K + c / ε := by ring
      _ ≤ C₂ / 2 * K + c / ε := by nlinarith
  have h4 : 2 * (|D| + c / ε) ≤ C₂ * K := by
    rw [div_le_iff₀ hC₂] at hK'; linarith
  have := le_abs_self D
  nlinarith

/-- **Choice of `K`** ((5.73) = `Fin:fixK`, DDDF l. 1192–1196): for `C₁, C₂ > 0` there are
arbitrarily large `K ≥ 1` with `e^{-C₂K}(e^{a√K} + e^{b√(2C₁K)})² ≤ C₁ K`. -/
theorem t20_exists_K {C₁ C₂ a b : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (K₀ : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ 1 ≤ K ∧
      exp (-(C₂ * K)) * (exp (a * √(K : ℝ)) + exp (b * √(2 * C₁ * K))) ^ 2 ≤ C₁ * K := by
  set c := |a| + |b| * √(2 * C₁) with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨K₁, hK₁⟩ := eventually_sqrt_sub_le hc0 hC₂ (Real.log 4)
  set K := max (max K₀ K₁) (max 1 ⌈1 / C₁⌉₊) with hKdef
  refine ⟨K, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  have hKK₁ : K₁ ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK1 : (1 / C₁ : ℝ) ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _))
  have hCK : 1 ≤ C₁ * K := by rwa [div_le_iff₀ hC₁, mul_comm] at hK1
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- both exponents are `≤ c √K`
  have hsq : √(2 * C₁ * K) = √(2 * C₁) * √(K : ℝ) := Real.sqrt_mul (by positivity) _
  have hsK := Real.sqrt_nonneg (K : ℝ)
  have ha : a * √(K : ℝ) ≤ c * √(K : ℝ) := by
    have : a ≤ c := (le_abs_self a).trans (le_add_of_nonneg_right (by positivity))
    exact mul_le_mul_of_nonneg_right this hsK
  have hb : b * √(2 * C₁ * K) ≤ c * √(K : ℝ) := by
    rw [hsq, ← mul_assoc]
    have : b * √(2 * C₁) ≤ c :=
      ((le_abs_self b).trans_eq rfl |> fun h => mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)).trans
        (le_add_of_nonneg_left (abs_nonneg a))
    exact mul_le_mul_of_nonneg_right this hsK
  have hsum : exp (a * √(K : ℝ)) + exp (b * √(2 * C₁ * K)) ≤ 2 * exp (c * √(K : ℝ)) := by
    have := exp_le_exp.2 ha; have := exp_le_exp.2 hb; linarith
  have hsq2 : (exp (a * √(K : ℝ)) + exp (b * √(2 * C₁ * K))) ^ 2 ≤
      4 * exp (2 * c * √(K : ℝ)) := by
    have h0 : 0 ≤ exp (a * √(K : ℝ)) + exp (b * √(2 * C₁ * K)) := by positivity
    calc _ ≤ (2 * exp (c * √(K : ℝ))) ^ 2 := pow_le_pow_left₀ h0 hsum 2
      _ = 4 * exp (2 * c * √(K : ℝ)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
  have hkey := hK₁ K hKK₁
  calc exp (-(C₂ * K)) * (exp (a * √(K : ℝ)) + exp (b * √(2 * C₁ * K))) ^ 2
      ≤ exp (-(C₂ * K)) * (4 * exp (2 * c * √(K : ℝ))) :=
        mul_le_mul_of_nonneg_left hsq2 (exp_pos _).le
    _ = 4 * exp (2 * c * √(K : ℝ) - C₂ * K) := by rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ 4 * exp (-Real.log 4) := by gcongr
    _ = 1 := by rw [exp_neg, exp_log (by norm_num)]; norm_num
    _ ≤ C₁ * K := hCK

/-- **DDDF Theorem 20, Step 5** (l. 1186–1210): the recursive inequality (5.70), the step bound
(5.71) and the a priori bound (5.72) give `sup_n Λ_n < ∞`. `Λ` is nonnegative and monotone with
`Λ_{n+1} ≤ Λ_n ∨ r_{n+1}` (true for `Λ_n = max_{k≤n} r_k`, `r_k ≥ 0`). The second conclusion is
DDDF's `sup_{n ≥ K} Var log L^{(n)}_{1,1}(ψ) ≤ 2 C₁ K` (l. 1185, via (5.70)). -/
theorem t20_step5 {r V Λ : ℕ → ℝ} {C₁ C₂ Cp Ct : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hCp : 0 ≤ Cp) (hnonneg : ∀ n, 0 ≤ Λ n) (hmono : Monotone Λ)
    (hΛ : ∀ n, Λ (n + 1) ≤ max (Λ n) (r (n + 1)))
    (hr : ∀ n, r n ≤ exp (Cp * √(V n)))
    (hrec : ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      V n ≤ C₁ * K + exp (-(C₂ * K)) * Λ (n - K) ^ 2)
    (happ : ∀ n : ℕ, 1 ≤ n → Λ n ≤ exp (Ct * √(n : ℝ))) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ B : ℝ, 0 < B ∧ (∀ n, Λ n ≤ B) ∧ ∀ n, K ≤ n → V n ≤ 2 * C₁ * K := by
  obtain ⟨K₀, hK₀⟩ := hrec
  obtain ⟨K, hKK₀, hK1, hfix⟩ := t20_exists_K (a := Ct) (b := Cp) hC₁ hC₂ K₀
  set e := exp (Cp * √(2 * C₁ * K)) with he
  set B := max (Λ K) e with hB
  have he0 : 0 < e := exp_pos _
  have hB0 : 0 < B := he0.trans_le (le_max_right _ _)
  -- `e^{-C₂K} B² ≤ C₁ K` (DDDF l. 1205–1207)
  have hBsq : exp (-(C₂ * K)) * B ^ 2 ≤ C₁ * K := by
    have hΛK := happ K hK1
    have hBle : B ≤ exp (Ct * √(K : ℝ)) + e :=
      max_le (hΛK.trans (le_add_of_nonneg_right he0.le))
        (le_add_of_nonneg_left (exp_pos _).le)
    refine le_trans ?_ hfix
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0.le hBle 2) (exp_pos _).le
  -- (5.70) with `Λ_{n-K} ≤ B` gives `V_n ≤ 2 C₁ K`
  have hVle : ∀ n, K ≤ n → Λ (n - K) ≤ B → V n ≤ 2 * C₁ * K := by
    intro n hn hsub
    have h1 := hK₀ K hKK₀ n hn
    have h2 : Λ (n - K) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hnonneg _) hsub 2
    have := mul_le_mul_of_nonneg_left h2 (exp_pos (-(C₂ * K))).le
    linarith
  have hall : ∀ n, Λ n ≤ B := by
    intro n
    induction n with
    | zero => exact (hmono (Nat.zero_le K)).trans (le_max_left _ _)
    | succ n ih =>
      rcases Nat.lt_or_ge (n + 1) (K + 1) with h | h
      · exact (hmono (Nat.lt_succ_iff.1 h)).trans (le_max_left _ _)
      · refine (hΛ n).trans (max_le ih ?_)
        have hV := hVle (n + 1) (by omega) ((hmono (by omega : n + 1 - K ≤ n)).trans ih)
        have hsqrt : √(V (n + 1)) ≤ √(2 * C₁ * K) := Real.sqrt_le_sqrt hV
        exact (hr (n + 1)).trans ((exp_le_exp.2 (mul_le_mul_of_nonneg_left hsqrt hCp)).trans
          (le_max_right _ _))
  exact ⟨K, hK1, B, hB0, hall, fun n hn => hVle n hn (hall _)⟩

end T20
end DDDF
end LQGMetric
