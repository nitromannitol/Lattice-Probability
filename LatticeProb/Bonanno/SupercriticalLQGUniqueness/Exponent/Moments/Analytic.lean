/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Moments.Analytic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P26Up0




 



set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Moments

 


theorem moment_consequences (μ lam M₂ R S : ℝ) (hlam : 0 < lam)
    (hgeomLower : Real.exp (-R) * lam ≤ μ)
    (hgeomUpper : μ ≤ Real.exp R * lam)
    (hgeomSecond : M₂ ≤ (Real.exp S * lam) ^ 2) :
    0 < μ ∧ |Real.log μ - Real.log lam| ≤ R ∧
      Real.sqrt M₂ / μ ≤ Real.exp (S + R) := by
  have hμ : 0 < μ := (mul_pos (Real.exp_pos _) hlam).trans_le hgeomLower
  have hloglo : -R + Real.log lam ≤ Real.log μ := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos _) hlam) hgeomLower
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    exact h
  have hloghi : Real.log μ ≤ R + Real.log lam := by
    have h := Real.log_le_log hμ hgeomUpper
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    exact h
  have hlog : |Real.log μ - Real.log lam| ≤ R := by
    rw [abs_le]
    constructor <;> linarith
  have hM : Real.sqrt M₂ ≤ Real.exp S * lam := by
    have h := Real.sqrt_le_sqrt hgeomSecond
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) hlam)] at h
  have hlamμ : lam ≤ Real.exp R * μ := by
    calc
      lam = Real.exp R * (Real.exp (-R) * lam) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp R * μ := mul_le_mul_of_nonneg_left hgeomLower (Real.exp_pos _).le
  refine ⟨hμ, hlog, ?_⟩
  apply (div_le_div_of_nonneg_right hM hμ.le).trans
  apply (div_le_iff₀ hμ).2
  rw [Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left hlamμ (Real.exp_pos S).le]


 


theorem l1_07_of_annular_moments (μ lam M₂ : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlam : ∀ n, 0 < lam n)
    (hgeomLower : ∀ n : ℕ, Real.exp (-(C * Real.sqrt n + C)) * lam n ≤ μ n)
    (hgeomUpper : ∀ n : ℕ, μ n ≤ Real.exp (C * Real.sqrt n + C) * lam n)
    (hgeomSecond : ∀ n : ℕ, M₂ n ≤
      (Real.exp (C * Real.sqrt n + C) * lam n) ^ 2) :
    ∀ n : ℕ, 0 < μ n ∧
      |Real.log (μ n) - Real.log (lam n)| ≤ C * Real.sqrt n + C ∧
      Real.sqrt (M₂ n) / μ n ≤ Real.exp (2 * C) * Real.exp (2 * C * Real.sqrt n) := by
  intro n
  have hR : 0 ≤ C * Real.sqrt n + C := by positivity
  have h := moment_consequences (μ n) (lam n) (M₂ n)
    (C * Real.sqrt n + C) (C * Real.sqrt n + C)
    (hlam n) (hgeomLower n) (hgeomUpper n) (hgeomSecond n)
  refine ⟨h.1, h.2.1, ?_⟩
  convert h.2.2 using 1
  rw [← Real.exp_add]
  congr 1
  ring


 

theorem exp_sqrt_sub_four_thirds_eventually_half
    (K M c : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      K * Real.exp (M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ)) ≤ 1 / 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have hroot : ∀ᶠ n : ℕ in atTop,
      (M + 1) / c ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hlim : Tendsto (fun n : ℕ => K * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul K
  have hsmall : ∀ᶠ n : ℕ in atTop, K * Real.exp (-(n : ℝ)) < 1 / 2 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hroot, hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hsmalln hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsqrt : Real.sqrt n ≤ (n : ℝ) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hnfrac : (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by ring, Real.rpow_add (by positivity),
      Real.rpow_one]
  have hcoef : M + 1 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      M + 1 = c * ((M + 1) / c) := by field_simp
      _ ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hn hc.le
  have hpow : (M + 1) * (n : ℝ) ≤ c * (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [hnfrac]
    nlinarith [mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ n)]
  have hexp : M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ) ≤ -(n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hM]
  calc
    K * Real.exp (M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ))
        ≤ K * Real.exp (-(n : ℝ)) := by gcongr
    _ ≤ 1 / 2 := hsmalln.le


 
theorem recursion_absorb_half (u good coeff : ℝ) (hu : 0 ≤ u)
    (hcoeff : coeff ≤ 1 / 2) (hsplit : u ≤ good + coeff * u) :
    u ≤ 2 * good := by
  have hbad : coeff * u ≤ (1 / 2 : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcoeff hu
  linarith


 



theorem recursion_of_covered_split (μ : ℕ → ℝ) (C K M c : ℝ)
    (hμ : ∀ n, 0 ≤ μ n) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hgeomCoveredSplit : ∀ m k : ℕ, 8 ≤ m → 1 ≤ k →
      μ (m + k) ≤
        C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k +
        K * Real.exp (M * Real.sqrt (m + k : ℕ) -
          c * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ)) * μ (m + k)) :
    ∃ n₀ : ℕ, ∀ m k : ℕ, 8 ≤ m → 1 ≤ k → n₀ ≤ m + k →
      μ (m + k) ≤
        2 * C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (exp_sqrt_sub_four_thirds_eventually_half K M c hK hM hc)
  refine ⟨n₀, ?_⟩
  intro m k hm hk hmk
  have hhalf := hn₀ (m + k) hmk
  have hsplit := hgeomCoveredSplit m k hm hk
  have habs := recursion_absorb_half (μ (m + k))
    (C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k)
    (K * Real.exp (M * Real.sqrt (m + k : ℕ) -
      c * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ))) (hμ _) hhalf hsplit
  convert habs using 1; ring


 



end SupercriticalLQGUniqueness.Exponent.Moments
