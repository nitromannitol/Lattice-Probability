/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.SlopeAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Moments.Analytic
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Fekete
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PowerWindow
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Window
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Uniqueness




 






set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.Exponent.SlopeAssembly

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem dyadic_median_slope_of_analytic_outputs
    (μ lam : ℕ → ℝ) (C K D : ℝ) (m₀ n₀ : ℕ)
    (hC : 0 ≤ C)
    (hμ : ∀ n, 0 < μ n)
    (hlam : ∀ n, 0 < lam n)
    (hcmp : ∀ n, |Real.log (μ n) - Real.log (lam n)| ≤
      D * Real.sqrt (n : ℝ) + D)
    (hlower : ∀ᶠ n : ℕ in atTop,
      -K * (n : ℝ) ≤ Real.logb 2 (μ n))
    (hsub : ∀ m k : ℕ, m₀ ≤ m → 1 ≤ k → n₀ ≤ m + k →
      Real.logb 2 (μ (m + k)) ≤ Real.logb 2 (μ m) +
        Real.logb 2 (μ k) + C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :
    ∃ α : ℝ, Tendsto
      (fun n : ℕ => (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := Exponent.Fekete.fekete_two_thirds_error_of_eventual_lower
    (fun n => Real.logb 2 (μ n)) C K m₀ n₀ hC hlower hsub
  refine ⟨-L, ?_⟩
  simpa only [neg_neg] using
    Exponent.PowerWindow.logb_median_asymptotic μ lam (-L) D hμ hlam
      (by simpa only [neg_neg] using hL) hcmp


 


theorem dyadic_median_slope_of_l1_06_outputs
    (μ lam M₂ : ℕ → ℝ) (C D K : ℝ) (m₀ n₀ : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hlam : ∀ n, 0 < lam n)
    (hgeomLower : ∀ n : ℕ,
      Real.exp (-(C * Real.sqrt n + C)) * lam n ≤ μ n)
    (hgeomUpper : ∀ n : ℕ,
      μ n ≤ Real.exp (C * Real.sqrt n + C) * lam n)
    (hgeomSecond : ∀ n : ℕ,
      M₂ n ≤ (Real.exp (C * Real.sqrt n + C) * lam n) ^ 2)
    (hlower : ∀ᶠ n : ℕ in atTop,
      -K * (n : ℝ) ≤ Real.logb 2 (μ n))
    (hsub : ∀ m k : ℕ, m₀ ≤ m → 1 ≤ k → n₀ ≤ m + k →
      Real.logb 2 (μ (m + k)) ≤ Real.logb 2 (μ m) +
        Real.logb 2 (μ k) + D * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) :
    ∃ α : ℝ, Tendsto
      (fun n : ℕ => (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hMoments := Exponent.Moments.l1_07_of_annular_moments μ lam M₂ C hC hlam
    hgeomLower hgeomUpper hgeomSecond
  exact dyadic_median_slope_of_analytic_outputs μ lam D K C m₀ n₀ hD
    (fun n => (hMoments n).1) hlam (fun n => (hMoments n).2.1) hlower hsub


 

theorem logb_recursion_of_l1_11
    (μ : ℕ → ℝ) (C : ℝ) (n₀ : ℕ)
    (hC : 1 ≤ C) (hμ : ∀ n, 0 < μ n)
    (hrec : ∀ m k : ℕ, 8 ≤ m → 1 ≤ k → n₀ ≤ m + k →
      μ (m + k) ≤
        2 * C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) *
          μ m * μ k) :
    ∀ m k : ℕ, 8 ≤ m → 1 ≤ k → n₀ ≤ m + k →
      Real.logb 2 (μ (m + k)) ≤ Real.logb 2 (μ m) +
        Real.logb 2 (μ k) +
          ((Real.log (2 * C) + C) / Real.log 2) *
            ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
  intro m k hm hk hn
  let t : ℝ := ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)
  have hmk : (1 : ℝ) ≤ (m + k : ℕ) := by exact_mod_cast (by omega : 1 ≤ m + k)
  have ht : 1 ≤ t := Real.one_le_rpow hmk (by norm_num)
  have hCpos : 0 < 2 * C := by linarith
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (hμ (m + k)) (hrec m k hm hk hn)
  have heq : Real.log
      (2 * C * Real.exp (C * t) * μ m * μ k) =
      Real.log (2 * C) + C * t + Real.log (μ m) + Real.log (μ k) := by
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hCpos.ne' (Real.exp_pos _).ne')
      (hμ m).ne') (hμ k).ne',
      Real.log_mul (mul_ne_zero hCpos.ne' (Real.exp_pos _).ne') (hμ m).ne',
      Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [show C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ) = C * t by rfl] at hlog
  rw [heq] at hlog
  have hlog' : Real.log (μ (m + k)) ≤
      Real.log (μ m) + Real.log (μ k) + (Real.log (2 * C) + C) * t := by
    nlinarith [mul_le_mul_of_nonneg_left ht hlogC]
  dsimp [Real.logb]
  apply (div_le_div_of_nonneg_right hlog' hlog2.le).trans
  dsimp only [t]
  ring_nf
  exact le_refl _


 


theorem dyadic_median_slope_of_analytic_summaries
    (μ lam M₂ : ℕ → ℝ) (Cmom Crec Kbad M c Klower : ℝ)
    (hCmom : 0 ≤ Cmom) (hCrec : 1 ≤ Crec)
    (hKbad : 0 ≤ Kbad) (hM : 0 ≤ M) (hc : 0 < c)
    (hlam : ∀ n, 0 < lam n)
    (hgeomLower : ∀ n : ℕ,
      Real.exp (-(Cmom * Real.sqrt n + Cmom)) * lam n ≤ μ n)
    (hgeomUpper : ∀ n : ℕ,
      μ n ≤ Real.exp (Cmom * Real.sqrt n + Cmom) * lam n)
    (hgeomSecond : ∀ n : ℕ,
      M₂ n ≤ (Real.exp (Cmom * Real.sqrt n + Cmom) * lam n) ^ 2)
    (hlower : ∀ᶠ n : ℕ in atTop,
      -Klower * (n : ℝ) ≤ Real.logb 2 (μ n))
    (hCoveredSplit : ∀ m k : ℕ, 8 ≤ m → 1 ≤ k →
      μ (m + k) ≤
        Crec * Real.exp (Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) *
          μ m * μ k +
        Kbad * Real.exp (M * Real.sqrt (m + k : ℕ) -
          c * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ)) * μ (m + k)) :
    ∃ α : ℝ, Tendsto
      (fun n : ℕ => (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hMoments := Exponent.Moments.l1_07_of_annular_moments μ lam M₂ Cmom hCmom hlam
    hgeomLower hgeomUpper hgeomSecond
  obtain ⟨n₀, hrec⟩ := Exponent.Moments.recursion_of_covered_split μ Crec Kbad M c
    (fun n => (hMoments n).1.le) hKbad hM hc hCoveredSplit
  have hD : 0 ≤ (Real.log (2 * Crec) + Crec) / Real.log 2 := by
    apply div_nonneg
    · have : 1 ≤ 2 * Crec := by linarith
      exact add_nonneg (Real.log_nonneg this) (by linarith)
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hlogrec := logb_recursion_of_l1_11 μ Crec n₀ hCrec
    (fun n => (hMoments n).1) hrec
  exact dyadic_median_slope_of_l1_06_outputs μ lam M₂ Cmom
    ((Real.log (2 * Crec) + Crec) / Real.log 2) Klower 8 n₀
    hCmom hD hlam hgeomLower hgeomUpper hgeomSecond hlower hlogrec


 

theorem slope_of_normalized_error (lam : ℕ → ℝ) (α : ℝ)
    (h : Tendsto (fun n : ℕ =>
      (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.logb 2 (lam n) / (n : ℝ)) atTop (𝓝 (-α)) := by
  have hs := h.sub (tendsto_const_nhds (x := α) (f := atTop))
  have hs' : Tendsto (fun n : ℕ =>
      (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ) - α)
      atTop (𝓝 (-α)) := by
    simpa only [zero_sub] using hs
  apply hs'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring


 


theorem existsUnique_of_reference_slopes
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {W₀ : WNSpace → Ω₀ → ℝ} (hW₀ : IsWhiteNoise P₀ W₀)
    (hSlopes : ∀ ξ : Set.Ioi (0 : ℝ), ∃ α : ℝ,
      Tendsto (fun n : ℕ =>
        Real.logb 2 (lambdaN (ξ : ℝ) W₀ P₀ n) / (n : ℝ))
        atTop (𝓝 (-α))) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∃! Q : ℝ, IsLFPPExponent ξ Q := by
  intro ξ
  obtain ⟨α, hα⟩ := hSlopes ξ
  refine ⟨(1 - α) / (ξ : ℝ),
    Exponent.Median.isLFPPExponent_of_dyadic_median_slope P₀ hW₀ ξ α hα, ?_⟩
  intro Q hQ
  exact isLFPPExponent_unique ξ Q _ hQ
    (Exponent.Median.isLFPPExponent_of_dyadic_median_slope P₀ hW₀ ξ α hα)


 

theorem existsUnique_of_normalized_reference_slopes
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {W₀ : WNSpace → Ω₀ → ℝ} (hW₀ : IsWhiteNoise P₀ W₀)
    (hSlopes : ∀ ξ : Set.Ioi (0 : ℝ), ∃ α : ℝ,
      Tendsto (fun n : ℕ =>
        (Real.logb 2 (lambdaN (ξ : ℝ) W₀ P₀ n) + α * (n : ℝ)) / (n : ℝ))
        atTop (𝓝 0)) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∃! Q : ℝ, IsLFPPExponent ξ Q := by
  apply existsUnique_of_reference_slopes P₀ hW₀
  intro ξ
  obtain ⟨α, hα⟩ := hSlopes ξ
  exact ⟨α, slope_of_normalized_error _ α hα⟩


end SupercriticalLQGUniqueness.Exponent.SlopeAssembly
