/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6DiamMean at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamSum
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6T20Done

/-!
# DDDF Prop 27, Step 2: `E Diam ≤ C λ_n` (task P2-DDDF6d)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1370–1376: from `eq:SumObtained` (`s6_sumObtained`),
Prop 26 (`λ_{n−K} ≤ λ_n e^{C√K}/λ_K`) and the lower bound `λ_K ≥ 2^{-K(1 − ξQ + ζ)}` ((5.54)),
`E Diam([0,1]², e^{ξφ_{0,n}} ds) ≤ λ_n C Σ_K 2^{-Kξ(Q−2)/2} e^{C√K} ≤ C' λ_n` since `Q > 2`.

This file: the real-analysis tools (`sum_exp_bound`, `two_lt_Q'`, `rpow_four_eq`) and the lower
bound of `λ_K` from (5.54) (`lambdaN_lower_of_554`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6D

open LFPP T20E Blueprint WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma two_lt_Q' {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 2 < LQGMetric.Q γ := by
  unfold LQGMetric.Q
  have h : 2 / γ + γ / 2 - 2 = (2 - γ) ^ 2 / (2 * γ) := by field_simp; ring
  have : 0 < (2 - γ) ^ 2 / (2 * γ) := by
    have : 0 < 2 - γ := by linarith
    positivity
  linarith

/-- `D√x ≤ βx/2 + D²/(2β)` -/
lemma sqrt_le_lin {β D x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) :
    D * √x ≤ β / 2 * x + D ^ 2 / (2 * β) := by
  have hs := Real.sq_sqrt hx
  have h2 : 2 * β * (β / 2 * x + D ^ 2 / (2 * β)) = β ^ 2 * x + D ^ 2 := by field_simp
  have h3 : 2 * β * (D * √x) ≤ 2 * β * (β / 2 * x + D ^ 2 / (2 * β)) := by
    rw [h2]; nlinarith [sq_nonneg (β * √x - D), hs]
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- `4^x = e^{2x log 2}` and `2^{-K} = e^{-K log 2}` -/
lemma rpow_four_eq (x : ℝ) : (4 : ℝ) ^ x = Real.exp (2 * Real.log 2 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring_nf

lemma inv_two_pow_eq (K : ℕ) : (2 : ℝ)⁻¹ ^ K = Real.exp (-(Real.log 2) * K) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]

/-- **the lower bound `λ_K ≥ c 2^{-K(1 − ξq + ζ)}`** from (5.54) (`ℓ_K ≤ λ_K`) -/
theorem lambdaN_lower_of_554 (hW : IsWhiteNoise P W) {q : ℝ} (h554 : S6Eq5_54 ξ q W P)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ,
      c * Real.exp (-(Real.log 2) * (1 - ξ * q + ζ) * K) ≤ lambdaN ξ W P K := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨K₀, hK₀⟩ := h554 (1 / 2) (by norm_num) le_rfl ζ hζ
  set g : ℕ → ℝ := fun K => Real.exp (-(Real.log 2) * (1 - ξ * q + ζ) * K)
  have hg : ∀ K, 0 < g K := fun K => Real.exp_pos _
  set r : ℕ → ℝ := fun K => min 1 (lambdaN ξ W P K / g K)
  have hr0 : ∀ K, 0 < r K := fun K => lt_min one_pos (div_pos (lambdaN_pos hW K) (hg K))
  have hr1 : ∀ K, r K ≤ 1 := fun K => min_le_left _ _
  refine ⟨∏ K ∈ Finset.range K₀, r K, Finset.prod_pos fun K _ => hr0 K, fun K => ?_⟩
  have hc1 : ∏ K ∈ Finset.range K₀, r K ≤ 1 :=
    Finset.prod_le_one₀ (fun K _ => (hr0 K).le) fun K _ => hr1 K
  rcases lt_or_ge K K₀ with hK | hK
  · have hle : ∏ K ∈ Finset.range K₀, r K ≤ r K := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hK)]
      exact mul_le_of_le_one_right (hr0 K).le
        (Finset.prod_le_one₀ (fun K _ => (hr0 K).le) fun K _ => hr1 K)
    calc (∏ K ∈ Finset.range K₀, r K) * g K ≤ r K * g K :=
          mul_le_mul_of_nonneg_right hle (hg K).le
      _ ≤ lambdaN ξ W P K / g K * g K :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hg K).le
      _ = lambdaN ξ W P K := div_mul_cancel₀ _ (hg K).ne'
  · have h1 := hK₀ K hK
    have e : (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q + ζ))) = g K := by
      rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
    have h2 : ellN ξ W P K (ENNReal.ofReal (1 / 2)) ≤ lambdaN ξ W P K :=
      T20B.ellN_le_lambdaN (by norm_num) (by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp) K
    rw [e] at h1
    calc (∏ K ∈ Finset.range K₀, r K) * g K ≤ 1 * g K :=
          mul_le_mul_of_nonneg_right hc1 (hg K).le
      _ ≤ lambdaN ξ W P K := by rw [one_mul]; exact h1.trans h2

/-- one term of `eq:SumObtained` (DDDF l. 1372) -/
lemma term_bound {ξ K₂ C : ℝ} {q : ℕ} (hC0 : 0 ≤ C) {lam lamK lamNK c M₀ C₇ a : ℝ} (K : ℕ)
    (hc : 0 < c) (hlamK : c * Real.exp (-(Real.log 2) * a * K) ≤ lamK)
    (hNK : lamNK ≤ M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam / lamK) (hM₀ : 0 ≤ M₀)
    (hlam : 0 ≤ lam) (hNK0 : 0 ≤ lamNK) :
    (4 : ℝ) ^ (ξ * (K : ℝ) + K₂ * √(K : ℝ)) *
        ((4 ^ K * C) ^ ((q : ℝ)⁻¹) * ((2 : ℝ)⁻¹ ^ K * lamNK)) ≤
      C ^ ((q : ℝ)⁻¹) * M₀ / c * lam * Real.exp (Real.log 2 * (2 * ξ + 2 / q - 1 + a) * K +
        (2 * Real.log 2 * K₂ + |C₇|) * √(K : ℝ)) := by
  set L := Real.log 2
  have hK0 : 0 < lamK := lt_of_lt_of_le (by positivity) hlamK
  have h1 : lamNK ≤ M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam * Real.exp (L * a * K) / c := by
    refine hNK.trans ?_
    rw [div_le_div_iff₀ hK0 hc]
    have hc' : c ≤ lamK * Real.exp (L * a * K) := by
      have := mul_le_mul_of_nonneg_right hlamK (Real.exp_pos (L * a * K)).le
      rwa [mul_assoc, ← Real.exp_add, show -L * a * K + L * a * K = 0 by ring, Real.exp_zero,
        mul_one] at this
    have h0 : 0 ≤ M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam := by positivity
    calc M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam * c
        ≤ M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam * (lamK * Real.exp (L * a * K)) :=
          mul_le_mul_of_nonneg_left hc' h0
      _ = _ := by ring
  rw [Real.mul_rpow (by positivity) hC0, show ((4 : ℝ) ^ K) ^ ((q : ℝ)⁻¹) =
      (4 : ℝ) ^ ((K : ℝ) * (q : ℝ)⁻¹) by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)],
    rpow_four_eq, rpow_four_eq, inv_two_pow_eq]
  have hCq : 0 ≤ C ^ ((q : ℝ)⁻¹) := Real.rpow_nonneg hC0 _
  calc Real.exp (2 * L * (ξ * K + K₂ * √(K : ℝ))) * (Real.exp (2 * L * (K * (q : ℝ)⁻¹)) *
        C ^ ((q : ℝ)⁻¹) * (Real.exp (-L * K) * lamNK))
      ≤ Real.exp (2 * L * (ξ * K + K₂ * √(K : ℝ))) * (Real.exp (2 * L * (K * (q : ℝ)⁻¹)) *
        C ^ ((q : ℝ)⁻¹) * (Real.exp (-L * K) *
          (M₀ * Real.exp (|C₇| * √(K : ℝ)) * lam * Real.exp (L * a * K) / c))) := by
        gcongr
    _ = C ^ ((q : ℝ)⁻¹) * M₀ / c * lam * (Real.exp (2 * L * (ξ * K + K₂ * √(K : ℝ))) *
          Real.exp (2 * L * (K * (q : ℝ)⁻¹)) * Real.exp (-L * K) *
          Real.exp (|C₇| * √(K : ℝ)) * Real.exp (L * a * K)) := by ring
    _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

end S6D
end DDDF
end LQGMetric
