/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28L1E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28L1D

/-!
# DDDF Prop 28 Part 2 Step 1 for the family: elementary helpers (task P2-DDDF28L)

Helpers for `S6P28L1F` (scale selection, the summable bound of DDDF l. 1470). The main
results are described below.

DDDF = arXiv:1904.08021, `tightness.tex` l. 1455–1472 (+ l. 1648). `lowerStep1_of`: the union
bound over the scales `1 ≤ K < n` (DDDF's sum `∑_k P(E_{k,n,s})`, `eq:SndPart`) with the
one-scale bound `level_prob` (`P(E_K) ≤ C e^{-cK} e^{-cs}`, DDDF l. 1470; here
`≤ 2η ρ^K`), plus the pairs `δ < |x − x'| ≤ 16δ` (`lower_mid`). `s6_lowerStep1`:
`S6P28.S6LowerStep1 (xiGamma γ) W P α` for `α ≥ 1`, `α > ξ(Q+2)`, from (5.54) and (5.78) via
(5.76) `s6_eq5_76_of_554`, (6.98) `s6_eq6_98_of_554` and the left tail (6.103) for `R_{1,3}`
(`s6_tails_AB_of_554`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace S6P28L

open WhiteNoise SupTail Blueprint LFPP S6P28

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

lemma amgm_sqrt {β a k : ℝ} (hβ : 0 < β) (hk : 0 ≤ k) :
    a * √k ≤ β * k + a ^ 2 / (4 * β) := by
  rw [show β * k + a ^ 2 / (4 * β) = (4 * β ^ 2 * k + a ^ 2) / (4 * β) by field_simp,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * β * √k - a), Real.sq_sqrt hk]

lemma exp_neg_abs_log_le {x : ℝ} (hx : 0 < x) : Real.exp (-|Real.log x|) ≤ x :=
  (Real.exp_le_exp.2 (neg_abs_le _)).trans_eq (Real.exp_log hx)

/-- the scale of a pair: `4h < |x − y| ≤ 8h` for some `h = 2^{-K}`, `K ≥ 1` -/
lemma exists_scale {x y : ℂ} (hx : x ∈ closedUnitSquare) (hy : y ∈ closedUnitSquare)
    (hxy : 0 < ‖x - y‖) :
    ∃ K : ℕ, 1 ≤ K ∧ 4 * (2 : ℝ)⁻¹ ^ K ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ 8 * (2 : ℝ)⁻¹ ^ K := by
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have h2 : ‖x - y‖ ≤ 2 := by
    have := Complex.norm_le_abs_re_add_abs_im (x - y)
    rw [Complex.sub_re, Complex.sub_im] at this
    have a1 : |x.re - y.re| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have a2 : |x.im - y.im| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  set t := ‖x - y‖ / 4 with ht
  have ht0 : 0 < t := by positivity
  have h1t : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near h1t (by norm_num : (1 : ℝ) < 2)
  refine ⟨N + 1, by omega, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ ^ (N + 1) < t := by
      rw [inv_pow, inv_lt_comm₀ (by positivity) ht0, ← one_div]; exact hN2
    linarith
  · have : t ≤ 2 * (2 : ℝ)⁻¹ ^ (N + 1) := by
      rw [pow_succ, inv_pow, ← mul_assoc, mul_comm 2, mul_assoc, mul_inv_cancel₀ two_ne_zero,
        mul_one, le_inv_comm₀ ht0 (by positivity), ← one_div]; exact hN1
    linarith

/-- the crossing term at scale `K` (DDDF l. 1470: `≤ C e^{-cK} e^{-cs}`): `16·4^K C₁ e^{-c₁ s²}
≤ η e^{-2wK}` once `s ≥ B' + βK` with `B'` large -/
lemma cross_term_le {c₁ C₁ η β w B' s : ℝ} (K : ℕ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hη : 0 < η)
    (hβ : 0 < β) (hB'3 : 3 ≤ B') (hcB : Real.log 4 + 2 * w ≤ 2 * c₁ * B' * β)
    (hB1 : |Real.log (η / (16 * C₁))| ≤ c₁ * B' ^ 2) (hsK : B' + β * K ≤ s) :
    4 * (4 * 4 ^ K) * (C₁ * Real.exp (-c₁ * s ^ 2)) ≤ η * Real.exp (-(2 * w) * K) := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hB0 : 0 ≤ B' := by linarith
  have hsq : B' ^ 2 + 2 * B' * β * K ≤ s ^ 2 := by
    have h0 : 0 ≤ B' + β * K := by positivity
    have h2 : (B' + β * K) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ h0 hsK 2
    nlinarith [sq_nonneg (β * K)]
  have e1 : Real.exp (-c₁ * s ^ 2) ≤ Real.exp (-(c₁ * B' ^ 2)) *
      Real.exp (-(Real.log 4 + 2 * w) * K) := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
    have h1 := mul_le_mul_of_nonneg_right hcB hK0
    have h2 := mul_le_mul_of_nonneg_left hsq hc₁.le
    nlinarith
  have e2 : Real.exp (-(c₁ * B' ^ 2)) ≤ η / (16 * C₁) :=
    (Real.exp_le_exp.2 (neg_le_neg hB1)).trans (exp_neg_abs_log_le (by positivity))
  have e4 : (4 : ℝ) ^ K = Real.exp (Real.log 4 * K) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc 4 * (4 * 4 ^ K) * (C₁ * Real.exp (-c₁ * s ^ 2))
      ≤ 4 * (4 * 4 ^ K) * (C₁ * (Real.exp (-(c₁ * B' ^ 2)) *
          Real.exp (-(Real.log 4 + 2 * w) * K))) := by gcongr
    _ ≤ 4 * (4 * 4 ^ K) * (C₁ * (η / (16 * C₁) *
          Real.exp (-(Real.log 4 + 2 * w) * K))) := by gcongr
    _ = η * (Real.exp (Real.log 4 * K) * Real.exp (-(Real.log 4 + 2 * w) * K)) := by
        rw [e4]; field_simp; ring
    _ = η * Real.exp (-(2 * w) * K) := by
        rw [← Real.exp_add]; congr 2; ring

/-- the choice of `B'` -/
lemma exists_B {c₁ C₁ η β w : ℝ} (hc₁ : 0 < c₁) (hβ : 0 < β) (hw : 0 < w) :
    ∃ B' : ℝ, 3 ≤ B' ∧ Real.log 4 + 2 * w ≤ 2 * c₁ * B' * β ∧
      |Real.log (η / (16 * C₁))| ≤ c₁ * B' ^ 2 := by
  set a := (Real.log 4 + 2 * w) / (2 * c₁ * β)
  set b := |Real.log (η / (16 * C₁))| / c₁
  have ha : 0 ≤ a := by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); positivity
  have hb : 0 ≤ b := by positivity
  refine ⟨3 + a + b, by linarith, ?_, ?_⟩
  · have : a * (2 * c₁ * β) = Real.log 4 + 2 * w := div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : a ≤ 3 + a + b)
      (by positivity : (0 : ℝ) ≤ 2 * c₁ * β)]
  · have : b * c₁ = |Real.log (η / (16 * C₁))| := div_mul_cancel₀ _ hc₁.ne'
    have h1 : b ≤ (3 + a + b) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hc₁.le]

/-- `∑_{1 ≤ K < n} 2η ρ^K ≤ ε/2` for `η = ε(1−ρ)/4` -/
lemma geom_bound {ε ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    ∑ K ∈ Finset.Ico 1 n, 2 * (ε * (1 - ρ) / 4) * ρ ^ K ≤ ε / 2 ∨ ε < 0 := by
  rcases lt_or_ge ε 0 with h | h
  · exact Or.inr h
  left
  rw [← Finset.mul_sum]
  have h1 := geom_sum_Ico_le_of_lt_one (m := 1) (n := n) hρ0 hρ1
  have h2 : ρ ^ 1 / (1 - ρ) ≤ 1 / (1 - ρ) := by
    rw [pow_one]; exact div_le_div_of_nonneg_right hρ1.le (by linarith)
  have h3 : 2 * (ε * (1 - ρ) / 4) * (1 / (1 - ρ)) = ε / 2 := by
    have : 1 - ρ ≠ 0 := by linarith
    field_simp; ring
  have h4 : 0 ≤ 2 * (ε * (1 - ρ) / 4) := by have := sub_pos.2 hρ1; positivity
  calc 2 * (ε * (1 - ρ) / 4) * ∑ K ∈ Finset.Ico 1 n, ρ ^ K
      ≤ 2 * (ε * (1 - ρ) / 4) * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left (h1.trans h2) h4
    _ = ε / 2 := h3

end S6P28L
end DDDF
end LQGMetric
