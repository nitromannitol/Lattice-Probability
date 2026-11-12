/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9An at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Ev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DG Proposition 3.9: the scales and the final arithmetic (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, proof of Proposition 3.9 (DG:1362–1389): the top level
`k₀ = ⌈β log₂ ε⁻¹⌉` (`|S| = 2^{-⌈log₂ ε^{-β}⌉}`, DG:1362), the bottom level
`K = ⌈(β + β̄) log₂ ε⁻¹⌉ + 2` (DG's `log₂ ε^{β−A}` steps, DG:1373, with `A = β̄` the exponent of
Lemma 3.8), and the arithmetic of (eqn-dist-to-X)–(eqn-dyadic-diam): the total is
`≤ 120 (K+2)^4 ε^{-β} ε^{-1/(d−ζ̃)} ≤ ε^{-1/(d−ζ)}` once `β = (1/(d−ζ) − 1/(d−ζ̃))/2`.
(DG keep the gain `ε^{β(2+γ²/2−2γ−ζ̃)/d}`; with `β` this small it is not needed.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DG

lemma p39d_eq_rpow (n : ℕ) : p39d n = (2 : ℝ) ^ (-(n : ℝ)) := by
  simp only [p39d]; rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

lemma p39_rpow_logb {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (2 : ℝ) ^ (a * Real.logb 2 ε⁻¹) = ε ^ (-a) := by
  rw [mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.2 hε), Real.inv_rpow hε.le,
    Real.rpow_neg hε.le]

lemma p39_logb_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : 0 < Real.logb 2 ε⁻¹ :=
  Real.logb_pos (by norm_num) (by rw [lt_inv_comm₀ one_pos hε, inv_one]; exact hε1)

/-- the top level `k₀ = ⌈β log₂ ε⁻¹⌉`: `2^{-k₀} ≤ ε^β` and `2^{k₀} ≤ 2 ε^{-β}` -/
lemma p39_k0 {ε β : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) :
    p39d ⌈β * Real.logb 2 ε⁻¹⌉₊ ≤ ε ^ β ∧
      (2 : ℝ) ^ ⌈β * Real.logb 2 ε⁻¹⌉₊ ≤ 2 * ε ^ (-β) := by
  have ht := p39_logb_pos hε hε1
  have h0 : 0 ≤ β * Real.logb 2 ε⁻¹ := by positivity
  constructor
  · rw [p39d_eq_rpow]
    calc (2 : ℝ) ^ (-(⌈β * Real.logb 2 ε⁻¹⌉₊ : ℝ)) ≤ 2 ^ ((-β) * Real.logb 2 ε⁻¹) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [Nat.le_ceil (β * Real.logb 2 ε⁻¹)])
      _ = ε ^ β := by rw [p39_rpow_logb hε, neg_neg]
  · rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (⌈β * Real.logb 2 ε⁻¹⌉₊ : ℝ) ≤ 2 ^ (β * Real.logb 2 ε⁻¹ + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.ceil_lt_add_one h0).le
      _ = 2 * ε ^ (-β) := by
          rw [Real.rpow_add (by norm_num), p39_rpow_logb hε, Real.rpow_one]; ring

/-- the bottom level `K = ⌈(β + β̄) log₂ ε⁻¹⌉ + 2` -/
lemma p39_K {ε β βb : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) (hβb : 0 < βb) :
    ⌈β * Real.logb 2 ε⁻¹⌉₊ ≤ ⌈(β + βb) * Real.logb 2 ε⁻¹⌉₊ + 2 ∧
      2 * p39d (⌈(β + βb) * Real.logb 2 ε⁻¹⌉₊ + 2) < ε ^ βb ∧
      ((⌈(β + βb) * Real.logb 2 ε⁻¹⌉₊ + 2 : ℕ) : ℝ) ≤ (β + βb) * Real.logb 2 ε⁻¹ + 3 := by
  have ht := p39_logb_pos hε hε1
  have h0 : 0 ≤ (β + βb) * Real.logb 2 ε⁻¹ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.ceil_mono (show β * Real.logb 2 ε⁻¹ ≤ (β + βb) * Real.logb 2 ε⁻¹ by nlinarith)
    omega
  · rw [p39d_eq_rpow]
    have e1 : (2 : ℝ) ^ (-(((⌈(β + βb) * Real.logb 2 ε⁻¹⌉₊ + 2 : ℕ)) : ℝ)) ≤
        2 ^ ((-(β + βb)) * Real.logb 2 ε⁻¹ + (-2)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      linarith [Nat.le_ceil ((β + βb) * Real.logb 2 ε⁻¹)]
    rw [Real.rpow_add (by norm_num), p39_rpow_logb hε, neg_neg] at e1
    have e2 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    have e3 : ε ^ (β + βb) ≤ ε ^ βb :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)
    have e4 : 0 < ε ^ βb := Real.rpow_pos_of_pos hε _
    rw [e2] at e1
    nlinarith
  · push_cast
    linarith [Nat.ceil_lt_add_one h0]

/-- `log₂ ε⁻¹ ≤ (2/η) ε^{-η}` -/
lemma p39_logb_le {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    Real.logb 2 ε⁻¹ ≤ 2 / η * ε ^ (-η) := by
  have h1 : Real.log ε⁻¹ ≤ ε⁻¹ ^ η / η := Real.log_le_rpow_div (inv_nonneg.2 hε.le) hη
  rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le] at h1
  have hl : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  rw [Real.logb]
  by_cases hn : Real.log ε⁻¹ ≤ 0
  · have : Real.log ε⁻¹ / Real.log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    have : 0 ≤ 2 / η * ε ^ (-η) := by have := Real.rpow_pos_of_pos hε (-η); positivity
    linarith
  · push Not at hn
    rw [div_le_iff₀ (by linarith)]
    have : 0 < ε ^ (-η) := Real.rpow_pos_of_pos hε _
    calc Real.log ε⁻¹ ≤ ε ^ (-η) / η := h1
      _ ≤ 2 / η * ε ^ (-η) * Real.log 2 := by
        rw [div_eq_mul_inv]; field_simp; nlinarith

/-- the final arithmetic (DG (eqn-dist-to-X)–(eqn-dyadic-diam)) -/
lemma p39_alg {K J k2 B E u v A : ℝ} (hJ : J ≤ K) (hJ0 : 0 ≤ J) (hK0 : 0 ≤ K)
    (hk2 : k2 ≤ 2 * u) (hk20 : 0 ≤ k2) (hu : 1 ≤ u) (hE : 1 ≤ E) (hB : B = (K + 2) ^ 3 + E)
    (hKv : K + 2 ≤ A * v) (hA : 120 * A ^ 4 ≤ v ^ 4) (hv : v ^ 8 = u) (hv0 : 0 ≤ v)
    (hA0 : 0 ≤ A) :
    2 + 2 * (B + J * (3 * B)) + (4 * k2 + 4) * (4 * B) ≤ u ^ 2 * E := by
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ K + 2) 3]
  have a1 : J * (3 * B) ≤ K * (3 * B) := mul_le_mul_of_nonneg_right hJ (by linarith)
  have a2 : (4 * k2 + 4) * (4 * B) ≤ (8 * u + 4) * (4 * B) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have a3 : B ≤ u * B := le_mul_of_one_le_left (by linarith) hu
  have a4 : K * B ≤ K * (u * B) := mul_le_mul_of_nonneg_left a3 hK0
  have a5 : 0 ≤ K * (u * B) := by have : 0 ≤ u * B := by nlinarith
                                  positivity
  have h1 : 2 + 2 * (B + J * (3 * B)) + (4 * k2 + 4) * (4 * B) ≤ 60 * (K + 2) * u * B := by
    nlinarith
  have hK3 : 0 ≤ (K + 2) ^ 3 := by positivity
  have hK1 : 1 ≤ (K + 2) ^ 3 := one_le_pow₀ (by linarith)
  have h2 : B ≤ 2 * (K + 2) ^ 3 * E := by
    rw [hB]
    nlinarith [mul_le_mul_of_nonneg_left hE hK3, mul_le_mul_of_nonneg_right hK1 (by linarith : (0 : ℝ) ≤ E)]
  have h3 : (K + 2) ^ 4 ≤ (A * v) ^ 4 := pow_le_pow_left₀ (by linarith) hKv 4
  have h4 : 120 * (K + 2) ^ 4 ≤ u := by
    rw [← hv]
    have : (A * v) ^ 4 = A ^ 4 * v ^ 4 := mul_pow A v 4
    have hv4 : 0 ≤ v ^ 4 := by positivity
    have : v ^ 8 = v ^ 4 * v ^ 4 := by ring
    nlinarith
  have hu0 : 0 ≤ u := by linarith
  calc 2 + 2 * (B + J * (3 * B)) + (4 * k2 + 4) * (4 * B) ≤ 60 * (K + 2) * u * B := h1
    _ ≤ 60 * (K + 2) * u * (2 * (K + 2) ^ 3 * E) := by gcongr
    _ = 120 * (K + 2) ^ 4 * (u * E) := by ring
    _ ≤ u * (u * E) := by gcongr
    _ = u ^ 2 * E := by ring

end DG
end LQGMetric
