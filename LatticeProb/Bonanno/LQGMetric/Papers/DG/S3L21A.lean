/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L21A at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DG Lemma 3.21: the exponent bookkeeping (P2-DG105i)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Lemma 3.21
(`lem-square-dist`, DG:1678–1719), the chain (eqn-square-dist-T) (DG:1708–1714): on the event
(eqn-field-control') (DG:1693–1697), with `δ_ε = 2^{-M}`, `n = 2^k`, the factor
`T_S = (n/δ_ε)^{2+γ²/2} e^{−γ min_{S(1)} ĥ_{δ_ε/n}}` satisfies
* `T_S ε ≤ ε_*` for `ε` small (`l321_x_le`: DG "`max_S T_S ε = o_ε(1)`", DG:1715–1716, using
  `β < 2/(2+γ)²`), and
* Lemma 3.19's bound at `T_S ε` is at least (eqn-square-dist) (`l321_tgt_le_thr`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LQGMetric
namespace DG

/-- `T_S ε` (DG:1703–1705), `δ_ε/n = 2^{-(M+k)}`, `m = min_{S(1)} ĥ_{δ_ε/n}` -/
def l321X (γ ε : ℝ) (M k : ℕ) (m : ℝ) : ℝ :=
  ε * (((2 : ℝ)⁻¹ ^ (M + k)) ^ (2 + γ ^ 2 / 2))⁻¹ * Real.exp (-(γ * m))

/-- DG's bound of Lemma 3.19 at `T_S ε` (DG:1617–1619): `e^{−√n} (T_S ε)^{-1/(d+ζ₁)}` -/
def l321Thr (γ d ζ₁ ε : ℝ) (M k : ℕ) (m : ℝ) : ℝ :=
  Real.exp (-√((2 : ℝ) ^ k)) * l321X γ ε M k m ^ (-(1 / (d + ζ₁)))

/-- DG's bound (eqn-square-dist) (DG:1684–1687), `x = max_{S(1)} ĥ_{ε^β}` -/
def l321Tgt (γ d ζ β ε x : ℝ) : ℝ :=
  ε ^ (-(1 / d) + β * (2 + γ ^ 2 / 2) / d + ζ) * Real.exp (γ / d * x)

lemma l321_logX {γ ε m : ℝ} (hε : 0 < ε) (M k : ℕ) :
    Real.log (l321X γ ε M k m) =
      Real.log ε + (2 + γ ^ 2 / 2) * ((M + k) * Real.log 2) - γ * m := by
  unfold l321X
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hε.ne' (by positivity),
    Real.log_inv, Real.log_rpow (by positivity), Real.log_pow, Real.log_inv, Real.log_exp]
  push_cast; ring

/-- `log 2^{-M} ≥ β log ε − log 2` from `ε^β ≤ 2 · 2^{-M}` -/
lemma l321_M_le {ε β : ℝ} {M : ℕ} (hε : 0 < ε) (hδ : ε ^ β ≤ 2 * (2 : ℝ)⁻¹ ^ M) :
    (M : ℝ) * Real.log 2 ≤ Real.log 2 - β * Real.log ε := by
  have h := Real.log_le_log (by positivity) hδ
  rw [Real.log_rpow hε, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_inv] at h
  linarith

/-- **`T_S ε ≤ ε_*`** (DG:1715–1716) -/
theorem l321_x_le {γ β ε ζt Mx m εs : ℝ} {M k : ℕ} (hγ : 0 < γ) (hβ : 0 ≤ β)
    (hε : 0 < ε) (hεs : 0 < εs) (hδ : ε ^ β ≤ 2 * (2 : ℝ)⁻¹ ^ M)
    (hm : Mx - ζt * Real.log ε⁻¹ ≤ m) (hMx : |Mx| ≤ (2 + ζt) * β * Real.log ε⁻¹)
    (hs : -((1 - β * (2 + γ ^ 2 / 2) - γ * (2 + ζt) * β - γ * ζt) * Real.log ε⁻¹) +
      (2 + γ ^ 2 / 2) * (k * Real.log 2) + (2 + γ ^ 2 / 2) * Real.log 2 ≤ Real.log εs) :
    l321X γ ε M k m ≤ εs := by
  have hx : 0 < l321X γ ε M k m := by unfold l321X; positivity
  rw [← Real.exp_log hx, ← Real.exp_log hεs, l321_logX hε]
  refine Real.exp_le_exp.2 ?_
  have hM := l321_M_le hε hδ
  rw [Real.log_inv] at hm hMx hs
  have hξ : 0 ≤ 2 + γ ^ 2 / 2 := by positivity
  have h1 : (2 + γ ^ 2 / 2) * (M * Real.log 2) ≤ (2 + γ ^ 2 / 2) * (Real.log 2 - β * Real.log ε) :=
    mul_le_mul_of_nonneg_left hM hξ
  have h2 : γ * (Mx - ζt * -Real.log ε) ≤ γ * m := mul_le_mul_of_nonneg_left hm hγ.le
  have h3 : γ * (-Mx) ≤ γ * ((2 + ζt) * β * -Real.log ε) :=
    mul_le_mul_of_nonneg_left ((neg_le_abs Mx).trans hMx) hγ.le
  linarith [h1, h2, h3]

/-- **the deterministic step of DG Lemma 3.21** (DG:1708–1719) -/
theorem l321_tgt_le_thr {γ d ζ ζ₁ ζt β ε Mx m : ℝ} {M k : ℕ} (hγ : 0 < γ) (hd : 1 ≤ d)
    (hζ₁ : 0 ≤ ζ₁) (hβ : 0 ≤ β) (hβξ : β * (2 + γ ^ 2 / 2) ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : ε ^ β ≤ 2 * (2 : ℝ)⁻¹ ^ M)
    (hm : Mx - ζt * Real.log ε⁻¹ ≤ m) (hMx : |Mx| ≤ (2 + ζt) * β * Real.log ε⁻¹)
    (hpar : 1 / (d + ζ₁) * γ * ζt + ζ₁ / d ^ 2 * (1 + γ * (2 + ζt) * β) ≤ ζ / 2)
    (hn : √((2 : ℝ) ^ k) + (2 + γ ^ 2 / 2) * (k * Real.log 2) + (2 + γ ^ 2 / 2) * Real.log 2 ≤
      ζ / 2 * Real.log ε⁻¹) :
    l321Tgt γ d ζ β ε Mx ≤ l321Thr γ d ζ₁ ε M k m := by
  unfold l321Tgt l321Thr
  have hx : 0 < l321X γ ε M k m := by unfold l321X; positivity
  rw [Real.rpow_def_of_pos hx, l321_logX hε, Real.rpow_def_of_pos hε, ← Real.exp_add,
    ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hM := l321_M_le hε hδ
  rw [Real.log_inv] at hm hMx hn
  set ℓ := -Real.log ε with hℓ
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; linarith [Real.log_neg hε hε1]
  have hd0 : 0 < d := by linarith
  set α₁ := 1 / (d + ζ₁) with hα₁
  have hα₁0 : 0 ≤ α₁ := by positivity
  have hα₁1 : α₁ ≤ 1 := by rw [hα₁, div_le_one (by linarith)]; linarith
  have hα₁d : α₁ ≤ 1 / d := one_div_le_one_div_of_le hd0 (by linarith)
  have hα₁d' : -(ζ₁ / d ^ 2) ≤ α₁ - 1 / d := by
    rw [hα₁]
    have : 1 / (d + ζ₁) - 1 / d = -(ζ₁ / (d * (d + ζ₁))) := by field_simp; ring
    rw [this, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hζ₁ (by positivity) (by nlinarith)
  set ξ := 2 + γ ^ 2 / 2 with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  -- products
  have p1 : α₁ * (ξ * (M * Real.log 2)) ≤ α₁ * (ξ * (Real.log 2 + β * ℓ)) := by
    have := mul_le_mul_of_nonneg_left hM hξ0
    exact mul_le_mul_of_nonneg_left (by rw [hℓ]; linarith) hα₁0
  have p2 : α₁ * (γ * (Mx - ζt * ℓ)) ≤ α₁ * (γ * m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hγ.le) hα₁0
  have p3 : -(ζ₁ / d ^ 2) * ℓ ≤ (α₁ - 1 / d) * ℓ * (1 - β * ξ) := by
    have h1 : -(ζ₁ / d ^ 2) * ℓ ≤ (α₁ - 1 / d) * ℓ := mul_le_mul_of_nonneg_right hα₁d' hℓ0
    have h2 : (α₁ - 1 / d) * ℓ ≤ (α₁ - 1 / d) * ℓ * (1 - β * ξ) := by
      have hneg : (α₁ - 1 / d) * ℓ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hℓ0
      have hb : 0 ≤ β * ξ := mul_nonneg hβ hξ0
      nlinarith
    linarith
  have p4 : -(ζ₁ / d ^ 2) * (γ * ((2 + ζt) * β * ℓ)) ≤ (α₁ - 1 / d) * (γ * Mx) := by
    have hγM : |γ * Mx| ≤ γ * ((2 + ζt) * β * ℓ) := by
      rw [abs_mul, abs_of_pos hγ]; exact mul_le_mul_of_nonneg_left hMx hγ.le
    have hc : 0 ≤ ζ₁ / d ^ 2 := by positivity
    have := abs_le.1 hγM
    have hlow : -(ζ₁ / d ^ 2) ≤ α₁ - 1 / d := hα₁d'
    have hhigh : α₁ - 1 / d ≤ 0 := by linarith
    nlinarith [abs_nonneg (γ * Mx)]
  have p5 : α₁ * (ξ * Real.log 2) ≤ ξ * Real.log 2 :=
    mul_le_of_le_one_left (mul_nonneg hξ0 (Real.log_nonneg (by norm_num))) hα₁1
  have p6 : α₁ * (ξ * (k * Real.log 2)) ≤ ξ * (k * Real.log 2) :=
    mul_le_of_le_one_left (by positivity) hα₁1
  have p7 := mul_le_mul_of_nonneg_right hpar hℓ0
  have e : Real.log ε = -ℓ := by rw [hℓ]; ring
  rw [e]
  clear_value ℓ α₁ ξ
  have q1 : -ℓ * (-(1 / d) + β * ξ / d + ζ) + γ / d * Mx =
      -((α₁ - 1 / d) * ℓ * (1 - β * ξ)) - (α₁ - 1 / d) * (γ * Mx) - ζ * ℓ +
        (α₁ * ℓ - α₁ * ξ * β * ℓ + α₁ * γ * Mx) := by ring
  have q2 : (-ℓ + ξ * ((M + k) * Real.log 2) - γ * m) * -α₁ =
      α₁ * ℓ - α₁ * (ξ * (M * Real.log 2)) - α₁ * (ξ * (k * Real.log 2)) + α₁ * (γ * m) := by
    ring
  have q3 : α₁ * (ξ * (Real.log 2 + β * ℓ)) = α₁ * (ξ * Real.log 2) + α₁ * ξ * β * ℓ := by ring
  have q4 : α₁ * (γ * (Mx - ζt * ℓ)) = α₁ * γ * Mx - α₁ * γ * ζt * ℓ := by ring
  have q5 : (α₁ * γ * ζt + ζ₁ / d ^ 2 * (1 + γ * (2 + ζt) * β)) * ℓ =
      α₁ * γ * ζt * ℓ + ζ₁ / d ^ 2 * ℓ + ζ₁ / d ^ 2 * (γ * ((2 + ζt) * β * ℓ)) := by ring
  have q6 : -(ζ₁ / d ^ 2) * (γ * ((2 + ζt) * β * ℓ)) = -(ζ₁ / d ^ 2 * (γ * ((2 + ζt) * β * ℓ))) := by
    ring
  have q7 : -(ζ₁ / d ^ 2) * ℓ = -(ζ₁ / d ^ 2 * ℓ) := by ring
  rw [q1, q2]
  rw [q3] at p1; rw [q4] at p2; rw [q5] at p7; rw [q6] at p4; rw [q7] at p3
  linarith [p1, p2, p3, p4, p5, p6, p7]

end DG
end LQGMetric
