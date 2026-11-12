/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_9Ratio at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Trans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.9: comparing the normalizations of `𝕣S_k` and `𝕣K`

Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
proof of Proposition 3.9 (T:1774–1775): "We apply the Gaussian tail bound to bound each of the
Gaussian random variables `h_{𝕣ρ_k}(𝕣u_k) − h_𝕣(0)` (which have constant order variance) and
Theorem 1.5 to compare `𝔠_{𝕣ρ_k}` to `𝔠_𝕣` up to a constant-order multiplicative error."

For a fixed `ρ ∈ (0,1)` the ratio `𝔠_{𝕣ρ} e^{ξh_{𝕣ρ}(𝕣u)} / (𝔠_𝕣 e^{ξh_𝕣(0)})` has
superpolynomial upper tails, uniformly in `𝕣`. The constant-order comparison of `𝔠_{𝕣ρ}` with
`𝔠_𝕣` for fixed `ρ` is Axiom V's bound `c(δr)/c(r) ≤ Λ δ^{-Λ}` (part of `IsWeakLQGMetric`, the
same comparison as Theorem 1.5 gives); the Gaussian tail is `L34.tail_far_part` (variance
`≤ log(1/ρ) + 2 log(|u|+1)`).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

/-- elementary: `2 e^{-y²/(2V)} ≤ 2 s^{-b}` once `log s` is large, `y = (log s - ℓ)/ξ` -/
lemma gauss_le_pow {ξ V ℓ b s : ℝ} (hξ : 0 < ξ) (hV : 0 < V) (hb : 0 < b)
    (hs : Real.exp (max (2 * ℓ) (8 * ξ ^ 2 * V * b)) ≤ s) :
    2 * Real.exp (-((Real.log s - ℓ) / ξ) ^ 2 / (2 * V)) ≤ 2 * s ^ (-b) := by
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  set x := Real.log s with hx
  have hx1 : max (2 * ℓ) (8 * ξ ^ 2 * V * b) ≤ x := by
    rw [hx, Real.le_log_iff_exp_le hs0]; exact hs
  have h2ℓ : 2 * ℓ ≤ x := (le_max_left _ _).trans hx1
  have hxb : 8 * ξ ^ 2 * V * b ≤ x := (le_max_right _ _).trans hx1
  have hx0 : 0 ≤ x := le_trans (by positivity) hxb
  rw [Real.rpow_def_of_pos hs0, ← hx]
  gcongr
  -- `b x ≤ ((x - ℓ)/ξ)² / (2V)`
  rw [mul_neg, neg_div, neg_le_neg_iff, div_pow, div_div, le_div_iff₀ (by positivity)]
  have h1 : x / 2 ≤ x - ℓ := by linarith
  have h2 : (x / 2) ^ 2 ≤ (x - ℓ) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  nlinarith [mul_le_mul_of_nonneg_left hxb hx0]

/-- **Superpolynomial upper tail of the ratio of normalizations** (T:1774–1775), canonical
space, uniformly in `𝕣`. -/
theorem ratio_upper_tail {γ : ℝ} (hγ0 : 0 < γ) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {μ : Measure DistC} [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWPGFF id μ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : ℂ) {b : ℝ}
    (hb : 0 < b) :
    ∃ s₀ : ℝ, 1 ≤ s₀ ∧ ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ s : ℝ, s₀ ≤ s →
      μ {g | s < scaleFac (xiGamma γ) c g (𝕣 * ρ) ((𝕣 : ℂ) * u) /
        scaleFac (xiGamma γ) c g 𝕣 0} ≤ ENNReal.ofReal (2 * s ^ (-b)) := by
  obtain ⟨Λ, hΛ1, hΛ⟩ := hD.tightness.2.1
  set ξ := xiGamma γ
  have hξ : 0 < ξ := GM.xiGamma_pos hγ0
  set L := Λ * ρ ^ (-Λ) with hL
  have hL0 : 0 < L := mul_pos (by linarith) (Real.rpow_pos_of_pos hρ0 _)
  set ℓ := Real.log L
  set V := Real.log (1 / ρ) + 2 * Real.log (‖u‖ + 1) with hV
  have hV0 : 0 < V := by
    have h1 : 0 < Real.log (1 / ρ) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hρ0, hρ1⟩)
    have h2 : 0 ≤ Real.log (‖u‖ + 1) := Real.log_nonneg (by linarith [norm_nonneg u])
    linarith
  set s₀ := Real.exp (max (2 * ℓ) (8 * ξ ^ 2 * V * b) + |ℓ| + 1)
  refine ⟨s₀, Real.one_le_exp (by positivity), fun 𝕣 h𝕣 s hs => ?_⟩
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  have hsL : ℓ < Real.log s := by
    rw [Real.lt_log_iff_exp_lt hs0]
    refine lt_of_lt_of_le (Real.exp_lt_exp.2 ?_) hs
    have := le_abs_self ℓ
    have : 0 ≤ max (2 * ℓ) (8 * ξ ^ 2 * V * b) := le_max_of_le_right (by positivity)
    linarith
  set y := (Real.log s - ℓ) / ξ
  have hy : 0 < y := div_pos (by linarith) hξ
  have htail := L34.tail_far_part (P := μ) (h := id) hμ.1 (w := (𝕣 : ℂ) * u) (a := 𝕣 * ρ)
    (ρ := 𝕣) (R := ‖u‖) (by positivity) (by nlinarith) (norm_nonneg u)
    (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h𝕣.le, mul_comm]) hy
  have hlog : Real.log (𝕣 / (𝕣 * ρ)) = Real.log (1 / ρ) := by
    congr 1; field_simp
  rw [hlog, ← hV] at htail
  refine le_trans (measure_mono fun g hg => ?_) (htail.trans (ENNReal.ofReal_le_ofReal
    (gauss_le_pow hξ hV0 hb ((Real.exp_le_exp.2 (by
      have := abs_nonneg ℓ; linarith)).trans hs))))
  simp only [mem_ofPred_eq, CircleAvg.cInc, id] at hg ⊢
  -- `s < (c(𝕣ρ)/c(𝕣)) e^{ξΔ} ≤ L e^{ξ|Δ|}`
  have hc𝕣 : 0 < c 𝕣 := hD.tightness.1 𝕣 h𝕣
  have hcr : c (𝕣 * ρ) / c 𝕣 ≤ L := by
    have := (hΛ ρ ⟨hρ0, hρ1⟩ 𝕣 h𝕣).2
    rwa [mul_comm ρ 𝕣] at this
  set Δ := circleAvg g (𝕣 * ρ) ((𝕣 : ℂ) * u) - circleAvg g 𝕣 0
  have hratio : scaleFac ξ c g (𝕣 * ρ) ((𝕣 : ℂ) * u) / scaleFac ξ c g 𝕣 0 =
      c (𝕣 * ρ) / c 𝕣 * Real.exp (ξ * Δ) := by
    unfold scaleFac
    rw [mul_sub, Real.exp_sub]
    field_simp
  rw [hratio] at hg
  have h1 : s < L * Real.exp (ξ * |Δ|) := by
    refine hg.trans_le (mul_le_mul hcr (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hL0.le)
    exact mul_le_mul_of_nonneg_left (le_abs_self _) hξ.le
  have h2 : Real.log s < ℓ + ξ * |Δ| := by
    rw [← Real.log_exp (ξ * |Δ|), ← Real.log_mul hL0.ne' (Real.exp_pos _).ne']
    exact Real.log_lt_log hs0 h1
  show y ≤ |Δ|
  rw [div_le_iff₀ hξ]
  linarith

end LQGMetric.DFGPS
