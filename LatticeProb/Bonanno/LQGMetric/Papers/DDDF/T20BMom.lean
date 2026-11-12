/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20BMom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldExpTail

/-!
# DDDF Theorem 20, Step 4: exponential moments from `e^{-cs²/log s}` tails (task P2-DDDFT20b)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1164–1167 ((5.69) = `eq:FirstIneq`): the moments of
the ratio `max L(R^L) / min L(R^S)` over the `O(4^K)` rectangles of Step 4 are bounded by
`Λ_{n−K}² e^{C K^{1/2+ε₀}}` ("we could have a `log K` term instead"). DDDF give no computation;
own elementary step: a variable `X ≥ 0` with `P(X ≥ t) ≤ N C e^{-ct²/log t}` (`t > 2`; the union
bound of `T20BRect.lean`) has `E e^{lX} ≤ e^{l x₀} + 1` with
`x₀ = max(3, (4(l+1)/c)², (4 log(lNC+1)/c)^{2/3})` (`T20B.lintegral_exp_le_of_tail_logsq`),
i.e. `e^{O(log N)^{2/3}} = e^{O(K^{2/3})}` for `N = O(4^K)`: subexponential in `K`, which is all
that (5.70) needs (DDDF's `e^{CK^{1/2+ε₀}}` is also subexponential). Built on
`lintegral_exp_le_of_tail` (layer-cake).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

namespace T20B

/-- the threshold `x₀ = max(3, (4(l+1)/c)², (4 log(lNC+1)/c)^{2/3})` -/
def tailX0 (l N C c : ℝ) : ℝ :=
  max 3 (max ((4 * (l + 1) / c) ^ 2) ((4 * Real.log (l * N * C + 1) / c) ^ ((2 : ℝ) / 3)))

lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * √t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht)
  rw [Real.log_sqrt ht.le] at h
  linarith [Real.sqrt_nonneg t]

/-- the key inequality `L + (l+1) t ≤ c t² / log t` for `t ≥ x₀` -/
lemma tail_ineq {l N C c t : ℝ} (hl : 0 < l) (hN : 0 ≤ N) (hC : 0 < C) (hc : 0 < c)
    (ht : tailX0 l N C c ≤ t) :
    Real.log (l * N * C + 1) + (l + 1) * t ≤ c * t ^ 2 / Real.log t := by
  have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos (by linarith)
  have hs : 0 < √t := Real.sqrt_pos.2 ht0
  have hss : √t * √t = t := Real.mul_self_sqrt ht0.le
  have hlNC : 0 ≤ l * N * C := mul_nonneg (mul_nonneg hl.le hN) hC.le
  have hL0 : 0 ≤ Real.log (l * N * C + 1) := Real.log_nonneg (by linarith)
  -- `c t² / log t ≥ (c/2) t √t`
  have h1 : c / 2 * (t * √t) ≤ c * t ^ 2 / Real.log t := by
    rw [le_div_iff₀ hlog]
    have := log_le_two_sqrt ht0
    have e : c / 2 * (t * √t) * (2 * √t) = c * t ^ 2 := by
      have e2 : c / 2 * (t * √t) * (2 * √t) = c * t * (√t * √t) := by ring
      rw [e2, hss]; ring
    calc c / 2 * (t * √t) * Real.log t ≤ c / 2 * (t * √t) * (2 * √t) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c * t ^ 2 := e
  -- `(c/4) t √t ≥ (l+1) t`
  have h2 : (l + 1) * t ≤ c / 4 * (t * √t) := by
    have hq : (4 * (l + 1) / c) ^ 2 ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
    have hsq : 4 * (l + 1) / c ≤ √t := Real.le_sqrt_of_sq_le hq
    have : 4 * (l + 1) ≤ c * √t := by rw [div_le_iff₀ hc] at hsq; linarith
    nlinarith
  -- `(c/4) t √t ≥ L`
  have h3 : Real.log (l * N * C + 1) ≤ c / 4 * (t * √t) := by
    set y := 4 * Real.log (l * N * C + 1) / c
    have hy : 0 ≤ y := by positivity
    have hq : y ^ ((2 : ℝ) / 3) ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
    have hpow : (y ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) ≤ t ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hq (by norm_num)
    rw [← Real.rpow_mul hy, show (2 : ℝ) / 3 * (3 / 2) = 1 by norm_num, Real.rpow_one] at hpow
    have et : t ^ ((3 : ℝ) / 2) = t * √t := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [et] at hpow
    have : 4 * Real.log (l * N * C + 1) ≤ c * (t * √t) := by
      have := hpow; rw [div_le_iff₀ hc] at this; linarith
    linarith
  linarith

/-- **Exponential moment from an `e^{-ct²/log t}` tail** (own elementary step):
if `X ≥ 0` and `P(X ≥ t) ≤ N C e^{-ct²/log t}` for `t > 2`, then
`E e^{lX} ≤ e^{l x₀} + 1`, `x₀ = tailX0 l N C c`. -/
theorem lintegral_exp_le_of_tail_logsq [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : AEMeasurable X P) {l N C c : ℝ} (hl : 0 < l) (hN : 0 ≤ N)
    (hC : 0 < C) (hc : 0 < c)
    (htail : ∀ t, 2 < t → P {ω | t ≤ X ω} ≤
      ENNReal.ofReal (N * C * Real.exp (-c * t ^ 2 / Real.log t))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * X ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (l * tailX0 l N C c) + 1) := by
  set x₀ := tailX0 l N C c
  have hx3 : 3 ≤ x₀ := le_max_left _ _
  have h := lintegral_exp_le_of_tail (P := P) hX0 hXm (x₀ := x₀) (B := 1) (κ := 1) hl
    (by linarith) one_pos zero_le_one fun t ht => ?_
  · refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (-1 * x₀) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  · have ht2 : 2 < t := by linarith
    have hP : P.real {ω | t ≤ X ω} ≤ N * C * Real.exp (-c * t ^ 2 / Real.log t) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail t ht2)
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hkey := tail_ineq hl hN hC hc ht.le
    have hlNC : l * N * C ≤ Real.exp (Real.log (l * N * C + 1)) := by
      rw [Real.exp_log (by positivity)]; linarith
    calc l * Real.exp (l * t) * P.real {ω | t ≤ X ω}
        ≤ l * Real.exp (l * t) * (N * C * Real.exp (-c * t ^ 2 / Real.log t)) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = (l * N * C) * Real.exp (l * t + -c * t ^ 2 / Real.log t) := by
          rw [Real.exp_add]; ring
      _ ≤ Real.exp (Real.log (l * N * C + 1)) * Real.exp (l * t + -c * t ^ 2 / Real.log t) :=
          mul_le_mul_of_nonneg_right hlNC (Real.exp_pos _).le
      _ = Real.exp (Real.log (l * N * C + 1) + (l * t + -c * t ^ 2 / Real.log t)) :=
          (Real.exp_add _ _).symm
      _ ≤ 1 * Real.exp (-1 * t) := by
          rw [one_mul]
          refine Real.exp_le_exp.2 ?_
          have e : -c * t ^ 2 / Real.log t = -(c * t ^ 2 / Real.log t) := by ring
          rw [e]; linarith

end T20B

end DDDF
end LQGMetric
