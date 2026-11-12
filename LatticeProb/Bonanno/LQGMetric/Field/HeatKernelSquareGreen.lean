/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareGreen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareTheta

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sine (eigenfunction) expansion of the Dirichlet heat kernel of an interval and a square
(task P2-KHSQ)

From the Poisson-summation form of the image sums (`HeatSq.tsum_gauss1_shift_eq_cos`) and
`cos(α − β) − cos(α + β) = 2 sin α sin β`, the image kernel of `(a, a+L)` is the classical
Dirichlet eigenfunction expansion (Feller, *An Introduction to Probability Theory and its
Applications* II, §X.5 (method of images); Karatzas–Shreve, *Brownian Motion and Stochastic
Calculus*, Problem 2.8.8):

  `q_s(u,v) = (2/L) ∑_{k ≥ 1} e^{−π²k²s/(2L²)} sin(πk(u−a)/L) sin(πk(v−a)/L)`
  (`HeatSq.hasSum_intervalDirKernel_sine`),

and the square kernel `p^D_s = q_s ⊗ q_s` is the double series over `(j,k)`
(`HeatSq.hasSum_sqDirKernel_sine`).
-/

noncomputable section

open Real

namespace LQGMetric
namespace HeatSq

/-- the Dirichlet sine mode `sin(πk(u−a)/L)` of `(a, a+L)` -/
def sinMode (a L : ℝ) (k : ℕ) (u : ℝ) : ℝ := Real.sin (π * k * (u - a) / L)

/-- the heat factor `e^{−π²k²s/(2L²)}` of the `k`-th mode -/
def modeDecay (L s : ℝ) (k : ℕ) : ℝ := Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2)

lemma abs_sinMode_le (a L : ℝ) (k : ℕ) (u : ℝ) : |sinMode a L k u| ≤ 1 := abs_sin_le_one _

lemma modeDecay_pos (L s : ℝ) (k : ℕ) : 0 < modeDecay L s k := Real.exp_pos _

lemma summable_modeDecay {L s : ℝ} (hs : 0 < s) (hL : 0 < L) :
    Summable (modeDecay L s) := by
  have hl : 0 < π ^ 2 / (2 * L ^ 2) * s := by positivity
  have h := (summable_exp_neg_mul_int_sq' hl).comp_injective Nat.cast_injective
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, modeDecay, Int.cast_natCast]
  congr 1; ring

/-- **Sine series of the interval kernel.** -/
theorem hasSum_intervalDirKernel_sine {a L s : ℝ} (hs : 0 < s) (hL : 0 < L) (u v : ℝ) :
    HasSum (fun k : ℕ => 2 / L * (modeDecay L s k * (sinMode a L k u * sinMode a L k v)))
      (intervalDirKernel a L s u v) := by
  set l := π ^ 2 / (2 * L ^ 2) with hl
  have hl0 : 0 < l * s := by positivity
  set E : ℤ → ℝ := fun k => Real.exp (-l * s * k ^ 2) with hE
  have hEs : Summable E := (summable_exp_neg_mul_int_sq' hl0).congr fun k => by
    simp only [hE]; congr 1; ring
  have hc : ∀ c : ℝ, Summable fun k : ℤ => E k * Real.cos (π * k * c / L) := fun c =>
    hEs.of_norm_bounded fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cos_le_one _)
  set G : ℤ → ℝ := fun k => 2 * (E k * (Real.sin (π * k * (u - a) / L) *
    Real.sin (π * k * (v - a) / L))) with hG
  have hGsum : HasSum G ((2 * L)⁻¹⁻¹ * intervalDirKernel a L s u v) := by
    rw [intervalDirKernel_eq_sub hs hL, tsum_gauss1_shift_eq_cos hs hL,
      tsum_gauss1_shift_eq_cos hs hL, ← mul_sub, ← mul_assoc, inv_mul_cancel₀ (by positivity),
      one_mul, ← (hc _).tsum_sub (hc _)]
    refine ((hc _).sub (hc _)).hasSum.congr_fun fun k => ?_
    simp only [hG, hE]
    have e1 : π * k * (u - v) / L = π * k * (u - a) / L - π * k * (v - a) / L := by ring
    have e2 : π * k * (u + v - 2 * a) / L = π * k * (u - a) / L + π * k * (v - a) / L := by
      ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  have h2 := hGsum.nat_add_neg
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, add_zero] at h2
  have e : (fun k : ℕ => 2 / L * (modeDecay L s k * (sinMode a L k u * sinMode a L k v))) =
      fun n : ℕ => (2 * L)⁻¹ * (G n + G (-n)) := by
    funext n
    simp only [hG, hE, modeDecay, sinMode, ← hl, Int.cast_neg, Int.cast_natCast, neg_sq,
      neg_mul, mul_neg, neg_div, Real.sin_neg, neg_neg]
    field_simp
    ring
  rw [e]
  have h3 := h2.mul_left (2 * L)⁻¹
  rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at h3

end HeatSq
end LQGMetric
