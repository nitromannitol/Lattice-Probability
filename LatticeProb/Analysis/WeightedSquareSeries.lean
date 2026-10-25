import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# Weighted square series

Completing a weighted square proves countable weighted Cauchy--Schwarz.
Absolute summability also controls uniformly bounded weighted families.
-/

namespace LatticeProb

noncomputable section

/-- Completing a weighted square bounds the square of the weighted first moment. -/
theorem sq_tsum_mul_le {ι : Type*} {w v : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (hfirst : Summable (fun i => w i * v i))
    (hsecond : Summable (fun i => w i * v i ^ 2)) :
    (∑' i, w i * v i) ^ 2 ≤ (∑' i, w i) * ∑' i, w i * v i ^ 2 := by
  let W := ∑' i, w i
  let B := ∑' i, w i * v i
  let Q := ∑' i, w i * v i ^ 2
  have hW : 0 ≤ W := tsum_nonneg hw
  by_cases hzero : W = 0
  · have hwzero : ∀ i, w i = 0 := by
      intro i
      exact le_antisymm (by simpa only [W, hzero] using hs.le_tsum i (fun j _ => hw j))
        (hw i)
    simp only [hwzero, zero_mul, tsum_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
  · have heq : (∑' i, w i * (v i - B / W) ^ 2) =
        Q - 2 * (B / W) * B + (B / W) ^ 2 * W := by
      have hterm (i) : w i * (v i - B / W) ^ 2 =
          w i * v i ^ 2 - (2 * (B / W)) * (w i * v i) +
            (B / W) ^ 2 * w i := by ring
      simp_rw [hterm]
      rw [((hsecond.sub (hfirst.mul_left _)).tsum_add (hs.mul_left _)),
        hsecond.tsum_sub (hfirst.mul_left _), tsum_mul_left, tsum_mul_left]
    have hnonneg : 0 ≤ ∑' i, w i * (v i - B / W) ^ 2 := tsum_nonneg (fun i => mul_nonneg (hw i)
      (sq_nonneg (v i - B / W)))
    rw [heq] at hnonneg
    have halg : W * (Q - 2 * (B / W) * B + (B / W) ^ 2 * W) = W * Q - B ^ 2 := by
      field_simp [hzero]
      ring
    have hm := mul_nonneg hW hnonneg
    rw [halg] at hm
    exact sub_nonneg.mp hm

/-- Absolute summability controls a weighted family of uniformly bounded variables. -/
theorem summable_weighted_bounded {ι Ω : Type*} {X : ι → Ω → ℝ} {b : ι → ℝ}
    (hb : Summable b) {K : ℝ} (hX : ∀ i ω, |X i ω| ≤ K) (ω : Ω) :
    Summable (fun i => b i * X i ω) := by
  apply (hb.abs.mul_right K).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hX i ω) (abs_nonneg _)

end

end LatticeProb
