/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: MeshOnly/MeshOnlyNashDecay.lean.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal-power bound under power decay

If a positive function `X` with derivative `X'` on `[a, b]` satisfies `k X^(1+q) ≤ -X'` there,
for constants `k, q > 0`, then `X b ≤ (k q (b - a))^(-1/q)`. The bound does not depend on `X a`.

Proof: `Y = X^(-q)` has derivative `-q X^(-q-1) X' ≥ k q` on `[a, b]`, so
`Y b ≥ Y a + k q (b - a) ≥ k q (b - a)`. Taking the power `-1/q` reverses the inequality.
-/

open Set

namespace LatticeProb

/-- If `k X^(1+q) ≤ -X'` on `[a, b]` with `X > 0` there, then `X b ≤ (k q (b - a))^(-1/q)`.
The bound does not depend on the value `X a`. -/
theorem reciprocal_power_bound_of_power_decay
    (X X' : ℝ → ℝ) {a b k q : ℝ} (hab : a < b) (hk : 0 < k) (hq : 0 < q)
    (hX : ∀ s ∈ Icc a b, 0 < X s)
    (hderiv : ∀ s ∈ Icc a b, HasDerivAt X (X' s) s)
    (hdecay : ∀ s ∈ Icc a b, k * X s ^ (1 + q) ≤ -X' s) :
    X b ≤ (k * q * (b - a)) ^ (-1 / q) := by
  have hD (s : ℝ) (hs : s ∈ Icc a b) :=
    (hderiv s hs).rpow_const (p := -q) (Or.inl (hX s hs).ne')
  have hbound (s : ℝ) (hs : s ∈ Icc a b) :
      k * q ≤ deriv (fun t => X t ^ (-q)) s := by
    rw [(hD s hs).deriv]
    have hcancel : X s ^ (1 + q) * X s ^ (-q - 1) = 1 := by
      rw [← Real.rpow_add (hX s hs)]
      have he : (1 + q) + (-q - 1) = 0 := by ring
      rw [he, Real.rpow_zero]
    calc
      k * q = (k * X s ^ (1 + q)) * (q * X s ^ (-q - 1)) := by
        calc
          _ = k * q * (X s ^ (1 + q) * X s ^ (-q - 1)) := by rw [hcancel, mul_one]
          _ = _ := by ring
      _ ≤ (-X' s) * (q * X s ^ (-q - 1)) :=
        mul_le_mul_of_nonneg_right (hdecay s hs)
          (mul_nonneg hq.le (Real.rpow_nonneg (hX s hs).le _))
      _ = _ := by ring
  have hinc := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (f := fun t => X t ^ (-q))
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => hbound s (interior_subset hs))
    a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩ hab.le
  have hlow : k * q * (b - a) ≤ X b ^ (-q) := by
    linarith [Real.rpow_nonneg (hX a ⟨le_rfl, hab.le⟩).le (-q)]
  have hbase : 0 < k * q * (b - a) := mul_pos (mul_pos hk hq) (sub_pos.mpr hab)
  have hp := Real.rpow_le_rpow_of_nonpos hbase hlow
    (show -1 / q ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hq.le)
  have hXb : 0 ≤ X b := (hX b ⟨hab.le, le_rfl⟩).le
  rw [← Real.rpow_mul hXb] at hp
  have he : (-q) * (-1 / q) = 1 := by field_simp
  simpa only [he, Real.rpow_one] using hp

namespace ReciprocalPowerDecayExample

/-- The hypotheses of `reciprocal_power_bound_of_power_decay` hold for `X s = (1 + s)⁻¹` on
`[0, 1]` with `k = q = 1` and `X' s = -((1 + s)^2)⁻¹`, so the bound applies to this instance. -/
example : (fun s : ℝ => (1 + s)⁻¹) 1 ≤ (1 * 1 * (1 - 0 : ℝ)) ^ (-1 / (1 : ℝ)) := by
  refine reciprocal_power_bound_of_power_decay (fun s : ℝ => (1 + s)⁻¹)
    (fun s : ℝ => -((1 + s) ^ 2)⁻¹) (a := 0) (b := 1) (k := 1) (q := 1) (by norm_num)
    one_pos one_pos ?_ ?_ ?_
  · intro s hs
    exact inv_pos.mpr (by linarith [hs.1])
  · intro s hs
    have hpos : (0 : ℝ) < 1 + s := by linarith [hs.1]
    exact (((hasDerivAt_id' s).const_add 1).inv hpos.ne').congr_deriv (by ring)
  · intro s hs
    have hpos : (0 : ℝ) < 1 + s := by linarith [hs.1]
    norm_num [Real.rpow_two, inv_pow]

end ReciprocalPowerDecayExample

end LatticeProb
