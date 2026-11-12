/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36UpperGood at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The bound on the good event (upper half of DFGPS Lemma 3.6)

Decision D52. On the event where the box paths exist (DG Prop 3.21), the oscillation of `h_δ` is
`≤ (ζ₁/ξ) log δ⁻¹`, the dyadic scale sums are `≤ δ^{−ζ₁}` and the two corner walks cost
`≤ δ^{−ξQ−ζ₁}`, the left–right graph distance is `≤ 18 δ^{−ξQ−3ζ₁} ≤ δ^{−ξQ−4ζ₁}`.
-/

noncomputable section

open Set

namespace LQGMetric.DFGPS.L36

open Blueprint
open LQGDimension.Blueprint.Draft (osc)

/-- `δ⁻¹ r (δ/r)^{1−s−t} ≤ δ^{−s−t} r^s` for `0 < r ≤ 1`, `t ≥ 0` -/
lemma box_scale_le {δ r s t : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 ≤ t) :
    δ⁻¹ * r * (δ / r) ^ (1 - s - t) ≤ δ ^ (-s - t) * r ^ s := by
  rw [Real.div_rpow hδ.le hr.le]
  have e1 : δ⁻¹ * δ ^ (1 - s - t) = δ ^ (-s - t) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]; ring_nf
  have e2 : r / r ^ (1 - s - t) = r ^ (s + t) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hr.le]
    nth_rewrite 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hr]; ring_nf
  have e3 : r ^ (s + t) ≤ r ^ s := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  calc δ⁻¹ * r * (δ ^ (1 - s - t) / r ^ (1 - s - t))
      = (δ⁻¹ * δ ^ (1 - s - t)) * (r / r ^ (1 - s - t)) := by ring
    _ = δ ^ (-s - t) * r ^ (s + t) := by rw [e1, e2]
    _ ≤ δ ^ (-s - t) * r ^ s := mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg hδ.le _)

/-- **Good-event bound.** -/
theorem graphLFPP_le_good {δ ξ s ζ₁ : ℝ} (hδ : 0 < δ) (hδ64 : δ ≤ 1/64) (hξ : 0 < ξ)
    (hs : 0 ≤ s) (hζ₁ : 0 ≤ ζ₁) {Φ : ℂ → ℝ} (hΦ : Continuous Φ) (G : ℝ → ℂ → ℝ) (N : ℕ)
    (hN : 64 * δ ≤ rk (N + 1))
    (hL : ∀ k < N + 1, ∃ q, DG.IsDGPath ((fun x => (rk k : ℂ) * x + 0) ''
      Metric.closedBall aL (3/4)) ((rk k : ℂ) * bL + 0) ((rk k : ℂ) * aL + 0) q ∧
      LQGDimension.lfppLength ξ Φ q ≤
        2 * rk k * Real.exp (ξ * G (rk k) 0) * (δ / rk k) ^ ((1 - s) - ζ₁))
    (hR : ∀ k < N + 1, ∃ q, DG.IsDGPath ((fun x => (rk k : ℂ) * x + 1) ''
      Metric.closedBall aR (3/4)) ((rk k : ℂ) * bR + 1) ((rk k : ℂ) * aR + 1) q ∧
      LQGDimension.lfppLength ξ Φ q ≤
        2 * rk k * Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁))
    (hosc : ξ * osc Φ (8 * δ) ≤ ζ₁ * Real.log (1 / δ))
    (hmL : ∑ k ∈ Finset.range (N + 1), rk k ^ s * Real.exp (ξ * G (rk k) 0) ≤ δ ^ (-ζ₁))
    (hmR : ∑ k ∈ Finset.range (N + 1), rk k ^ s * Real.exp (ξ * G (rk k) 1) ≤ δ ^ (-ζ₁))
    (hwL : ((gridWalk δ (1, 1) (rnd δ (xL (N + 1)))).map fun x => Real.exp (ξ * Φ x)).sum ≤
      δ ^ (-s - ζ₁))
    (hwR : ((gridWalk δ (rnd δ (xR (N + 1))) (mR δ, 1)).map fun x => Real.exp (ξ * Φ x)).sum ≤
      δ ^ (-s - ζ₁))
    (h18 : 18 ≤ δ ^ (-ζ₁)) :
    graphLFPP ξ δ Φ (leftVerts δ 1) (rightVerts δ 1) (rS 1) ≤ δ ^ (-s - 4 * ζ₁) := by
  have hdet := graphLFPP_le_det hδ hδ64 hξ.le hΦ N hN _ _ hL hR
  have hosc' : Real.exp (ξ * osc Φ (8 * δ)) ≤ δ ^ (-ζ₁) := by
    rw [Real.rpow_def_of_pos hδ]
    apply Real.exp_le_exp.2
    rw [one_div, Real.log_inv] at hosc
    linarith
  -- each box term
  have hbox : ∀ c : ℂ, ∀ k, 4 * δ⁻¹ * (2 * rk k * Real.exp (ξ * G (rk k) c) *
      (δ / rk k) ^ ((1 - s) - ζ₁)) ≤ 8 * δ ^ (-s - ζ₁) * (rk k ^ s * Real.exp (ξ * G (rk k) c)) :=
    fun c k => by
    have := box_scale_le (s := s) hδ (rk_pos k) ((rk_le_half k).trans (by norm_num)) hζ₁
    rw [show (1 - s) - ζ₁ = 1 - s - ζ₁ by ring]
    have he := (Real.exp_pos (ξ * G (rk k) c)).le
    calc 4 * δ⁻¹ * (2 * rk k * Real.exp (ξ * G (rk k) c) * (δ / rk k) ^ (1 - s - ζ₁))
        = 8 * Real.exp (ξ * G (rk k) c) * (δ⁻¹ * rk k * (δ / rk k) ^ (1 - s - ζ₁)) := by ring
      _ ≤ 8 * Real.exp (ξ * G (rk k) c) * (δ ^ (-s - ζ₁) * rk k ^ s) := by gcongr
      _ = _ := by ring
  have hsumL : 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) ≤ 8 * δ ^ (-s - ζ₁) * δ ^ (-ζ₁) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun k _ => hbox 0 k).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hmL (by positivity)
  have hsumR : 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 1) *
      (δ / rk k) ^ ((1 - s) - ζ₁) ≤ 8 * δ ^ (-s - ζ₁) * δ ^ (-ζ₁) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun k _ => hbox 1 k).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hmR (by positivity)
  set A := δ ^ (-s - ζ₁) with hA
  set B := δ ^ (-ζ₁) with hB
  have hA0 : 0 < A := Real.rpow_pos_of_pos hδ _
  have hB0 : 0 < B := Real.rpow_pos_of_pos hδ _
  have hfin : δ ^ (-s - 4 * ζ₁) = A * B * B * B := by
    rw [hA, hB, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
  set E := Real.exp (ξ * osc Φ (8 * δ))
  have hE0 : 0 < E := Real.exp_pos _
  have key : 4 * δ⁻¹ * E * (∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) + ∑ k ∈ Finset.range (N + 1), 2 * rk k *
      Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁)) ≤ B * (16 * A * B) := by
    have e : 4 * δ⁻¹ * E * (∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) + ∑ k ∈ Finset.range (N + 1), 2 * rk k *
      Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁)) =
      E * (4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) + 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k *
      Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁)) := by ring
    rw [e]
    have h2 : 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) + 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k *
      Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁) ≤ 16 * A * B := by
      linarith
    have h3 : 0 ≤ 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) 0) *
      (δ / rk k) ^ ((1 - s) - ζ₁) + 4 * δ⁻¹ * ∑ k ∈ Finset.range (N + 1), 2 * rk k *
      Real.exp (ξ * G (rk k) 1) * (δ / rk k) ^ ((1 - s) - ζ₁) := by
      have : ∀ c : ℂ, 0 ≤ ∑ k ∈ Finset.range (N + 1), 2 * rk k * Real.exp (ξ * G (rk k) c) *
          (δ / rk k) ^ ((1 - s) - ζ₁) := fun c => Finset.sum_nonneg fun k _ => by
        have := rk_pos k
        have : 0 ≤ (δ / rk k) ^ ((1 - s) - ζ₁) := Real.rpow_nonneg (by positivity) _
        positivity
      have h0 := this 0
      have h1 := this 1
      positivity
    calc E * _ ≤ B * _ := mul_le_mul_of_nonneg_right hosc' h3
      _ ≤ B * (16 * A * B) := mul_le_mul_of_nonneg_left h2 hB0.le
  have hAB : A ≤ A * B * B := by
    have hBB : 1 ≤ B * B := by nlinarith
    calc A = A * 1 := by ring
      _ ≤ A * (B * B) := mul_le_mul_of_nonneg_left hBB hA0.le
      _ = A * B * B := by ring
  have hfinal : 18 * (A * B * B) ≤ A * B * B * B := by
    have := mul_le_mul_of_nonneg_left h18 (by positivity : 0 ≤ A * B * B)
    linarith
  rw [hfin]
  refine hdet.trans ?_
  linarith [hwL, hwR, key, hAB, hfinal]

end LQGMetric.DFGPS.L36
