import LatticeProb.Analysis.GridAnnulusApprox
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Counting annuli with grid parameters

The union bound over all annuli `B_r(z) \ B̄_s(z)` with `|z| ≤ ρ` and radii in a bounded range is reduced to a
finite family of annuli with grid parameters: centres in the lattice `η ℤ²` and radii in the geometric grid
`{q ^ n : n ∈ ℤ}`. This file bounds the size of that family: it has at most
`(2 ρ / η + 3) ^ 2 (log_q (y₁ / x₁) + 1) (log_q (y₂ / x₂) + 1)` members when the outer radii lie in `[x₁, y₁]` and
the inner radii in `[x₂, y₂]`.

## Main results

* `LatticeProb.zpow_exponent_mem_Icc`: if `x ≤ q ^ a ≤ y` with `q > 1` and `x > 0`, then
  `⌈log_q x⌉ ≤ a ≤ ⌊log_q y⌋`.
* `LatticeProb.card_Icc_ceil_logb_floor_logb_le`: this interval of exponents has at most `log_q (y / x) + 1` elements.
* `LatticeProb.lattice_index_mem_Icc`, `LatticeProb.card_lattice_index_le`: a lattice point `η (m + n i)` within `η`
  of a point of `B̄_ρ` has `|m|, |n| ≤ ⌊ρ / η⌋ + 1`; there are at most `2 ρ / η + 3` such indices per coordinate.
* `LatticeProb.gridAnnulusIndex`, `LatticeProb.card_gridAnnulusIndex_le`: the finite set of grid parameters and its
  size.
* `LatticeProb.exists_grid_annulus_approx_mem`: the grid annulus of `LatticeProb.exists_grid_annulus_approx` has its
  parameters in `gridAnnulusIndex`.
* `LatticeProb.measure_biUnion_finset_le_card_mul`: the union bound `P (⋃ i ∈ S, E i) ≤ #S p` when every
  `P (E i) ≤ p`.
-/

open Metric Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- If `x ≤ q ^ a ≤ y` with `q > 1` and `x > 0`, then `⌈log_q x⌉ ≤ a ≤ ⌊log_q y⌋`. -/
theorem zpow_exponent_mem_Icc {q x y : ℝ} (hq : 1 < q) (hx : 0 < x) {a : ℤ} (h₁ : x ≤ q ^ a)
    (h₂ : q ^ a ≤ y) : a ∈ Finset.Icc ⌈Real.logb q x⌉ ⌊Real.logb q y⌋ := by
  have hq0 : 0 < q := by linarith
  have hlog : Real.logb q (q ^ a) = a := by
    rw [← Real.rpow_intCast, Real.logb_rpow hq0 hq.ne']
  have hqa : 0 < q ^ a := zpow_pos hq0 a
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le]
    calc Real.logb q x ≤ Real.logb q (q ^ a) := Real.logb_le_logb_of_le hq hx h₁
      _ = a := hlog
  · rw [Int.le_floor]
    calc (a : ℝ) = Real.logb q (q ^ a) := hlog.symm
      _ ≤ Real.logb q y := Real.logb_le_logb_of_le hq hqa h₂

/-- The interval of integers `[⌈log_q x⌉, ⌊log_q y⌋]` has at most `log_q (y / x) + 1` elements, for `q > 1` and
`0 < x ≤ y`. -/
theorem card_Icc_ceil_logb_floor_logb_le {q x y : ℝ} (hq : 1 < q) (hx : 0 < x) (hxy : x ≤ y) :
    ((Finset.Icc ⌈Real.logb q x⌉ ⌊Real.logb q y⌋).card : ℝ) ≤ Real.logb q (y / x) + 1 := by
  have hy : 0 < y := hx.trans_le hxy
  have hdiv : Real.logb q (y / x) = Real.logb q y - Real.logb q x := Real.logb_div hy.ne' hx.ne'
  have hnn : 0 ≤ Real.logb q (y / x) := Real.logb_nonneg hq ((one_le_div hx).2 hxy)
  rw [Int.card_Icc]
  rcases le_or_gt 0 (⌊Real.logb q y⌋ + 1 - ⌈Real.logb q x⌉) with h | h
  · have hc : (((⌊Real.logb q y⌋ + 1 - ⌈Real.logb q x⌉).toNat : ℕ) : ℝ)
        = ((⌊Real.logb q y⌋ + 1 - ⌈Real.logb q x⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [hc]
    push_cast
    have h1 := Int.floor_le (Real.logb q y)
    have h2 := Int.le_ceil (Real.logb q x)
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    push_cast
    linarith

/-- A lattice point `η (m + n i)` within distance `η` of a point `z` with `|z| ≤ ρ` has
`|m|, |n| ≤ ⌊ρ / η⌋ + 1`. -/
theorem lattice_index_mem_Icc {η ρ : ℝ} (hη : 0 < η) {z : ℂ} (hz : ‖z‖ ≤ ρ) {m n : ℤ}
    (h : ‖z - (η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)‖ ≤ η) :
    m ∈ Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1) ∧
      n ∈ Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1) := by
  set w : ℂ := (η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I) with hw_def
  have hw : ‖w‖ ≤ ρ + η := by
    calc ‖w‖ = ‖z - (z - w)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z‖ + ‖z - w‖ := norm_sub_le _ _
      _ ≤ ρ + η := add_le_add hz h
  have hre : w.re = η * m := by simp [w]
  have him : w.im = η * n := by simp [w]
  have hdiv : (ρ + η) / η = ρ / η + 1 := by field_simp
  have key : ∀ k : ℤ, η * |(k : ℝ)| ≤ ρ + η → k ∈ Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1) := by
    intro k hk
    have hk' : |(k : ℝ)| ≤ ρ / η + 1 := by
      rw [← hdiv, le_div_iff₀ hη]
      linarith
    rw [Finset.mem_Icc]
    constructor
    · have : -k - 1 ≤ ⌊ρ / η⌋ := Int.le_floor.2 (by push_cast; linarith [neg_abs_le (k : ℝ)])
      omega
    · have : k - 1 ≤ ⌊ρ / η⌋ := Int.le_floor.2 (by push_cast; linarith [le_abs_self (k : ℝ)])
      omega
  constructor
  · refine key m ?_
    have h1 := Complex.abs_re_le_norm w
    rw [hre, abs_mul, abs_of_pos hη] at h1
    linarith
  · refine key n ?_
    have h1 := Complex.abs_im_le_norm w
    rw [him, abs_mul, abs_of_pos hη] at h1
    linarith

/-- There are at most `2 ρ / η + 3` integers `k` with `|k| ≤ ⌊ρ / η⌋ + 1`, for `η > 0` and `ρ ≥ 0`. -/
theorem card_lattice_index_le {η ρ : ℝ} (hη : 0 < η) (hρ : 0 ≤ ρ) :
    ((Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1)).card : ℝ) ≤ 2 * ρ / η + 3 := by
  have h0 : 0 ≤ ⌊ρ / η⌋ := Int.floor_nonneg.2 (div_nonneg hρ hη.le)
  have h : 0 ≤ ⌊ρ / η⌋ + 1 + 1 - -(⌊ρ / η⌋ + 1) := by omega
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg h]
  push_cast
  have h1 := Int.floor_le (ρ / η)
  have h2 : 2 * ρ / η = 2 * (ρ / η) := by ring
  linarith

/-- The grid parameters `(m, n, a, b)` of annuli `B_{q^a}(η (m + n i)) \ B̄_{q^b}(η (m + n i))` with
`|m|, |n| ≤ ⌊ρ / η⌋ + 1`, `⌈log_q x₁⌉ ≤ a ≤ ⌊log_q y₁⌋` and `⌈log_q x₂⌉ ≤ b ≤ ⌊log_q y₂⌋`. -/
noncomputable def gridAnnulusIndex (q η ρ x₁ y₁ x₂ y₂ : ℝ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1) ×ˢ Finset.Icc (-(⌊ρ / η⌋ + 1)) (⌊ρ / η⌋ + 1) ×ˢ
    Finset.Icc ⌈Real.logb q x₁⌉ ⌊Real.logb q y₁⌋ ×ˢ Finset.Icc ⌈Real.logb q x₂⌉ ⌊Real.logb q y₂⌋

/-- The number of grid parameters is at most `(2 ρ / η + 3) ^ 2 (log_q (y₁ / x₁) + 1) (log_q (y₂ / x₂) + 1)`. -/
theorem card_gridAnnulusIndex_le {q η ρ x₁ y₁ x₂ y₂ : ℝ} (hq : 1 < q) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (hx₁ : 0 < x₁) (hxy₁ : x₁ ≤ y₁) (hx₂ : 0 < x₂) (hxy₂ : x₂ ≤ y₂) :
    ((gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂).card : ℝ) ≤
      (2 * ρ / η + 3) ^ 2 * ((Real.logb q (y₁ / x₁) + 1) * (Real.logb q (y₂ / x₂) + 1)) := by
  have hA := card_lattice_index_le hη hρ
  have hB := card_Icc_ceil_logb_floor_logb_le hq hx₁ hxy₁
  have hC := card_Icc_ceil_logb_floor_logb_le hq hx₂ hxy₂
  have hB0 : 0 ≤ Real.logb q (y₁ / x₁) + 1 := by
    linarith [Real.logb_nonneg hq ((one_le_div hx₁).2 hxy₁)]
  have hA0 : 0 ≤ 2 * ρ / η + 3 := by
    have : 0 ≤ 2 * ρ / η := div_nonneg (by linarith) hη.le
    linarith
  simp only [gridAnnulusIndex, Finset.card_product]
  push_cast
  rw [sq, mul_assoc]
  exact mul_le_mul hA (mul_le_mul hA (mul_le_mul hB hC (Nat.cast_nonneg _) hB0) (by positivity) hA0)
    (by positivity) hA0

/-- The grid annulus of `LatticeProb.exists_grid_annulus_approx` has its parameters in `gridAnnulusIndex`
when `|z| ≤ ρ`, `x₁ ≤ (r - η) / q`, `r - η ≤ y₁`, `x₂ ≤ s + η` and `q (s + η) ≤ y₂`. -/
theorem exists_grid_annulus_approx_mem {q η ρ x₁ y₁ x₂ y₂ : ℝ} (hq : 1 < q) (hη : 0 < η) {z : ℂ}
    (hz : ‖z‖ ≤ ρ) {s r : ℝ} (hs : 0 ≤ s) (hr : η < r) (hx₁ : 0 < x₁) (hx₁r : x₁ ≤ (r - η) / q)
    (hy₁ : r - η ≤ y₁) (hx₂ : 0 < x₂) (hx₂s : x₂ ≤ s + η) (hy₂ : q * (s + η) ≤ y₂) :
    ∃ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      ‖z - (η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖ ≤ η ∧
      ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball z r ∧
      closedBall z s ⊆ closedBall ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2) ∧
      ball z s ⊆ ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2) ∧
      (r - η) / q < q ^ i.2.2.1 ∧ q ^ i.2.2.1 ≤ r - η ∧ s + η ≤ q ^ i.2.2.2 ∧
      q ^ i.2.2.2 < q * (s + η) := by
  obtain ⟨m, n, a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_grid_annulus_approx hq hη z hs hr
  obtain ⟨hm, hn⟩ := lattice_index_mem_Icc hη hz h1
  refine ⟨(m, n, a, b), ?_, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [gridAnnulusIndex, Finset.mem_product]
  exact ⟨hm, hn, zpow_exponent_mem_Icc hq hx₁ (hx₁r.trans h5.le) (h6.trans hy₁),
    zpow_exponent_mem_Icc hq hx₂ (hx₂s.trans h7) (h8.le.trans hy₂)⟩

/-- The union bound over a finite index set: if `P (E i) ≤ p` for every `i ∈ S`, then
`P (⋃ i ∈ S, E i) ≤ #S p`. -/
theorem measure_biUnion_finset_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ι) (E : ι → Set Ω) {p : ℝ≥0∞} (h : ∀ i ∈ S, P (E i) ≤ p) :
    P (⋃ i ∈ S, E i) ≤ S.card * p := by
  calc P (⋃ i ∈ S, E i) ≤ ∑ i ∈ S, P (E i) := measure_biUnion_finset_le S E
    _ ≤ ∑ _i ∈ S, p := Finset.sum_le_sum h
    _ = S.card * p := by rw [Finset.sum_const, nsmul_eq_mul]

end LatticeProb
