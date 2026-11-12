import LatticeProb.Analysis.PlanarPackingInverseSquare
import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Counting fat planar cells close to a point

Let `H i`, `i ∈ s`, be bounded planar cells, each containing an open disc of radius
`κ · diam (H i)` (an *inball* of relative size `κ`), the inballs being pairwise disjoint. Call a
cell *near* `u` if `dist(u, H i) ≤ diam (H i)`. Near cells of comparable diameter `d ≤ diam ≤ 2d`
all lie in the disc of radius `4d` about `u`, so packing their inballs shows that there are at
most `16 / κ²` of them. Summing over dyadic scales, near cells with diameters in `[m, M]` number
at most `(log₂ (M / m) + 1) · 16 / κ²`.

This is the counting step of the planar packing argument for effective resistance upper bounds
(cells close to the source of a unit flow are few when cells are fat and of controlled size).

## Main results

* `LatticeProb.subset_closedBall_infDist_add_diam`: `H ⊆ closedBall u (dist(u, H) + diam H)`.
* `LatticeProb.pairwiseDisjoint_ball_of_aedisjoint`: open discs inside pairwise a.e.-disjoint
  sets are pairwise disjoint.
* `LatticeProb.card_le_of_infDist_le_diam_of_scale`: one dyadic scale, at most `16 / κ²` cells.
* `LatticeProb.card_le_of_infDist_le_diam`: all scales between `m` and `M`, with `Int.log 2`.
* `LatticeProb.card_le_logb_of_infDist_le_diam`: the same bound with `Real.logb 2 (M / m)`.
-/

open MeasureTheory Metric Set Function

namespace LatticeProb

/-- A bounded set lies in the closed disc about `u` of radius `dist(u, H) + diam H`. -/
theorem subset_closedBall_infDist_add_diam {u : ℂ} {H : Set ℂ} (hb : Bornology.IsBounded H) :
    H ⊆ closedBall u (infDist u H + diam H) := by
  intro x hx
  rw [mem_closedBall, dist_comm]
  have : dist u x - diam H ≤ infDist u H := by
    rw [le_infDist ⟨x, hx⟩]
    intro y hy
    have h1 := dist_triangle u y x
    have h2 := dist_le_diam_of_mem hb hy hx
    linarith
  linarith

/-- Open discs contained in pairwise almost-everywhere disjoint planar sets are pairwise
disjoint. -/
theorem pairwiseDisjoint_ball_of_aedisjoint {ι : Type*} {s : Set ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {ρ : ι → ℝ} (hd : s.Pairwise (AEDisjoint volume on H))
    (hball : ∀ i ∈ s, ball (c i) (ρ i) ⊆ H i) :
    s.PairwiseDisjoint fun i => ball (c i) (ρ i) := by
  intro i hi j hj hij
  have h0 : volume (ball (c i) (ρ i) ∩ ball (c j) (ρ j)) = 0 :=
    measure_mono_null (inter_subset_inter (hball i hi) (hball j hj)) (hd hi hj hij)
  rw [(isOpen_ball.inter isOpen_ball).measure_eq_zero_iff volume] at h0
  exact disjoint_iff_inter_eq_empty.mpr h0

/-- **Near fat cells at one scale.** Cells `H i` with pairwise disjoint inballs
`ball (c i) (κ · diam (H i)) ⊆ H i`, diameters in `[d, 2d]` and `dist(u, H i) ≤ diam (H i)`
number at most `16 / κ²`. -/
theorem card_le_of_infDist_le_diam_of_scale {ι : Type*} {s : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {κ d : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (c i) (κ * diam (H i)))
    (hball : ∀ i ∈ s, ball (c i) (κ * diam (H i)) ⊆ H i)
    (hb : ∀ i ∈ s, Bornology.IsBounded (H i))
    (hlo : ∀ i ∈ s, d ≤ diam (H i)) (hhi : ∀ i ∈ s, diam (H i) ≤ 2 * d)
    (hnear : ∀ i ∈ s, infDist u (H i) ≤ diam (H i)) :
    (s.card : ℝ) ≤ 16 / κ ^ 2 := by
  have hpack := card_mul_sq_le_sq_of_pairwiseDisjoint_ball (r := κ * d) (R := 4 * d) (z := u)
    (mul_pos hκ hd) hdisj
    (fun i hi => (hball i hi).trans ((subset_closedBall_infDist_add_diam (hb i hi)).trans
      (closedBall_subset_closedBall (by linarith [hnear i hi, hhi i hi]))))
    (fun i hi => mul_le_mul_of_nonneg_left (hlo i hi) hκ.le)
  rw [le_div_iff₀ (by positivity)]
  have h2 : ((s.card : ℝ) * κ ^ 2) * d ^ 2 ≤ 16 * d ^ 2 := by
    calc ((s.card : ℝ) * κ ^ 2) * d ^ 2 = (s.card : ℝ) * (κ * d) ^ 2 := by ring
      _ ≤ (4 * d) ^ 2 := hpack
      _ = 16 * d ^ 2 := by ring
  exact le_of_mul_le_mul_right h2 (by positivity)

/-- **Near fat cells over all scales.** Cells `H i` with pairwise disjoint inballs
`ball (c i) (κ · diam (H i)) ⊆ H i`, diameters in `[m, M]` and `dist(u, H i) ≤ diam (H i)`
number at most `(⌊log₂ (M / m)⌋ + 1) · 16 / κ²`. -/
theorem card_le_of_infDist_le_diam {ι : Type*} {s : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {κ m M : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (c i) (κ * diam (H i)))
    (hball : ∀ i ∈ s, ball (c i) (κ * diam (H i)) ⊆ H i)
    (hb : ∀ i ∈ s, Bornology.IsBounded (H i))
    (hlo : ∀ i ∈ s, m ≤ diam (H i)) (hhi : ∀ i ∈ s, diam (H i) ≤ M)
    (hnear : ∀ i ∈ s, infDist u (H i) ≤ diam (H i)) :
    (s.card : ℝ) ≤ ((Int.log 2 (M / m)).toNat + 1) * (16 / κ ^ 2) := by
  set K := (Int.log 2 (M / m)).toNat with hK
  set k : ι → ℕ := fun i => (Int.log 2 (diam (H i) / m)).toNat with hkdef
  have hx1 : ∀ i ∈ s, 1 ≤ diam (H i) / m := fun i hi => (one_le_div hm).2 (hlo i hi)
  have hk : ∀ i ∈ s, k i ∈ Finset.range (K + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Int.toNat_le_toNat (Int.log_mono_right (zero_lt_one.trans_le (hx1 i hi))
      (div_le_div_of_nonneg_right (hhi i hi) hm.le))
  -- the scale of each cell
  have hscale : ∀ i ∈ s, m * 2 ^ k i ≤ diam (H i) ∧ diam (H i) ≤ 2 * (m * 2 ^ k i) := by
    intro i hi
    set x := diam (H i) / m with hx
    have hxpos : 0 < x := zero_lt_one.trans_le (hx1 i hi)
    have hl0 : 0 ≤ Int.log 2 x := by
      rw [← (Int.log_one_right 2 : Int.log 2 (1 : ℝ) = 0)]
      exact Int.log_mono_right zero_lt_one (hx1 i hi)
    have hkl : ((k i : ℕ) : ℤ) = Int.log 2 x := Int.toNat_of_nonneg hl0
    have hlow : ((2 : ℕ) : ℝ) ^ Int.log 2 x ≤ x := Int.zpow_log_le_self (by norm_num) hxpos
    have hupp : x < ((2 : ℕ) : ℝ) ^ (Int.log 2 x + 1) := Int.lt_zpow_succ_log_self (by norm_num) x
    rw [← hkl, zpow_natCast, Nat.cast_ofNat] at hlow
    rw [← hkl, show ((k i : ℕ) : ℤ) + 1 = ((k i + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      Nat.cast_ofNat] at hupp
    rw [hx, le_div_iff₀ hm] at hlow
    rw [hx, div_lt_iff₀ hm] at hupp
    constructor
    · linarith
    · rw [pow_succ] at hupp; linarith
  rw [Finset.card_eq_sum_card_fiberwise hk]
  push_cast
  calc ∑ j ∈ Finset.range (K + 1), (({i ∈ s | k i = j}).card : ℝ)
      ≤ ∑ _j ∈ Finset.range (K + 1), 16 / κ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hsub : (({i ∈ s | k i = j} : Finset ι) : Set ι) ⊆ s := by
          intro i hi; exact (Finset.mem_filter.mp hi).1
        refine card_le_of_infDist_le_diam_of_scale (u := u) (d := m * 2 ^ j) hκ (by positivity)
          (hdisj.subset hsub) ?_ ?_ ?_ ?_ ?_
        · intro i hi; exact hball i (Finset.mem_filter.mp hi).1
        · intro i hi; exact hb i (Finset.mem_filter.mp hi).1
        · intro i hi
          obtain ⟨his, hkj⟩ := Finset.mem_filter.mp hi
          exact hkj ▸ (hscale i his).1
        · intro i hi
          obtain ⟨his, hkj⟩ := Finset.mem_filter.mp hi
          exact hkj ▸ (hscale i his).2
        · intro i hi; exact hnear i (Finset.mem_filter.mp hi).1
    _ = ((K : ℝ) + 1) * (16 / κ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- **Near fat cells over all scales**, with `Real.logb`: under the hypotheses of
`card_le_of_infDist_le_diam` and `m ≤ M`, there are at most `(log₂ (M / m) + 1) · 16 / κ²` near
cells. -/
theorem card_le_logb_of_infDist_le_diam {ι : Type*} {s : Finset ι} {H : ι → Set ℂ}
    {c : ι → ℂ} {u : ℂ} {κ m M : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hmM : m ≤ M)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (c i) (κ * diam (H i)))
    (hball : ∀ i ∈ s, ball (c i) (κ * diam (H i)) ⊆ H i)
    (hb : ∀ i ∈ s, Bornology.IsBounded (H i))
    (hlo : ∀ i ∈ s, m ≤ diam (H i)) (hhi : ∀ i ∈ s, diam (H i) ≤ M)
    (hnear : ∀ i ∈ s, infDist u (H i) ≤ diam (H i)) :
    (s.card : ℝ) ≤ (Real.logb 2 (M / m) + 1) * (16 / κ ^ 2) := by
  refine (card_le_of_infDist_le_diam hκ hm hdisj hball hb hlo hhi hnear).trans ?_
  have h1 : 1 ≤ M / m := (one_le_div hm).2 hmM
  have hl0 : 0 ≤ Int.log 2 (M / m) := by
    rw [← (Int.log_one_right 2 : Int.log 2 (1 : ℝ) = 0)]
    exact Int.log_mono_right zero_lt_one h1
  have hfl := Real.floor_logb_natCast (b := 2) (r := M / m) (by linarith)
  rw [Nat.cast_ofNat] at hfl
  have hKle : (((Int.log 2 (M / m)).toNat : ℕ) : ℝ) ≤ Real.logb 2 (M / m) := by
    have e : (((Int.log 2 (M / m)).toNat : ℕ) : ℤ) = Int.log 2 (M / m) := Int.toNat_of_nonneg hl0
    have h2 : ((Int.log 2 (M / m) : ℤ) : ℝ) ≤ Real.logb 2 (M / m) := by
      rw [← hfl]; exact Int.floor_le _
    calc (((Int.log 2 (M / m)).toNat : ℕ) : ℝ) = ((((Int.log 2 (M / m)).toNat : ℕ) : ℤ) : ℝ) := by
          norm_cast
      _ = ((Int.log 2 (M / m) : ℤ) : ℝ) := by rw [e]
      _ ≤ Real.logb 2 (M / m) := h2
  gcongr

end LatticeProb
