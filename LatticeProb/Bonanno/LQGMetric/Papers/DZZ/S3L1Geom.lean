/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L1Geom at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Defs
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# DZZ §3: deterministic facts about the dyadic partition (P2-DZZ3A, WP-113)

* `DyBox.anc_boxAt`: the level-`i` ancestor of the level-`n` box containing `v` is the level-`i`
  box containing `v` (`i ≤ n`).
* `exists_isCell_of_level`: if every box of level `k` has mass `< δ²`, every `v ∈ 𝕍` lies in a
  cell (the splitting procedure halts along `v`), and
* `IsCell.n_le_of_level`: every cell has level `≤ k`;
* `IsCell.lt_n_of_levels`: if every box of level `≤ K` has mass `≥ δ²`, every cell has level `> K`.
These are the deterministic halves of DZZ's proof of Lemma 3.1 (l. 833–848).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

namespace DyBox

lemma side_pos (b : DyBox) : 0 < b.side := by unfold side; positivity

lemma log_side (b : DyBox) : Real.log b.side = -(b.n * Real.log 2) := by
  rw [side, Real.log_pow, Real.log_inv]; ring

lemma two_pow_sub_one_div {i n : ℕ} (h : i ≤ n) : (2 ^ n - 1) / 2 ^ (n - i) = 2 ^ i - 1 := by
  have hd : 1 ≤ 2 ^ (n - i) := Nat.one_le_two_pow
  have ha : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have hn : 2 ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' h]
  set d := 2 ^ (n - i)
  set a := 2 ^ i
  rw [hn]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · rw [Nat.sub_mul, one_mul]
    exact Nat.sub_le_sub_left hd _
  · rw [Nat.sub_add_cancel ha]
    exact Nat.sub_lt (Nat.mul_pos (by omega) (by omega)) one_pos

lemma idx_div {i n : ℕ} (h : i ≤ n) (x : ℝ) : idx n x / 2 ^ (n - i) = idx i x := by
  have hF : ⌊x * 2 ^ n⌋₊ / 2 ^ (n - i) = ⌊x * 2 ^ i⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    have hn : (2 : ℝ) ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' h]
    push_cast
    rw [hn]
    field_simp
  unfold idx
  rcases le_total ⌊x * 2 ^ n⌋₊ (2 ^ n - 1) with h1 | h1
  · rw [min_eq_left h1, hF, min_eq_left]
    rw [← hF, ← two_pow_sub_one_div h]
    exact Nat.div_le_div_right h1
  · rw [min_eq_right h1, two_pow_sub_one_div h, min_eq_right]
    rw [← hF, ← two_pow_sub_one_div h]
    exact Nat.div_le_div_right h1

/-- The level-`i` ancestor of `boxAt n v` is `boxAt i v`. -/
theorem anc_boxAt {i n : ℕ} (h : i ≤ n) (v : ℂ) : (boxAt n v).anc i = boxAt i v := by
  ext
  · exact min_eq_left h
  · exact idx_div h v.re
  · exact idx_div h v.im

end DyBox

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- If every box of level `k` has mass `< δ²`, every point of `𝕍` lies in a cell. -/
theorem exists_isCell_of_level {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2) {v : ℂ}
    (hv : v ∈ dzzV) : ∃ b, IsCell m δ b ∧ b.Mem v := by
  classical
  have hex : ∃ n, m (boxAt n v) < δ ^ 2 := ⟨k, hk _ rfl⟩
  refine ⟨boxAt (Nat.find hex) v, ⟨Nat.find_spec hex, fun i hi => ?_⟩, hv, rfl⟩
  have hi' : i < Nat.find hex := hi
  rw [anc_boxAt hi'.le]
  exact not_lt.mp (Nat.find_min hex hi')

/-- If every box of level `k` has mass `< δ²`, every cell has level `≤ k`. -/
theorem IsCell.n_le_of_level {k : ℕ} (hk : ∀ b : DyBox, b.n = k → m b < δ ^ 2) {b : DyBox}
    (hb : IsCell m δ b) : b.n ≤ k := by
  by_contra h
  push Not at h
  have h1 := hb.2 k h
  have h2 := hk (b.anc k) (min_eq_left h.le)
  linarith

/-- If every box of level `≤ K` has mass `≥ δ²`, every cell has level `> K`. -/
theorem IsCell.lt_n_of_levels {K : ℕ} (hK : ∀ b : DyBox, b.n ≤ K → δ ^ 2 ≤ m b) {b : DyBox}
    (hb : IsCell m δ b) : K < b.n := by
  by_contra h
  push Not at h
  have := hK b h
  linarith [hb.1]

end DZZ
end LQGMetric
