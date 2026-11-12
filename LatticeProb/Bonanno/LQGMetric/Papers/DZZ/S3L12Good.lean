/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Good at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Geom

/-!
# DZZ Lemma 3.12, proof step "u and v are good" (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1430–1433 (proof of Lemma 3.12): applying
(eq-B-good) to the boxes `B` with `x ∈ B_large` shows that `x` is good. The deterministic part:

* `boxAt_mem_boxColl`: for `w ∈ 𝖢_large°` (in `𝕍`) and `k ≥ 1`, the level-`(n_𝖢 + k)` box containing `w`
  is in `𝓑(𝖢, 2^{-k})` (own elementary proof: `𝖢_large` is aligned with the grid of side `s_𝖢/2`);
* `cellSide_eq_of_isCell`: `s_{w,δ}` is the side of any cell containing `w` (cells are an antichain);
* **`isGoodPoint_of_boxColl`**: if every `B' ∈ 𝓑(𝖢, 2^{-k})` has `M(B') < δ²` for every cell `𝖢` with
  `x ∈ 𝖢_large`, then `x` is good for `ε = 2^{-k}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- One coordinate of `boxAt_mem_boxColl`. -/
lemma idx_cell_sub {n k j : ℕ} (hk : 1 ≤ k) (hj : j < 2 ^ n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : |x - (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n| < (2 : ℝ)⁻¹ ^ n) :
    (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ n ≤ (idx (n + k) x : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) ∧
      ((idx (n + k) x : ℝ) + 1) * (2 : ℝ)⁻¹ ^ (n + k) ≤
        (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  set h := (2 : ℝ)⁻¹ ^ (n + (K + 1)) with hh
  have hpos : 0 < h := by positivity
  have hs : (2 : ℝ)⁻¹ ^ n = 2 * 2 ^ K * h := by
    rw [hh, pow_add, pow_succ]
    field_simp
    rw [← mul_pow]; norm_num
  have hN : (2 : ℝ) ^ (n + (K + 1)) * h = 1 := by
    rw [hh, ← mul_pow]; norm_num
  rw [hs] at hx ⊢
  set y := x * 2 ^ (n + (K + 1)) with hy
  have hxy : x = y * h := by rw [hy, mul_assoc, hN, mul_one]
  rw [hxy] at hx
  have hy0 : 0 ≤ y := by positivity
  have hK : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  -- `a < y < b` with `a = (2j − 1) 2^K`, `b = (2j + 3) 2^K`
  have hab := abs_lt.mp hx
  have hlo : ((2 * j - 1) * 2 ^ K : ℝ) < y := by
    have := hab.1
    nlinarith
  have hhi : y < ((2 * j + 3) * 2 ^ K : ℝ) := by
    have := hab.2
    nlinarith
  set i := idx (n + (K + 1)) x with hi
  have hile : (i : ℝ) ≤ y := by
    have h1 : (i : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
    exact h1.trans (Nat.floor_le hy0)
  -- upper: `i + 1 ≤ b` (integers)
  have hup : (i : ℝ) + 1 ≤ (2 * j + 3) * 2 ^ K := by
    have hlt : (i : ℝ) < ((2 * j + 3) * 2 ^ K : ℕ) := by push_cast; linarith
    have : i + 1 ≤ (2 * j + 3) * 2 ^ K := by exact_mod_cast hlt
    exact_mod_cast this
  -- lower: `a ≤ i`
  have hdown : ((2 * j - 1) * 2 ^ K : ℝ) ≤ i := by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      push_cast; nlinarith
    · have ha : ((2 * j - 1) * 2 ^ K : ℝ) = (((2 * j - 1) * 2 ^ K : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * j)]; ring
      rw [ha]
      have h1 : (2 * j - 1) * 2 ^ K ≤ ⌊y⌋₊ := Nat.le_floor (by rw [← ha]; exact hlo.le)
      have h2 : (2 * j - 1) * 2 ^ K ≤ 2 ^ (n + (K + 1)) - 1 := by
        have e : 2 ^ (n + (K + 1)) = 2 ^ n * 2 ^ K * 2 := by rw [pow_add, pow_succ]; ring
        have hP : 1 ≤ 2 ^ K := Nat.one_le_two_pow
        have hA : j * 2 ^ K + 2 ^ K ≤ 2 ^ n * 2 ^ K := by
          have := Nat.mul_le_mul_right (2 ^ K) (show j + 1 ≤ 2 ^ n from hj)
          linarith [add_mul j 1 (2 ^ K)]
        have hx : (2 * j - 1) * 2 ^ K ≤ 2 * (j * 2 ^ K) := by
          calc (2 * j - 1) * 2 ^ K ≤ (2 * j) * 2 ^ K := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
            _ = 2 * (j * 2 ^ K) := by ring
        rw [e]
        generalize (2 * j - 1) * 2 ^ K = X at hx ⊢
        generalize j * 2 ^ K = A at hx hA
        generalize 2 ^ n * 2 ^ K = B at hA ⊢
        generalize 2 ^ K = P at hA hP
        omega
      exact_mod_cast le_min h1 h2
  constructor
  · nlinarith
  · nlinarith

/-- For `w ∈ 𝖢_large°` in `𝕍` and `k ≥ 1`, the level-`(n_𝖢 + k)` box containing `w` is in `𝓑(𝖢, 2^{-k})`. -/
lemma boxAt_mem_boxColl {C : DyBox} {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : w ∈ C.largeBoxOpen)
    (hwV : w ∈ dzzV) : boxAt (C.n + k) w ∈ boxColl C k := by
  refine ⟨rfl, ?_⟩
  obtain ⟨re1, re2⟩ := idx_cell_sub hk C.hj hwV.1 hw.1
  obtain ⟨im1, im2⟩ := idx_cell_sub hk C.hk hwV.2.2.1 hw.2
  intro z ⟨h1, h2, h3, h4⟩
  simp only [boxAt, DyBox.side] at h1 h2 h3 h4
  simp only [DyBox.largeBox, DyBox.center, DyBox.side, mem_ofPred_eq]
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

variable {m : DyBox → ℝ} {δ : ℝ}

/-- `s_{w,δ}` is the side of any cell containing `w`. -/
lemma cellSide_eq_of_isCell {c : DyBox} {w : ℂ} (hc : IsCell m δ c) (hw : c.Mem w) :
    cellSide m δ w = c.side := by
  have hex : ∃ b, IsCell m δ b ∧ b.Mem w := ⟨c, hc, hw⟩
  unfold cellSide
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hb, hbw⟩ := hex.choose_spec
  set b := hex.choose
  have key : b = c := by
    refine isCell_eq_of_anc m δ (d := boxAt (max b.n c.n) w) hb hc ?_ ?_
    · rw [anc_boxAt (le_max_left _ _), hbw.2]
    · rw [anc_boxAt (le_max_right _ _), hw.2]
  rw [key]

/-- A box of mass `< δ²` has an ancestor that is a cell (as `exists_isCell_anc`). -/
lemma exists_isCell_anc' {b : DyBox} (hb : m b < δ ^ 2) :
    ∃ i, i ≤ b.n ∧ IsCell m δ (b.anc i) := by
  classical
  have h0 : m (b.anc b.n) < δ ^ 2 := by rwa [anc_self le_rfl]
  have hP : ∃ i, m (b.anc i) < δ ^ 2 := ⟨b.n, h0⟩
  have hle : Nat.find hP ≤ b.n := Nat.find_min' hP h0
  refine ⟨Nat.find hP, hle, Nat.find_spec hP, fun i' hi' => ?_⟩
  have hn : (b.anc (Nat.find hP)).n = Nat.find hP := min_eq_left hle
  rw [hn] at hi'
  rw [anc_anc b hi'.le]
  exact not_lt.mp (Nat.find_min hP hi')

/-- **Goodness of a point from (eq-B-good)** (DZZ l. 1430–1433, deterministic part). -/
theorem isGoodPoint_of_boxColl {k : ℕ} (hk : 1 ≤ k) {x : ℂ}
    (h : ∀ C : DyBox, IsCell m δ C → x ∈ C.largeBox → ∀ b' ∈ boxColl C k, m b' < δ ^ 2) :
    IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) x := by
  intro C hC hx w hw hwV
  set B := boxAt (C.n + k) w
  have hB := boxAt_mem_boxColl hk hw hwV
  obtain ⟨i, hi, hci⟩ := exists_isCell_anc' (h C hC hx B hB)
  have hi' : i ≤ C.n + k := hi
  have e : B.anc i = boxAt i w := anc_boxAt hi' w
  rw [e] at hci
  have hmem : (boxAt i w).Mem w := ⟨hwV, rfl⟩
  rw [cellSide_eq_of_isCell hci hmem]
  simp only [DyBox.side, boxAt]
  rw [← pow_add]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

end DZZ
end LQGMetric
