/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12Union at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Good

/-!
# DZZ Lemma 3.12: union bounds (P2-DZZ312)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1430–1434 (proof of Lemma 3.12): (eq-B-good) is
applied to the `O(log δ⁻¹)` boxes `B` with `x ∈ B_large` and `s_B ≥ δ^{C_mc}`, (eq-B-percolation) to all boxes.

* `measureReal_window_le`: at a fixed level, at most `9` boxes `B` have `x ∈ B_large` (own count);
* `measureReal_window_levels_le`, `measureReal_levels_le`: the sums over the levels `0, …, N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open DyBox

/-- The column of a box `B` of level `n` with `x ∈ B_large` is within `1` of `idx n x`. -/
lemma j_window {n j : ℕ} (hj : j < 2 ^ n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : |x - (j + 1 / 2) * (2 : ℝ)⁻¹ ^ n| ≤ (2 : ℝ)⁻¹ ^ n) :
    idx n x - 1 ≤ j ∧ j ≤ idx n x + 1 := by
  have hs : 0 < (2 : ℝ)⁻¹ ^ n := by positivity
  have hN : (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ n = 1 := by rw [← mul_pow]; norm_num
  set y := x * 2 ^ n with hy
  have hxy : x = y * (2 : ℝ)⁻¹ ^ n := by rw [hy, mul_assoc, hN, mul_one]
  rw [hxy] at hx
  have hab := abs_le.mp hx
  have hlo : (j : ℝ) - 1 / 2 ≤ y := by nlinarith
  have hhi : y ≤ (j : ℝ) + 3 / 2 := by nlinarith
  have hy0 : 0 ≤ y := by positivity
  have hfl := Nat.floor_le hy0
  have hfl2 := Nat.lt_floor_add_one y
  have hidx : idx n x = min ⌊y⌋₊ (2 ^ n - 1) := rfl
  rw [hidx]
  constructor
  · have : ⌊y⌋₊ ≤ j + 1 := by
      have : (⌊y⌋₊ : ℝ) < j + 2 := by linarith
      have : ⌊y⌋₊ < j + 2 := by exact_mod_cast this
      omega
    omega
  · rcases le_or_gt ⌊y⌋₊ (2 ^ n - 1) with h | h
    · rw [min_eq_left h]
      have : (j : ℝ) < ⌊y⌋₊ + 2 := by linarith
      have : j < ⌊y⌋₊ + 2 := by exact_mod_cast this
      omega
    · rw [min_eq_right h.le]
      omega

/-- At a fixed level, a union over the boxes `B` with `x ∈ B_large` costs at most `9` times the bound. -/
lemma measureReal_window_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (n : ℕ) {x : ℂ} (hx : x ∈ dzzV) (S : DyBox → Set Ω) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : DyBox, b.n = n → x ∈ b.largeBox → P.real (S b) ≤ B) :
    P.real {ω | ∃ b : DyBox, b.n = n ∧ x ∈ b.largeBox ∧ ω ∈ S b} ≤ 9 * B := by
  classical
  set a := idx n x.re
  set c := idx n x.im
  set T : Fin 3 → Fin 3 → Set Ω := fun d e =>
    {ω | ∃ b : DyBox, b.n = n ∧ b.j = a - 1 + d ∧ b.k = c - 1 + e ∧ x ∈ b.largeBox ∧ ω ∈ S b}
  have hsub : {ω | ∃ b : DyBox, b.n = n ∧ x ∈ b.largeBox ∧ ω ∈ S b} ⊆ ⋃ d, ⋃ e, T d e := by
    rintro ω ⟨b, hbn, hxb, hω⟩
    have hj := j_window (n := n) (hbn ▸ b.hj) hx.1 (by
      have := hxb.1; simpa [DyBox.center, DyBox.side, hbn] using this)
    have hk := j_window (n := n) (hbn ▸ b.hk) hx.2.2.1 (by
      have := hxb.2; simpa [DyBox.center, DyBox.side, hbn] using this)
    refine mem_iUnion.2 ⟨⟨b.j - (a - 1), by omega⟩, mem_iUnion.2 ⟨⟨b.k - (c - 1), by omega⟩,
      b, hbn, ?_, ?_, hxb, hω⟩⟩
    · simp only; omega
    · simp only; omega
  have hT : ∀ d e, P.real (T d e) ≤ B := by
    intro d e
    by_cases hne : (T d e).Nonempty
    · obtain ⟨ω₀, b₀, hb₀n, hb₀j, hb₀k, hxb₀, -⟩ := hne
      have : T d e ⊆ S b₀ := by
        rintro ω ⟨b, hbn, hbj, hbk, -, hω⟩
        have : b = b₀ := DyBox.ext (hbn.trans hb₀n.symm) (hbj.trans hb₀j.symm)
          (hbk.trans hb₀k.symm)
        rwa [← this]
      exact (measureReal_mono this).trans (hB b₀ hb₀n hxb₀)
    · rw [not_nonempty_iff_eq_empty.mp hne, measureReal_empty]; exact hB0
  refine (measureReal_mono hsub).trans ?_
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc ∑ d, P.real (⋃ e, T d e) ≤ ∑ _d : Fin 3, 3 * B := by
        refine Finset.sum_le_sum fun d _ => (measureReal_iUnion_fintype_le _).trans ?_
        calc ∑ e, P.real (T d e) ≤ ∑ _e : Fin 3, B := Finset.sum_le_sum fun e _ => hT d e
          _ = 3 * B := by simp
    _ = 9 * B := by simp; ring

/-- Window union over the levels `0, …, N`. -/
lemma measureReal_window_levels_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (N : ℕ) {x : ℂ} (hx : x ∈ dzzV) (S : DyBox → Set Ω) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : DyBox, b.n ≤ N → x ∈ b.largeBox → P.real (S b) ≤ B) :
    P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S b} ≤ 9 * (N + 1) * B := by
  have hsub : {ω | ∃ b : DyBox, b.n ≤ N ∧ x ∈ b.largeBox ∧ ω ∈ S b} ⊆
      ⋃ n ∈ Finset.range (N + 1), {ω | ∃ b : DyBox, b.n = n ∧ x ∈ b.largeBox ∧ ω ∈ S b} := by
    rintro ω ⟨b, hbn, hxb, hω⟩
    exact mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hbn)) ⟨b, rfl, hxb, hω⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ n ∈ Finset.range (N + 1), P.real {ω | ∃ b : DyBox, b.n = n ∧ x ∈ b.largeBox ∧ ω ∈ S b}
      ≤ ∑ _n ∈ Finset.range (N + 1), 9 * B := Finset.sum_le_sum fun n hn =>
        measureReal_window_le n hx S hB0 fun b hbn hxb =>
          hB b (by rw [hbn]; exact Nat.lt_succ_iff.mp (Finset.mem_range.1 hn)) hxb
    _ = 9 * (N + 1) * B := by simp; ring

/-- Union over all boxes of the levels `0, …, N`: at most `(N + 1) 4^N` boxes. -/
lemma measureReal_levels_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (N : ℕ) (S : DyBox → Set Ω) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ b : DyBox, b.n ≤ N → P.real (S b) ≤ B) :
    P.real {ω | ∃ b : DyBox, b.n ≤ N ∧ ω ∈ S b} ≤ (N + 1) * ((2 : ℝ) ^ N) ^ 2 * B := by
  have hsub : {ω | ∃ b : DyBox, b.n ≤ N ∧ ω ∈ S b} ⊆
      ⋃ n ∈ Finset.range (N + 1), {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ S b} := by
    rintro ω ⟨b, hbn, hω⟩
    exact mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hbn)) ⟨b, rfl, hω⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ n ∈ Finset.range (N + 1), P.real {ω | ∃ b : DyBox, b.n = n ∧ ω ∈ S b}
      ≤ ∑ _n ∈ Finset.range (N + 1), ((2 : ℝ) ^ N) ^ 2 * B := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.1 hn)
        refine (measureReal_level_le n S fun b hbn => hB b (hbn ▸ hnN)).trans ?_
        gcongr
        · norm_num
    _ = (N + 1) * ((2 : ℝ) ^ N) ^ 2 * B := by simp; ring

end DZZ
end LQGMetric
