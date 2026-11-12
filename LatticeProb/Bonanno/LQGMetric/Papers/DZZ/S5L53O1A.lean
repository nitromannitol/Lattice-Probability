/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53O1A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J13
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53NN1

/-!
# DZZ Lemma 5.3, node 3: chain interfaces are grid-aligned side pieces (P2-DZZ53O1)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2393 (`Λ_i = 𝖢̄_i ∩ 𝖢̄_{i+1}`) and
l. 2425–2430 (`𝖢_i` is partitioned into `K²` dyadic squares of side `s_i/K`), used at
l. 1946–1952 (the pieces `Λ_{i-1}`, `Λ_i` are covered by the boundary segments of the sub-boxes).
Open item (O1) of handoff P2-DZZ53J.

* `l53SidePiece C κ d p q`: the grid-aligned piece `S p q` of side `d` of `𝖢` (the bottom piece
  `l53BotSeg`, S5L53J11, and the `l53LineSeg` pieces of `l53_cellSeg_left/top/right`, S5L53J13),
  in units `t = s_𝖢 / 2^κ`.
* `l53O1_grid`: one-dimensional dyadic arithmetic (endpoints of `[a s, (a+1) s] ∩ [a' s', (a'+1) s']`
  are integer multiples of `t` when `t ≤ s'`).
* **`l53_iface_eq_sidePiece`**: two neighbouring non-nested dyadic boxes with `s_𝖢/2^κ ≤ s_𝖢'`
  meet in a grid-aligned piece `l53SidePiece 𝖢 κ d p q`, `0 ≤ p ≤ q ≤ 2^κ = 2N + 2`. The case
  analysis follows `l53_iface_ge_aux` (S5L53M1) and the nesting step `dy_nested_real`.
* **`l53_cover_sidePiece`**: `l53_cover_bot` / `l53_cover_lineSeg` dispatched over the side `d`.
* **`l53_l313_iface_sidePiece`**: for an `L313Q` sequence with `2^{-κ} ≤ ε²` (side ratio
  `l53_side_ratio`, non-nesting `l53_l313_nonnest`), `l53Iface l (i+1)` is a grid-aligned piece
  of a side of both `l_i` and `l_{i+1}`.

Own elementary proofs (dyadic arithmetic; copies of the case analysis of S5L53M1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- The grid-aligned piece `S p q` of side `d` of `𝖢` (units `t = s_𝖢 / 2^κ` from the
bottom-left corner), as consumed by `l53_cover_bot` and `l53_cover_lineSeg`. -/
def l53SidePiece (C : DyBox) (κ : ℕ) (d : PercDir) (p q : ℝ) : Set ℂ :=
  match d with
  | .B => l53BotSeg C κ p q
  | .L => l53LineSeg Complex.re Complex.im (C.j * C.side) (C.k * C.side) ((2 : ℝ)⁻¹ ^ (C.n + κ)) p q
  | .T => l53LineSeg Complex.im Complex.re ((C.k + 1) * C.side) (C.j * C.side)
      ((2 : ℝ)⁻¹ ^ (C.n + κ)) p q
  | .R => l53LineSeg Complex.re Complex.im ((C.j + 1) * C.side) (C.k * C.side)
      ((2 : ℝ)⁻¹ ^ (C.n + κ)) p q

/-- One-dimensional dyadic arithmetic: the endpoints of the intersection of two dyadic
intervals are on the grid `t ℤ`, `t = 2^{-(n+κ)} ≤ 2^{-n'}`. -/
lemma l53O1_grid {n n' a a' κ : ℕ} (h : n' ≤ n + κ)
    (hle : max ((a : ℝ) * (2 : ℝ)⁻¹ ^ n) (a' * (2 : ℝ)⁻¹ ^ n') ≤
      min ((a + 1) * (2 : ℝ)⁻¹ ^ n) ((a' + 1) * (2 : ℝ)⁻¹ ^ n')) :
    ∃ p q : ℤ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 ^ κ ∧
      (a : ℝ) * (2 : ℝ)⁻¹ ^ n + p * (2 : ℝ)⁻¹ ^ (n + κ) =
        max ((a : ℝ) * (2 : ℝ)⁻¹ ^ n) (a' * (2 : ℝ)⁻¹ ^ n') ∧
      (a : ℝ) * (2 : ℝ)⁻¹ ^ n + q * (2 : ℝ)⁻¹ ^ (n + κ) =
        min ((a + 1) * (2 : ℝ)⁻¹ ^ n) ((a' + 1) * (2 : ℝ)⁻¹ ^ n') := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h
  set t : ℝ := (2 : ℝ)⁻¹ ^ (n + κ) with ht
  have t0 : 0 < t := by positivity
  have hs : (2 : ℝ)⁻¹ ^ n = 2 ^ κ * t := by
    rw [ht, pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ κ), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, mul_one]
  have hs' : (2 : ℝ)⁻¹ ^ n' = 2 ^ e * t := by
    rw [ht, he, pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ e), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, mul_one]
  set A : ℤ := a * 2 ^ κ with hA
  set B : ℤ := a' * 2 ^ e with hB
  have e1 : (a : ℝ) * (2 : ℝ)⁻¹ ^ n = (A : ℝ) * t := by rw [hs, hA]; push_cast; ring
  have e2 : (a' : ℝ) * (2 : ℝ)⁻¹ ^ n' = (B : ℝ) * t := by rw [hs', hB]; push_cast; ring
  have e3 : ((a : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n = ((A + 2 ^ κ : ℤ) : ℝ) * t := by
    rw [hs, hA]; push_cast; ring
  have e4 : ((a' : ℝ) + 1) * (2 : ℝ)⁻¹ ^ n' = ((B + 2 ^ e : ℤ) : ℝ) * t := by
    rw [hs', hB]; push_cast; ring
  rw [e1, e2, e3, e4, ← max_mul_of_nonneg _ _ t0.le, ← min_mul_of_nonneg _ _ t0.le] at hle ⊢
  have hle' : max A B ≤ min (A + 2 ^ κ) (B + 2 ^ e) := by
    have := le_of_mul_le_mul_right hle t0
    exact_mod_cast this
  refine ⟨max A B - A, min (A + 2 ^ κ) (B + 2 ^ e) - A, by omega, by omega, by omega, ?_, ?_⟩
  · push_cast; ring
  · push_cast; ring

/-- **(O1): the interface of two neighbouring non-nested dyadic boxes is a grid-aligned piece
of one side of the first**, when `s_𝖢 / 2^κ ≤ s_𝖢'` (DZZ l. 2393, 2425–2430). -/
theorem l53_iface_eq_sidePiece {C C' : DyBox} {κ N : ℕ} (hK : 2 ^ κ = 2 * N + 2)
    (hn1 : C.closedBox ⊆ C'.closedBox → C = C') (hn2 : C'.closedBox ⊆ C.closedBox → C' = C)
    (hN : Neighbour C C') (ht : (2 : ℝ)⁻¹ ^ (C.n + κ) ≤ C'.side) :
    ∃ (d : PercDir) (p q : ℤ), 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 * N + 2 ∧
      C.closedBox ∩ C'.closedBox = l53SidePiece C κ d p q := by
  obtain ⟨hne, hns⟩ := hN
  simp only [Set.Subsingleton, not_forall] at hns
  obtain ⟨z, ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩, -⟩ := hns
  have hs := side_pos' C
  have hs' := side_pos' C'
  have hnn : C'.n ≤ C.n + κ :=
    (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).1 ht
  have hKR : ((2 : ℤ) ^ κ) = 2 * N + 2 := by exact_mod_cast hK
  -- the strict overlap in both coordinates forces nesting
  have hnot : ¬ (((C.j : ℝ) * C.side < (C'.j + 1) * C'.side ∧
      (C'.j : ℝ) * C'.side < (C.j + 1) * C.side) ∧
      ((C.k : ℝ) * C.side < (C'.k + 1) * C'.side ∧
      (C'.k : ℝ) * C'.side < (C.k + 1) * C.side)) := by
    rintro ⟨⟨hj1, hj2⟩, ⟨hk1, hk2⟩⟩
    rcases le_total C'.n C.n with hle | hle
    · have u := dy_nested_real (n := C.n) (n' := C'.n) hle hj1 hj2
      have v := dy_nested_real (n := C.n) (n' := C'.n) hle hk1 hk2
      have hsub : C.closedBox ⊆ C'.closedBox := by
        rintro q ⟨q1, q2, q3, q4⟩
        exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
      exact hne (hn1 hsub)
    · have u := dy_nested_real (n := C'.n) (n' := C.n) hle hj2 hj1
      have v := dy_nested_real (n := C'.n) (n' := C.n) hle hk2 hk1
      have hsub : C'.closedBox ⊆ C.closedBox := by
        rintro q ⟨q1, q2, q3, q4⟩
        exact ⟨u.1.trans q1, q2.trans u.2, v.1.trans q3, q4.trans v.2⟩
      exact hne (hn2 hsub).symm
  -- the grid endpoints in both coordinates
  obtain ⟨px, qx, hpx0, hpqx, hqx, hpx, hqx'⟩ : ∃ p q : ℤ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 ^ κ ∧
      (C.j : ℝ) * C.side + p * (2 : ℝ)⁻¹ ^ (C.n + κ) = max ((C.j : ℝ) * C.side) (C'.j * C'.side) ∧
      (C.j : ℝ) * C.side + q * (2 : ℝ)⁻¹ ^ (C.n + κ) =
        min ((C.j + 1) * C.side) ((C'.j + 1) * C'.side) :=
    l53O1_grid hnn (max_le (le_min (a1.trans a2) (a1.trans b2)) (le_min (b1.trans a2)
      (b1.trans b2)))
  obtain ⟨py, qy, hpy0, hpqy, hqy, hpy, hqy'⟩ : ∃ p q : ℤ, 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 ^ κ ∧
      (C.k : ℝ) * C.side + p * (2 : ℝ)⁻¹ ^ (C.n + κ) = max ((C.k : ℝ) * C.side) (C'.k * C'.side) ∧
      (C.k : ℝ) * C.side + q * (2 : ℝ)⁻¹ ^ (C.n + κ) =
        min ((C.k + 1) * C.side) ((C'.k + 1) * C'.side) :=
    l53O1_grid hnn (max_le (le_min (a3.trans a4) (a3.trans b4)) (le_min (b3.trans a4)
      (b3.trans b4)))
  by_cases hx : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side ∧
      (C'.j : ℝ) * C'.side < (C.j + 1) * C.side
  · by_cases hk1 : (C.k : ℝ) * C.side < (C'.k + 1) * C'.side
    · -- top side: `k_𝖢' s' = (k_𝖢 + 1) s`
      have hk2 : ¬ (C'.k : ℝ) * C'.side < (C.k + 1) * C.side := fun h => hnot ⟨hx, hk1, h⟩
      have hyeq : (C'.k : ℝ) * C'.side = (C.k + 1) * C.side := by push Not at hk2; linarith
      refine ⟨.T, px, qx, hpx0, hpqx, by omega, ?_⟩
      ext w
      simp only [l53SidePiece, l53LineSeg, mem_inter_iff, DyBox.closedBox, mem_ofPred_eq]
      rw [hpx, hqx', max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩
        exact ⟨by linarith, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
      · rintro ⟨h1, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
        refine ⟨⟨c1, c2, ?_, ?_⟩, ⟨d1, d2, ?_, ?_⟩⟩ <;> linarith
    · -- bottom side: `(k_𝖢' + 1) s' = k_𝖢 s`
      have hyeq : (C.k : ℝ) * C.side = (C'.k + 1) * C'.side := by push Not at hk1; linarith
      refine ⟨.B, px, qx, hpx0, hpqx, by omega, ?_⟩
      ext w
      simp only [l53SidePiece, l53BotSeg, mem_inter_iff, DyBox.closedBox, mem_ofPred_eq]
      rw [hpx, hqx', max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩
        exact ⟨by linarith, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
      · rintro ⟨h1, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
        refine ⟨⟨c1, c2, ?_, ?_⟩, ⟨d1, d2, ?_, ?_⟩⟩ <;> linarith
  · by_cases hj1 : (C.j : ℝ) * C.side < (C'.j + 1) * C'.side
    · -- right side: `j_𝖢' s' = (j_𝖢 + 1) s`
      have hj2 : ¬ (C'.j : ℝ) * C'.side < (C.j + 1) * C.side := fun h => hx ⟨hj1, h⟩
      have hxeq : (C'.j : ℝ) * C'.side = (C.j + 1) * C.side := by push Not at hj2; linarith
      refine ⟨.R, py, qy, hpy0, hpqy, by omega, ?_⟩
      ext w
      simp only [l53SidePiece, l53LineSeg, mem_inter_iff, DyBox.closedBox, mem_ofPred_eq]
      rw [hpy, hqy', max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩
        exact ⟨by linarith, ⟨c3, d3⟩, ⟨c4, d4⟩⟩
      · rintro ⟨h1, ⟨c3, d3⟩, ⟨c4, d4⟩⟩
        refine ⟨⟨?_, ?_, c3, c4⟩, ⟨?_, ?_, d3, d4⟩⟩ <;> linarith
    · -- left side: `(j_𝖢' + 1) s' = j_𝖢 s`
      have hxeq : (C.j : ℝ) * C.side = (C'.j + 1) * C'.side := by push Not at hj1; linarith
      refine ⟨.L, py, qy, hpy0, hpqy, by omega, ?_⟩
      ext w
      simp only [l53SidePiece, l53LineSeg, mem_inter_iff, DyBox.closedBox, mem_ofPred_eq]
      rw [hpy, hqy', max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3, d4⟩⟩
        exact ⟨by linarith, ⟨c3, d3⟩, ⟨c4, d4⟩⟩
      · rintro ⟨h1, ⟨c3, d3⟩, ⟨c4, d4⟩⟩
        refine ⟨⟨?_, ?_, c3, c4⟩, ⟨?_, ?_, d3, d4⟩⟩ <;> linarith

/-- **Coverage of a grid-aligned side piece by its boundary segments**, any side
(`l53_cover_bot`, S5L53J12, and `l53_cover_lineSeg` with `l53_cellSeg_left/top/right`, S5L53J13). -/
theorem l53_cover_sidePiece (C : DyBox) {κ n N : ℕ} (hK : 2 ^ κ = 2 * N + 2) (hnN : n ≤ N)
    (d : PercDir) {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2 * N + 2) :
    (∀ x ∈ l53SidePrev d n N p q, l53CellSeg C κ n N x ⊆ l53SidePiece C κ d p q ∧
      (N : ℤ) - n < x.2 ∧ x.2 < N + n) ∧
    (μH[1] : Measure ℂ).real (l53SidePiece C κ d p q) ≤
        (μH[1] : Measure ℂ).real (⋃ x ∈ l53SidePrev d n N p q, l53CellSeg C κ n N x) +
          (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + κ) ∧
      (μH[1] : Measure ℂ).real
          (l53SidePiece C κ d p q \ ⋃ x ∈ l53SidePrev d n N p q, l53CellSeg C κ n N x) ≤
        (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + κ) := by
  cases d
  · exact l53_cover_lineSeg C hnN Complex.im Complex.re _ _
      (fun u v => l53_lineSeg_measure_h _ _ _ u v) .T
      (fun a h1 h2 => l53_cellSeg_top C hK hnN h1 h2) hp hpq hq
  · exact l53_cover_bot C hK hnN hp hpq hq
  · exact l53_cover_lineSeg C hnN Complex.re Complex.im _ _
      (fun u v => l53_lineSeg_measure_v _ _ _ u v) .R
      (fun a h1 h2 => l53_cellSeg_right C hK hnN h1 h2) hp hpq hq
  · exact l53_cover_lineSeg C hnN Complex.re Complex.im _ _
      (fun u v => l53_lineSeg_measure_v _ _ _ u v) .L
      (fun a h1 h2 => l53_cellSeg_left C hK hnN h1 h2) hp hpq hq

section chain

variable {m : DyBox → ℝ} {δ ε : ℝ} {u v : ℂ} {l : List DyBox}

/-- **(O1) on an `L313Q` sequence**: if `2^{-κ} ≤ ε²` (so `s_i / 2^κ ≤ s_{i±1}` by the side ratio),
the interface `Λ_{i+1} = 𝖢̄_i ∩ 𝖢̄_{i+1}` is a grid-aligned piece of a side of `𝖢_i` (the `Next`
interface of `𝖢_i`) and of a side of `𝖢_{i+1}` (its `Prev` interface). -/
theorem l53_l313_iface_sidePiece (hQ : L313Q ε u v (fun b => IsCell m δ b) l) {κ N : ℕ}
    (hK : 2 ^ κ = 2 * N + 2) (hε : (2 : ℝ)⁻¹ ^ κ ≤ ε ^ 2) (i : ℕ) (hi : i + 1 < l.length) :
    (∃ (d : PercDir) (p q : ℤ), 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 * N + 2 ∧
      l53Iface l (i + 1) = l53SidePiece (l.getD i root) κ d p q) ∧
    (∃ (d : PercDir) (p q : ℤ), 0 ≤ p ∧ p ≤ q ∧ q ≤ 2 * N + 2 ∧
      l53Iface l (i + 1) = l53SidePiece (l.getD (i + 1) root) κ d p q) := by
  obtain ⟨n1, n2⟩ := l53_l313_nonnest hQ i hi
  obtain ⟨r1, r2⟩ := l53_side_ratio hQ i hi
  have hN : Neighbour (l.getD i root) (l.getD (i + 1) root) := by
    rw [l53NN_getD_eq l (by omega), l53NN_getD_eq l hi]
    exact hQ.1.2.getElem i hi
  have e : l53Iface l (i + 1) = (l.getD i root).closedBox ∩ (l.getD (i + 1) root).closedBox := by
    simp [l53Iface]
  have ht : ∀ b : DyBox, (2 : ℝ)⁻¹ ^ (b.n + κ) ≤ ε ^ 2 * b.side := fun b => by
    rw [pow_add, mul_comm]; exact mul_le_mul_of_nonneg_right hε (side_pos' b).le
  rw [e]
  refine ⟨l53_iface_eq_sidePiece hK n1 n2 hN ((ht _).trans r1), ?_⟩
  rw [inter_comm]
  exact l53_iface_eq_sidePiece hK n2 n1 hN.symm ((ht _).trans r2)

end chain

end DZZ
end LQGMetric
