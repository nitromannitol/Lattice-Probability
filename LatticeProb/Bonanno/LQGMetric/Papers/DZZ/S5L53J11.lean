/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J11 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J10

/-!
# DZZ Lemma 5.3, node 3: covering a side of a cell by boundary segments

DZZ l. 1901–1903 and (Eq.measure-of-Lambda-prime), l. 1946–1952: the boundary pieces `Λ_{i-1}`,
`Λ_i` of `𝖢_i` are covered by the segments `L ∈ 𝔹𝕊` of the sub-boxes up to a small error.
Here for the bottom side of `𝖢` and a grid-aligned piece
`Λ = l53BotSeg C k p q = {im = k_𝖢 s_𝖢, j_𝖢 s_𝖢 + p t ≤ re ≤ j_𝖢 s_𝖢 + q t}` (`t = s_𝖢/K`):
* `l53_seg_bot_eq`: the segment of the bottom boundary box in column `a` (`1 ≤ a ≤ K - 2`) is
  `l53BotSeg C k a (a+1)`;
* `l53_botSeg_cover`: `l53BotSeg C k a₀ a₁ ⊆ ⋃_{a₀ ≤ a < a₁} l53BotSeg C k a (a+1)`;
* `l53_botSeg_measure`: `μH¹(l53BotSeg C k u v) = (v - u) t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

/-- A piece of the bottom side of `𝖢`, in units `t = s_𝖢 / 2^k` from the corner. -/
def l53BotSeg (C : DyBox) (k : ℕ) (u v : ℝ) : Set ℂ :=
  {z | z.im = C.k * C.side ∧ C.j * C.side + u * (2 : ℝ)⁻¹ ^ (C.n + k) ≤ z.re ∧
    z.re ≤ C.j * C.side + v * (2 : ℝ)⁻¹ ^ (C.n + k)}

lemma l53_botSeg_measure (C : DyBox) (k : ℕ) (u v : ℝ) :
    μH[1] (l53BotSeg C k u v) = ENNReal.ofReal ((v - u) * (2 : ℝ)⁻¹ ^ (C.n + k)) := by
  rw [l53BotSeg, l53J_hline_eq]
  congr 1
  ring

/-- **The bottom segment of a non-corner bottom box.** -/
lemma l53_seg_bot_eq (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {a : ℤ} (ha₁ : 1 ≤ a)
    (ha₂ : a ≤ 2 * N) :
    (l53Sub C k N (a - N, -(N : ℤ))).closedBox ∩ frontier C.closedBox =
      l53BotSeg C k a (a + 1) := by
  have hz : ((a - N, -(N : ℤ)) : ℤ × ℤ) ∈ l53EvenBox N := mem_l53EvenBox.2 ⟨by omega, by omega,
    le_rfl, by omega⟩
  obtain ⟨hj, hk⟩ := l53_sub_jk C hK hz
  have hjR : ((l53Sub C k N (a - N, -(N : ℤ))).j : ℝ) = 2 ^ k * C.j + a := by
    have : ((l53Sub C k N (a - N, -(N : ℤ))).j : ℤ) = 2 ^ k * C.j + a := by rw [hj]; ring
    exact_mod_cast this
  have hkR : ((l53Sub C k N (a - N, -(N : ℤ))).k : ℝ) = 2 ^ k * C.k := by
    have : ((l53Sub C k N (a - N, -(N : ℤ))).k : ℤ) = 2 ^ k * C.k := by rw [hk]; ring
    exact_mod_cast this
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  have ha₁R : (1 : ℝ) ≤ a := by exact_mod_cast ha₁
  have ha₂R : (a : ℝ) ≤ 2 * N := by exact_mod_cast ha₂
  have ht := l53_side_mul_pow C k
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + k) with htdef
  have t0 : 0 < t := by positivity
  have hs : C.side = (2 * N + 2) * t := by rw [← ht, hKR]; ring
  have s0 := side_pos' C
  have hjC : (0 : ℝ) ≤ C.j := Nat.cast_nonneg _
  have hkC : (0 : ℝ) ≤ C.k := Nat.cast_nonneg _
  have hjj : (C.j : ℝ) * C.side ≤ (C.j + 1) * C.side := by nlinarith
  have hkk : (C.k : ℝ) * C.side ≤ (C.k + 1) * C.side := by nlinarith
  ext w
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hw⟩
    rw [l53_sub_side, hjR] at a1 a2
    rw [l53_sub_side, hkR] at a3 a4
    rw [closedBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
      frontier_Icc hjj, frontier_Icc hkk] at hw
    have e1 : C.j * C.side + a * t ≤ w.re := by rw [hs]; nlinarith
    have e2 : w.re ≤ C.j * C.side + (a + 1) * t := by rw [hs]; nlinarith
    refine ⟨?_, e1, e2⟩
    rcases hw with hw | hw <;> rw [Complex.mem_reProdIm] at hw
    · rcases hw.2 with h | h
      · exact h
      · exfalso; rw [h, hs] at a4; nlinarith
    · exfalso
      rcases hw.1 with h | h <;> rw [h, hs] at e1 e2 <;> nlinarith
  · rintro ⟨h1, h2, h3⟩
    have hwC : w ∈ C.closedBox := ⟨by nlinarith, by rw [hs] at h3 ⊢; nlinarith, by rw [h1],
      by rw [h1]; nlinarith⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mem_frontier_closedBox hwC (Or.inr (Or.inr (Or.inl h1)))⟩
    · rw [l53_sub_side, hjR]; rw [hs] at h2; nlinarith
    · rw [l53_sub_side, hjR]; rw [hs] at h3; nlinarith
    · rw [l53_sub_side, hkR, h1, hs]; nlinarith
    · rw [l53_sub_side, hkR, h1, hs]; nlinarith

/-- **Consecutive unit segments cover a grid-aligned piece.** -/
lemma l53_botSeg_cover (C : DyBox) (k : ℕ) {a₀ a₁ : ℤ} (h : a₀ < a₁) :
    l53BotSeg C k a₀ a₁ ⊆ ⋃ a ∈ Finset.Ico a₀ a₁, l53BotSeg C k a (a + 1) := by
  rintro w ⟨h1, h2, h3⟩
  simp only [mem_iUnion, Finset.mem_Ico]
  unfold l53BotSeg
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + k) with htdef
  have t0 : 0 < t := by positivity
  set x : ℝ := (w.re - C.j * C.side) / t with hx
  have hx1 : (a₀ : ℝ) ≤ x := by rw [hx, le_div_iff₀ t0]; linarith
  have hx2 : x ≤ a₁ := by rw [hx, div_le_iff₀ t0]; linarith
  set a : ℤ := min ⌊x⌋ (a₁ - 1) with ha
  have ha₀ : a₀ ≤ a := le_min (Int.le_floor.2 hx1) (by omega)
  have ha₁ : a < a₁ := lt_of_le_of_lt (min_le_right _ _) (by omega)
  have hal : (a : ℝ) ≤ x := (Int.cast_le.2 (min_le_left _ _)).trans (Int.floor_le x)
  have hau : x ≤ a + 1 := by
    rcases le_total ⌊x⌋ (a₁ - 1) with hm | hm
    · rw [ha, min_eq_left hm]; exact (Int.lt_floor_add_one x).le
    · rw [ha, min_eq_right hm]; push_cast; linarith
  refine ⟨a, ⟨ha₀, ha₁⟩, h1, ?_, ?_⟩
  · have := (le_div_iff₀ t0).1 (hx ▸ hal); linarith
  · have := (div_le_iff₀ t0).1 (hx ▸ hau); linarith

end LQGMetric.DZZ
