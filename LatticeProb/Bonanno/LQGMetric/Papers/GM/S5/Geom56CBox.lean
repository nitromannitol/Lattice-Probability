/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CLay
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.SepMeas56

/-!
# GM Lemma 5.6: grid corridors and finite square sets (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6 (l. 2963–2968),
with the axis-parallel corridor of decision D69 (decisions/DEC-SEP.md §3).

* `iUnion_box_eq`: the squares with indices in `[a₁, a₂) × [b₁, b₂)` tile the closed box
  `[a₁ s, a₂ s] × [b₁ s, b₂ s]`;
* `exists_corridor`: for every point `u` and axis `e ∈ {1, −1, i, −i}` there is a corridor
  `rectC c e (50 s) (2 s)` tiled by grid squares with `u` near its `+e` end
  (`ξ ∈ [48.5 s, 49.5 s]`, `|η| ≤ s/2`, `(ξ, η)` the coordinates of `u − c` along `e`, `ie`);
* `sqF`: the finite set of squares meeting `X ⊆ cl B_{2r}(z)`, `↑(sqF …) = 𝓢_s(X)`.
Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma exists_Ico_coord {s x : ℝ} (hs : 0 < s) {a₁ a₂ : ℤ} (h1 : (a₁ : ℝ) * s ≤ x)
    (h2 : x ≤ (a₂ : ℝ) * s) (h12 : a₁ < a₂) :
    ∃ i ∈ Finset.Ico a₁ a₂, (i : ℝ) * s ≤ x ∧ x ≤ ((i : ℝ) + 1) * s := by
  have hf1 : (⌊x / s⌋ : ℝ) ≤ x / s := Int.floor_le _
  have hf2 : x / s < ⌊x / s⌋ + 1 := Int.lt_floor_add_one _
  have hxs1 : (a₁ : ℝ) ≤ x / s := by rw [le_div_iff₀ hs]; exact h1
  have hxs2 : x / s ≤ a₂ := by rw [div_le_iff₀ hs]; exact h2
  by_cases hc : ⌊x / s⌋ ≤ a₂ - 1
  · refine ⟨⌊x / s⌋, Finset.mem_Ico.2 ⟨Int.le_floor.2 hxs1, by omega⟩, ?_, ?_⟩
    · rw [← le_div_iff₀ hs]; exact hf1
    · rw [← div_le_iff₀ hs]; exact hf2.le
  · rw [not_le] at hc
    have : (a₂ : ℝ) ≤ ⌊x / s⌋ := by exact_mod_cast (show a₂ ≤ ⌊x / s⌋ by omega)
    have hx : x = a₂ * s := by
      have : (a₂ : ℝ) ≤ x / s := this.trans hf1
      rw [le_div_iff₀ hs] at this; linarith
    refine ⟨a₂ - 1, Finset.mem_Ico.2 ⟨by omega, by omega⟩, ?_, ?_⟩ <;> push_cast <;> nlinarith

/-- the squares with indices in a box tile the closed box -/
lemma iUnion_box_eq {s : ℝ} (hs : 0 < s) {a₁ a₂ b₁ b₂ : ℤ} (ha : a₁ < a₂) (hb : b₁ < b₂) :
    ⋃ m ∈ Finset.Ico a₁ a₂ ×ˢ Finset.Ico b₁ b₂, gridSquare s m =
      {w : ℂ | (a₁ : ℝ) * s ≤ w.re ∧ w.re ≤ a₂ * s ∧ (b₁ : ℝ) * s ≤ w.im ∧ w.im ≤ b₂ * s} := by
  ext w
  simp only [mem_iUnion, exists_prop, Finset.mem_product, mem_ofPred_eq]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, w1, w2, w3, w4⟩
    rw [Finset.mem_Ico] at hm1 hm2
    have e1 : (a₁ : ℝ) ≤ m.1 := by exact_mod_cast hm1.1
    have e2 : (m.1 : ℝ) + 1 ≤ a₂ := by exact_mod_cast hm1.2
    have e3 : (b₁ : ℝ) ≤ m.2 := by exact_mod_cast hm2.1
    have e4 : (m.2 : ℝ) + 1 ≤ b₂ := by exact_mod_cast hm2.2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨w1, w2, w3, w4⟩
    obtain ⟨i, hi, hi1, hi2⟩ := exists_Ico_coord hs w1 w2 ha
    obtain ⟨j, hj, hj1, hj2⟩ := exists_Ico_coord hs w3 w4 hb
    exact ⟨(i, j), ⟨hi, hj⟩, hi1, hi2, hj1, hj2⟩

lemma round_bounds (x : ℝ) : |x - round x| ≤ 1 / 2 := abs_sub_round x

/-- **grid corridors**; see the module docstring -/
theorem exists_corridor {s : ℝ} (hs : 0 < s) (u e : ℂ) (he : e = 1 ∨ e = -1 ∨ e = Complex.I ∨
    e = -Complex.I) :
    ∃ (c : ℂ) (Fc : Finset (ℤ × ℤ)), ⋃ m ∈ Fc, gridSquare s m = rectC c e (50 * s) (2 * s) ∧
      48.5 * s ≤ ((u - c) * (starRingEnd ℂ) e).re ∧ ((u - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s ∧
      |((u - c) * (starRingEnd ℂ) e).im| ≤ s / 2 := by
  set p := round (u.re / s)
  set q := round (u.im / s)
  have hp := round_bounds (u.re / s)
  have hq := round_bounds (u.im / s)
  rw [abs_le] at hp hq
  have hpr : u.re - p * s ∈ Icc (-(s / 2)) (s / 2) := by
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hp.1 hs.le,
      mul_le_mul_of_nonneg_right hp.2 hs.le, div_mul_cancel₀ u.re hs.ne']
  have hqr : u.im - q * s ∈ Icc (-(s / 2)) (s / 2) := by
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hq.1 hs.le,
      mul_le_mul_of_nonneg_right hq.2 hs.le, div_mul_cancel₀ u.im hs.ne']
  -- the box `{|Re (w - c)| ≤ A, |Im (w - c)| ≤ B}` for `c` on the grid
  have box : ∀ (i j : ℤ) (k l : ℕ), 0 < k → 0 < l →
      ⋃ m ∈ Finset.Ico (i - k) (i + k) ×ˢ Finset.Ico (j - l) (j + l), gridSquare s m =
        {w : ℂ | |w.re - i * s| ≤ k * s ∧ |w.im - j * s| ≤ l * s} := by
    intro i j k l hk hl
    rw [iUnion_box_eq hs (by omega) (by omega)]
    ext w
    simp only [mem_ofPred_eq, abs_le]
    push_cast
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  rcases he with rfl | rfl | rfl | rfl
  · refine ⟨⟨((p - 49 : ℤ) : ℝ) * s, (q : ℝ) * s⟩, _, (box (p - 49) q 50 2 (by norm_num) (by norm_num)).trans ?_, ?_⟩
    · ext w; simp [rectC]
    · simp only [map_one, mul_one, Complex.sub_re, Complex.sub_im]
      push_cast
      refine ⟨by linarith [hpr.1], by linarith [hpr.2], abs_le.2 ⟨by linarith [hqr.1], by linarith [hqr.2]⟩⟩
  · refine ⟨⟨((p + 49 : ℤ) : ℝ) * s, (q : ℝ) * s⟩, _, (box (p + 49) q 50 2 (by norm_num) (by norm_num)).trans ?_, ?_⟩
    · ext w; simp only [rectC, mem_ofPred_eq, map_neg, map_one, mul_neg, mul_one, Complex.neg_re,
        Complex.neg_im, abs_neg, Complex.sub_re, Complex.sub_im, Nat.cast_ofNat, neg_sub, abs_sub_comm]
    · simp only [map_neg, map_one, mul_neg, mul_one, Complex.neg_re, Complex.neg_im, abs_neg,
        Complex.sub_re, Complex.sub_im]
      push_cast
      refine ⟨by linarith [hpr.2], by linarith [hpr.1], abs_le.2 ⟨by linarith [hqr.1], by linarith [hqr.2]⟩⟩
  · refine ⟨⟨(p : ℝ) * s, ((q - 49 : ℤ) : ℝ) * s⟩, _, (box p (q - 49) 2 50 (by norm_num) (by norm_num)).trans ?_, ?_⟩
    · ext w; simp only [rectC, mem_ofPred_eq, Complex.conj_I, Complex.mul_re, Complex.mul_im,
        Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.sub_re,
        Complex.sub_im]
      constructor
      · rintro ⟨h1, h2⟩; constructor
        · first | simpa using h2 | (rw [abs_sub_comm]; simpa using h2) | simpa [abs_sub_comm] using h2
        · first | simpa using h1 | (rw [abs_sub_comm]; simpa using h1) | simpa [abs_sub_comm] using h1
      · rintro ⟨h1, h2⟩; constructor
        · first | simpa using h2 | (rw [abs_sub_comm]; simpa using h2) | simpa [abs_sub_comm] using h2
        · first | simpa using h1 | (rw [abs_sub_comm]; simpa using h1) | simpa [abs_sub_comm] using h1
    · simp only [Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      push_cast
      refine ⟨by linarith [hqr.1], by linarith [hqr.2], ?_⟩
      rw [abs_le]; constructor <;> linarith [hpr.1, hpr.2]
  · refine ⟨⟨(p : ℝ) * s, ((q + 49 : ℤ) : ℝ) * s⟩, _, (box p (q + 49) 2 50 (by norm_num) (by norm_num)).trans ?_, ?_⟩
    · ext w; simp only [rectC, mem_ofPred_eq, map_neg, Complex.conj_I, neg_neg, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      constructor
      · rintro ⟨h1, h2⟩; constructor
        · first | simpa using h2 | (rw [abs_sub_comm]; simpa using h2) | simpa [abs_sub_comm] using h2
        · first | simpa using h1 | (rw [abs_sub_comm]; simpa using h1) | simpa [abs_sub_comm] using h1
      · rintro ⟨h1, h2⟩; constructor
        · first | simpa using h2 | (rw [abs_sub_comm]; simpa using h2) | simpa [abs_sub_comm] using h2
        · first | simpa using h1 | (rw [abs_sub_comm]; simpa using h1) | simpa [abs_sub_comm] using h1
    · simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.sub_re, Complex.sub_im]
      push_cast
      refine ⟨by linarith [hqr.2], by linarith [hqr.1], ?_⟩
      rw [abs_le]; constructor <;> linarith [hpr.1, hpr.2]

/-- an axis within `45°` of a unit vector -/
lemma exists_axis {ω : ℂ} (hω : ‖ω‖ = 1) : ∃ e : ℂ, (e = 1 ∨ e = -1 ∨ e = Complex.I ∨
    e = -Complex.I) ∧ 7 / 10 ≤ (ω * (starRingEnd ℂ) e).re := by
  have h1 : ω.re ^ 2 + ω.im ^ 2 = 1 := by
    have := Complex.sq_norm ω
    rw [hω, Complex.normSq_apply] at this; nlinarith
  rcases le_total (ω.im ^ 2) (ω.re ^ 2) with h | h
  · have hx : 7 / 10 ≤ |ω.re| := by
      by_contra hc; rw [not_le] at hc
      have : ω.re ^ 2 < (7 / 10) ^ 2 := by rw [← sq_abs]; exact pow_lt_pow_left₀ hc (abs_nonneg _) (by norm_num)
      nlinarith
    rcases le_or_gt 0 ω.re with h0 | h0
    · exact ⟨1, Or.inl rfl, by simpa [abs_of_nonneg h0] using hx⟩
    · exact ⟨-1, Or.inr (Or.inl rfl), by simpa [abs_of_neg h0] using hx⟩
  · have hy : 7 / 10 ≤ |ω.im| := by
      by_contra hc; rw [not_le] at hc
      have : ω.im ^ 2 < (7 / 10) ^ 2 := by rw [← sq_abs]; exact pow_lt_pow_left₀ hc (abs_nonneg _) (by norm_num)
      nlinarith
    rcases le_or_gt 0 ω.im with h0 | h0
    · exact ⟨Complex.I, Or.inr (Or.inr (Or.inl rfl)), by simpa [abs_of_nonneg h0] using hy⟩
    · exact ⟨-Complex.I, Or.inr (Or.inr (Or.inr rfl)), by simpa [abs_of_neg h0] using hy⟩

/-- the finite set of squares meeting `X` (inside the index box of `B_{3r}(z)`) -/
def sqF (s r : ℝ) (z : ℂ) (X : Set ℂ) : Finset (ℤ × ℤ) := by
  classical exact (sqBox s (3 * r) z).filter (· ∈ squareSet s X)

lemma coe_sqF {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {z : ℂ} {X : Set ℂ}
    (hX : X ⊆ closedBall z (2 * r)) : (↑(sqF s r z X) : Set (ℤ × ℤ)) = squareSet s X := by
  ext m
  simp only [sqF, Finset.coe_filter, mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨squareSet_closedBall_subset_box hs hr z (squareSet_mono s hX h), h⟩

end LQGMetric.GM
