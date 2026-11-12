/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J13 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J12

/-!
# DZZ Lemma 5.3, node 3: the left, top and right sides of a cell

The analogues of `l53_seg_bot_eq` (S5L53J11) for the other three sides of the cell `𝖢`
(boundary boxes of the even grid, S5L53J7: left column `(-N, a - N)`, top row `(a - N, N + 1)`,
right column `(N + 1, a - N)`), with the side pieces written as `l53LineSeg`
(`{L z = c, x₀ + u t ≤ M z ≤ x₀ + v t}` for the coordinate maps `L, M ∈ {re, im}`).
`l53_lineSeg_cover`, `l53_lineSeg_mono`, `l53_lineSeg_measure_v/h` are the hypotheses of
`l53_cover_side` (S5L53J12) for any side; **`l53_cover_lineSeg`** is `l53_cover_side` for
`l53LineSeg` pieces, and `l53_cellSeg_left/top/right` are its input `hseg` for the three sides
(the bottom side is `l53_cover_bot`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric DyBox

/-- An axis-parallel segment `{L z = c, x₀ + u t ≤ M z ≤ x₀ + v t}`. -/
def l53LineSeg (L M : ℂ → ℝ) (c x₀ t u v : ℝ) : Set ℂ :=
  {z | L z = c ∧ x₀ + u * t ≤ M z ∧ M z ≤ x₀ + v * t}

lemma l53_lineSeg_mono (L M : ℂ → ℝ) (c x₀ : ℝ) {t : ℝ} (t0 : 0 < t) {u v u' v' : ℝ}
    (hu : u' ≤ u) (hv : v ≤ v') : l53LineSeg L M c x₀ t u v ⊆ l53LineSeg L M c x₀ t u' v' := by
  rintro z ⟨h1, h2, h3⟩
  exact ⟨h1, by nlinarith, by nlinarith⟩

lemma l53_lineSeg_cover (L M : ℂ → ℝ) (c x₀ : ℝ) {t : ℝ} (t0 : 0 < t) {a₀ a₁ : ℤ}
    (h : a₀ < a₁) :
    l53LineSeg L M c x₀ t a₀ a₁ ⊆ ⋃ a ∈ Finset.Ico a₀ a₁, l53LineSeg L M c x₀ t a (a + 1) := by
  rintro w ⟨h1, h2, h3⟩
  simp only [mem_iUnion, Finset.mem_Ico]
  set x : ℝ := (M w - x₀) / t with hx
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

lemma l53_lineSeg_measure_v (c x₀ t u v : ℝ) :
    μH[1] (l53LineSeg Complex.re Complex.im c x₀ t u v) = ENNReal.ofReal ((v - u) * t) := by
  rw [show l53LineSeg Complex.re Complex.im c x₀ t u v =
    {z : ℂ | z.re = c ∧ x₀ + u * t ≤ z.im ∧ z.im ≤ x₀ + v * t} from rfl, l53J_vline_eq]
  congr 1; ring

lemma l53_lineSeg_measure_h (c x₀ t u v : ℝ) :
    μH[1] (l53LineSeg Complex.im Complex.re c x₀ t u v) = ENNReal.ofReal ((v - u) * t) := by
  rw [show l53LineSeg Complex.im Complex.re c x₀ t u v =
    {z : ℂ | z.im = c ∧ x₀ + u * t ≤ z.re ∧ z.re ≤ x₀ + v * t} from rfl, l53J_hline_eq]
  congr 1; ring

/-- The common setting of the three side lemmas. -/
lemma l53_side_setup (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) :
    C.side = (2 * N + 2) * (2 : ℝ)⁻¹ ^ (C.n + k) := by
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  rw [← l53_side_mul_pow C k, hKR]; ring

/-- **The left segment of a non-corner left box.** -/
lemma l53_seg_left_eq (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {a : ℤ} (ha₁ : 1 ≤ a)
    (ha₂ : a ≤ 2 * N) :
    (l53Sub C k N (-(N : ℤ), a - N)).closedBox ∩ frontier C.closedBox =
      l53LineSeg Complex.re Complex.im (C.j * C.side) (C.k * C.side) ((2 : ℝ)⁻¹ ^ (C.n + k))
        a (a + 1) := by
  have hz : ((-(N : ℤ), a - N) : ℤ × ℤ) ∈ l53EvenBox N := mem_l53EvenBox.2 ⟨le_rfl, by omega,
    by omega, by omega⟩
  obtain ⟨hj, hk⟩ := l53_sub_jk C hK hz
  have hjR : ((l53Sub C k N (-(N : ℤ), a - N)).j : ℝ) = 2 ^ k * C.j := by
    have : ((l53Sub C k N (-(N : ℤ), a - N)).j : ℤ) = 2 ^ k * C.j := by rw [hj]; ring
    exact_mod_cast this
  have hkR : ((l53Sub C k N (-(N : ℤ), a - N)).k : ℝ) = 2 ^ k * C.k + a := by
    have : ((l53Sub C k N (-(N : ℤ), a - N)).k : ℤ) = 2 ^ k * C.k + a := by rw [hk]; ring
    exact_mod_cast this
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  rw [hKR] at hjR hkR
  have ha₁R : (1 : ℝ) ≤ a := by exact_mod_cast ha₁
  have ha₂R : (a : ℝ) ≤ 2 * N := by exact_mod_cast ha₂
  have hs := l53_side_setup C hK
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + k) with htdef
  have t0 : 0 < t := by positivity
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
    have e1 : C.k * C.side + a * t ≤ w.im := by rw [hs]; nlinarith
    have e2 : w.im ≤ C.k * C.side + (a + 1) * t := by rw [hs]; nlinarith
    refine ⟨?_, e1, e2⟩
    rcases hw with hw | hw <;> rw [Complex.mem_reProdIm] at hw
    · exfalso
      rcases hw.2 with h | h <;> rw [h, hs] at e1 e2 <;> nlinarith
    · rcases hw.1 with h | h
      · exact h
      · exfalso; rw [h, hs] at a2; nlinarith
  · rintro ⟨h1, h2, h3⟩
    have h1' : w.re = C.j * C.side := h1
    have hwC : w ∈ C.closedBox := ⟨by rw [h1'], by rw [h1']; nlinarith, by nlinarith,
      by rw [hs] at h3 ⊢; nlinarith⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mem_frontier_closedBox hwC (Or.inl h1')⟩
    · rw [l53_sub_side, hjR, h1', hs]; nlinarith
    · rw [l53_sub_side, hjR, h1', hs]; nlinarith
    · rw [l53_sub_side, hkR]; rw [hs] at h2; nlinarith
    · rw [l53_sub_side, hkR]; rw [hs] at h3; nlinarith

/-- **The top segment of a non-corner top box.** -/
lemma l53_seg_top_eq (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {a : ℤ} (ha₁ : 1 ≤ a)
    (ha₂ : a ≤ 2 * N) :
    (l53Sub C k N (a - N, (N : ℤ) + 1)).closedBox ∩ frontier C.closedBox =
      l53LineSeg Complex.im Complex.re ((C.k + 1) * C.side) (C.j * C.side)
        ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1) := by
  have hz : ((a - N, (N : ℤ) + 1) : ℤ × ℤ) ∈ l53EvenBox N := mem_l53EvenBox.2 ⟨by omega,
    by omega, by omega, le_rfl⟩
  obtain ⟨hj, hk⟩ := l53_sub_jk C hK hz
  set B := l53Sub C k N (a - N, (N : ℤ) + 1) with hB
  have hjR : (B.j : ℝ) = 2 ^ k * C.j + a := by
    have : (B.j : ℤ) = 2 ^ k * C.j + a := by rw [hj]; ring
    exact_mod_cast this
  have hkR : (B.k : ℝ) = 2 ^ k * C.k + (2 * N + 1) := by
    have : (B.k : ℤ) = 2 ^ k * C.k + (2 * N + 1) := by rw [hk]; ring
    exact_mod_cast this
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  have ha₁R : (1 : ℝ) ≤ a := by exact_mod_cast ha₁
  have ha₂R : (a : ℝ) ≤ 2 * N := by exact_mod_cast ha₂
  have hs := l53_side_setup C hK
  have hBs : B.side = (2 : ℝ)⁻¹ ^ (C.n + k) := l53_sub_side C k N _
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + k) with htdef
  have t0 : 0 < t := by positivity
  have hjt : (B.j : ℝ) * t = C.j * C.side + a * t := by rw [hjR, hs, hKR]; ring
  have hkt : (B.k : ℝ) * t = (C.k + 1) * C.side - t := by rw [hkR, hs, hKR]; ring
  have hat1 : t ≤ a * t := by nlinarith
  have hat2 : (a + 1) * t ≤ C.side - t := by rw [hs]; nlinarith
  have s0 := side_pos' C
  have hjj : (C.j : ℝ) * C.side ≤ (C.j + 1) * C.side := by nlinarith
  have hkk : (C.k : ℝ) * C.side ≤ (C.k + 1) * C.side := by nlinarith
  ext w
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hw⟩
    rw [hBs] at a1 a2 a3 a4
    rw [closedBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
      frontier_Icc hjj, frontier_Icc hkk] at hw
    have e1 : C.j * C.side + a * t ≤ w.re := by linarith
    have e2 : w.re ≤ C.j * C.side + (a + 1) * t := by linarith
    refine ⟨?_, e1, e2⟩
    rcases hw with hw | hw <;> rw [Complex.mem_reProdIm] at hw
    · rcases hw.2 with h | h
      · exfalso; rw [h] at a3; linarith
      · exact h
    · exfalso
      rcases hw.1 with h | h <;> rw [h] at e1 e2 <;> linarith
  · rintro ⟨h1, h2, h3⟩
    have h1' : w.im = (C.k + 1) * C.side := h1
    have hwC : w ∈ C.closedBox := ⟨by linarith, by linarith, by rw [h1']; linarith,
      by rw [h1']⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mem_frontier_closedBox hwC (Or.inr (Or.inr (Or.inr h1')))⟩ <;>
      rw [hBs]
    · linarith
    · linarith
    · rw [h1']; linarith
    · rw [h1']; linarith

/-- **The right segment of a non-corner right box.** -/
lemma l53_seg_right_eq (C : DyBox) {k N : ℕ} (hK : 2 ^ k = 2 * N + 2) {a : ℤ} (ha₁ : 1 ≤ a)
    (ha₂ : a ≤ 2 * N) :
    (l53Sub C k N ((N : ℤ) + 1, a - N)).closedBox ∩ frontier C.closedBox =
      l53LineSeg Complex.re Complex.im ((C.j + 1) * C.side) (C.k * C.side)
        ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1) := by
  have hz : (((N : ℤ) + 1, a - N) : ℤ × ℤ) ∈ l53EvenBox N := mem_l53EvenBox.2 ⟨by omega,
    le_rfl, by omega, by omega⟩
  obtain ⟨hj, hk⟩ := l53_sub_jk C hK hz
  set B := l53Sub C k N ((N : ℤ) + 1, a - N) with hB
  have hjR : (B.j : ℝ) = 2 ^ k * C.j + (2 * N + 1) := by
    have : (B.j : ℤ) = 2 ^ k * C.j + (2 * N + 1) := by rw [hj]; ring
    exact_mod_cast this
  have hkR : (B.k : ℝ) = 2 ^ k * C.k + a := by
    have : (B.k : ℤ) = 2 ^ k * C.k + a := by rw [hk]; ring
    exact_mod_cast this
  have hKR : (2 : ℝ) ^ k = 2 * N + 2 := by exact_mod_cast hK
  have ha₁R : (1 : ℝ) ≤ a := by exact_mod_cast ha₁
  have ha₂R : (a : ℝ) ≤ 2 * N := by exact_mod_cast ha₂
  have hs := l53_side_setup C hK
  have hBs : B.side = (2 : ℝ)⁻¹ ^ (C.n + k) := l53_sub_side C k N _
  set t : ℝ := (2 : ℝ)⁻¹ ^ (C.n + k) with htdef
  have t0 : 0 < t := by positivity
  have hjt : (B.j : ℝ) * t = (C.j + 1) * C.side - t := by rw [hjR, hs, hKR]; ring
  have hkt : (B.k : ℝ) * t = C.k * C.side + a * t := by rw [hkR, hs, hKR]; ring
  have hat1 : t ≤ a * t := by nlinarith
  have hat2 : (a + 1) * t ≤ C.side - t := by rw [hs]; nlinarith
  have s0 := side_pos' C
  have hjj : (C.j : ℝ) * C.side ≤ (C.j + 1) * C.side := by nlinarith
  have hkk : (C.k : ℝ) * C.side ≤ (C.k + 1) * C.side := by nlinarith
  ext w
  constructor
  · rintro ⟨⟨a1, a2, a3, a4⟩, hw⟩
    rw [hBs] at a1 a2 a3 a4
    rw [closedBox_eq_reProdIm, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
      frontier_Icc hjj, frontier_Icc hkk] at hw
    have e1 : C.k * C.side + a * t ≤ w.im := by linarith
    have e2 : w.im ≤ C.k * C.side + (a + 1) * t := by linarith
    refine ⟨?_, e1, e2⟩
    rcases hw with hw | hw <;> rw [Complex.mem_reProdIm] at hw
    · exfalso
      rcases hw.2 with h | h <;> rw [h] at e1 e2 <;> linarith
    · rcases hw.1 with h | h
      · exfalso; rw [h] at a1; linarith
      · exact h
  · rintro ⟨h1, h2, h3⟩
    have h1' : w.re = (C.j + 1) * C.side := h1
    have hwC : w ∈ C.closedBox := ⟨by rw [h1']; linarith, by rw [h1'], by linarith,
      by linarith⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, mem_frontier_closedBox hwC (Or.inr (Or.inl h1'))⟩ <;>
      rw [hBs]
    · rw [h1']; linarith
    · rw [h1']; linarith
    · linarith
    · linarith

/-- `l53_cover_side` for a side whose pieces are `l53LineSeg L M c x₀ t`. -/
theorem l53_cover_lineSeg (C : DyBox) {k n N : ℕ} (hnN : n ≤ N) (L M : ℂ → ℝ) (c x₀ : ℝ)
    (hmeas : ∀ u v, μH[1] (l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k)) u v) =
      ENNReal.ofReal ((v - u) * (2 : ℝ)⁻¹ ^ (C.n + k)))
    (d : PercDir) (hseg : ∀ a : ℤ, (N : ℤ) - n < a → a < N + n →
      l53CellSeg C k n N (d, a) = l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1))
    {p q : ℤ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2 * N + 2) :
    (∀ x ∈ l53SidePrev d n N p q,
      l53CellSeg C k n N x ⊆ l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k)) p q ∧
      (N : ℤ) - n < x.2 ∧ x.2 < N + n) ∧
    (μH[1] : Measure ℂ).real (l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k)) p q) ≤
        (μH[1] : Measure ℂ).real (⋃ x ∈ l53SidePrev d n N p q, l53CellSeg C k n N x) +
          (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + k) ∧
      (μH[1] : Measure ℂ).real (l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k)) p q \
          ⋃ x ∈ l53SidePrev d n N p q, l53CellSeg C k n N x) ≤
        (2 * ((N : ℝ) - n) + 3) * (2 : ℝ)⁻¹ ^ (C.n + k) := by
  have t0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (C.n + k) := by positivity
  refine l53_cover_side (l53LineSeg L M c x₀ ((2 : ℝ)⁻¹ ^ (C.n + k))) t0 (fun u v huv => ?_)
    (fun u v => ?_) (fun a₀ a₁ h => l53_lineSeg_cover L M c x₀ t0 h)
    (fun u v u' v' hu hv => l53_lineSeg_mono L M c x₀ t0 hu hv)
    (l53CellSeg C k n N) (measurableSet_l53CellSeg C k n N) d hnN hseg hp hpq hq
  · rw [Measure.real, hmeas, ENNReal.toReal_ofReal (by nlinarith)]
  · rw [hmeas]; exact ENNReal.ofReal_ne_top

/-- The segment of the left boundary box at a non-corner position (input `hseg` of
`l53_cover_lineSeg` with `L = re`, `M = im`, `c = j_𝖢 s_𝖢`, `x₀ = k_𝖢 s_𝖢`, `d = L`). -/
lemma l53_cellSeg_left (C : DyBox) {k n N : ℕ} (hK : 2 ^ k = 2 * N + 2) (hnN : n ≤ N) {a : ℤ}
    (ha₁ : (N : ℤ) - n < a) (ha₂ : a < N + n) :
    l53CellSeg C k n N (PercDir.L, a) = l53LineSeg Complex.re Complex.im (C.j * C.side)
      (C.k * C.side) ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1) := by
  rw [l53CellSeg, (l53_even_site n N a).2.2.1]
  exact l53_seg_left_eq C hK (by omega) (by omega)

/-- The segment of the top boundary box at a non-corner position (`L = im`, `M = re`,
`c = (k_𝖢 + 1) s_𝖢`, `x₀ = j_𝖢 s_𝖢`, `d = T`). -/
lemma l53_cellSeg_top (C : DyBox) {k n N : ℕ} (hK : 2 ^ k = 2 * N + 2) (hnN : n ≤ N) {a : ℤ}
    (ha₁ : (N : ℤ) - n < a) (ha₂ : a < N + n) :
    l53CellSeg C k n N (PercDir.T, a) = l53LineSeg Complex.im Complex.re ((C.k + 1) * C.side)
      (C.j * C.side) ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1) := by
  rw [l53CellSeg, (l53_even_site n N a).2.1]
  exact l53_seg_top_eq C hK (by omega) (by omega)

/-- The segment of the right boundary box at a non-corner position (`L = re`, `M = im`,
`c = (j_𝖢 + 1) s_𝖢`, `x₀ = k_𝖢 s_𝖢`, `d = R`). -/
lemma l53_cellSeg_right (C : DyBox) {k n N : ℕ} (hK : 2 ^ k = 2 * N + 2) (hnN : n ≤ N) {a : ℤ}
    (ha₁ : (N : ℤ) - n < a) (ha₂ : a < N + n) :
    l53CellSeg C k n N (PercDir.R, a) = l53LineSeg Complex.re Complex.im ((C.j + 1) * C.side)
      (C.k * C.side) ((2 : ℝ)⁻¹ ^ (C.n + k)) a (a + 1) := by
  rw [l53CellSeg, (l53_even_site n N a).2.2.2]
  exact l53_seg_right_eq C hK (by omega) (by omega)

end LQGMetric.DZZ
