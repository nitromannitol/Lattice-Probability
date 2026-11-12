import Mathlib

/-!
# Half-open squares of side `r` covering the disc of radius `1/2`

For `r > 0` the half-open squares `[a r, (a+1) r) × [b r, (b+1) r)`, `(a, b) ∈ ℤ × ℤ`, form a
partition of the plane. We record the finite family of those meeting the closed disc of radius
`1/2` (`squareIndex`) together with the facts used to split an integral over the disc into
pieces:

* the squares are measurable, pairwise disjoint and cover the disc, and their number is at most
  `16 / r²` when `r ≤ 1`;
* every square lies in the open ball of radius `r` around its centre, and the centre of a square
  meeting the disc has norm `< 1/2 + r`;
* two distinct squares whose indices have the same parity in both coordinates are at distance
  `≥ r`; there are four parity classes (`squareClass`);
* an integral against a measure of a function vanishing off the disc is the sum of the integrals
  over the squares of the family.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- The half-open square of side `r` with lower left corner `(i.1 r, i.2 r)`. -/
noncomputable def dyadicSquare (r : ℝ) (i : ℤ × ℤ) : Set ℂ :=
  (Complex.re ⁻¹' Ico ((i.1 : ℝ) * r) (((i.1 : ℝ) + 1) * r)) ∩
    (Complex.im ⁻¹' Ico ((i.2 : ℝ) * r) (((i.2 : ℝ) + 1) * r))

/-- The centre of `dyadicSquare r i`. -/
noncomputable def dyadicSquareCentre (r : ℝ) (i : ℤ × ℤ) : ℂ :=
  ⟨((i.1 : ℝ) + 1 / 2) * r, ((i.2 : ℝ) + 1 / 2) * r⟩

theorem mem_dyadicSquare {r : ℝ} {i : ℤ × ℤ} {x : ℂ} :
    x ∈ dyadicSquare r i ↔ ((i.1 : ℝ) * r ≤ x.re ∧ x.re < ((i.1 : ℝ) + 1) * r) ∧
      ((i.2 : ℝ) * r ≤ x.im ∧ x.im < ((i.2 : ℝ) + 1) * r) := by
  simp [dyadicSquare, Set.mem_Ico]

theorem measurableSet_dyadicSquare (r : ℝ) (i : ℤ × ℤ) : MeasurableSet (dyadicSquare r i) :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)

theorem mem_dyadicSquare_iff_floor {r : ℝ} (hr : 0 < r) {i : ℤ × ℤ} {x : ℂ} :
    x ∈ dyadicSquare r i ↔ ⌊x.re / r⌋ = i.1 ∧ ⌊x.im / r⌋ = i.2 := by
  simp only [mem_dyadicSquare, Int.floor_eq_iff, le_div_iff₀ hr, div_lt_iff₀ hr]

theorem exists_mem_dyadicSquare {r : ℝ} (hr : 0 < r) (x : ℂ) :
    x ∈ dyadicSquare r (⌊x.re / r⌋, ⌊x.im / r⌋) := by
  rw [mem_dyadicSquare_iff_floor hr]
  simp

theorem disjoint_dyadicSquare {r : ℝ} (hr : 0 < r) {i j : ℤ × ℤ} (hij : i ≠ j) :
    Disjoint (dyadicSquare r i) (dyadicSquare r j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [mem_dyadicSquare_iff_floor hr] at hxi hxj
  exact hij (Prod.ext (hxi.1.symm.trans hxj.1) (hxi.2.symm.trans hxj.2))

/-- A square of side `r` lies in the open ball of radius `r` around its centre. -/
theorem norm_sub_centre_lt {r : ℝ} (hr : 0 < r) {i : ℤ × ℤ} {x : ℂ}
    (hx : x ∈ dyadicSquare r i) : ‖x - dyadicSquareCentre r i‖ < r := by
  rw [mem_dyadicSquare] at hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  have hre : (x - dyadicSquareCentre r i).re ^ 2 ≤ (r / 2) ^ 2 := by
    simp only [dyadicSquareCentre, Complex.sub_re]
    apply sq_le_sq' <;> nlinarith
  have him : (x - dyadicSquareCentre r i).im ^ 2 ≤ (r / 2) ^ 2 := by
    simp only [dyadicSquareCentre, Complex.sub_im]
    apply sq_le_sq' <;> nlinarith
  have hsq : ‖x - dyadicSquareCentre r i‖ ^ 2 < r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [hre, him, sq_pos_of_pos hr]
  by_contra h
  have h' := pow_le_pow_left₀ hr.le (not_lt.1 h) 2
  linarith

theorem dyadicSquare_subset_ball {r : ℝ} (hr : 0 < r) (i : ℤ × ℤ) :
    dyadicSquare r i ⊆ ball (dyadicSquareCentre r i) r := fun _ hx => by
  rw [mem_ball_iff_norm]
  exact norm_sub_centre_lt hr hx

/-- The squares of side `r` meeting the closed disc of radius `1/2`. -/
noncomputable def squareIndex (r : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact ((Finset.Icc (-(⌈1 / (2 * r)⌉₊ : ℤ)) (⌈1 / (2 * r)⌉₊ : ℤ)) ×ˢ
    (Finset.Icc (-(⌈1 / (2 * r)⌉₊ : ℤ)) (⌈1 / (2 * r)⌉₊ : ℤ))).filter
    (fun i => (dyadicSquare r i ∩ closedBall (0 : ℂ) (1 / 2)).Nonempty)

private theorem floor_div_bounds {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    -(⌈1 / (2 * r)⌉₊ : ℤ) ≤ ⌊t / r⌋ ∧ ⌊t / r⌋ ≤ (⌈1 / (2 * r)⌉₊ : ℤ) := by
  have hM : 1 / (2 * r) ≤ (⌈1 / (2 * r)⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : |t / r| ≤ 1 / (2 * r) := by
    rw [abs_div, abs_of_pos hr, div_le_div_iff₀ hr (by positivity)]
    have := mul_le_mul_of_nonneg_right ht hr.le
    nlinarith
  rw [abs_le] at h1
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [h1.1]
  · exact_mod_cast (Int.floor_le (t / r)).trans (h1.2.trans hM)

theorem mem_squareIndex {r : ℝ} (hr : 0 < r) {i : ℤ × ℤ} :
    i ∈ squareIndex r ↔ (dyadicSquare r i ∩ closedBall (0 : ℂ) (1 / 2)).Nonempty := by
  classical
  unfold squareIndex
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨x, hx, hxb⟩ := h
    have hxb' : ‖x‖ ≤ 1 / 2 := by simpa using hxb
    have hre := floor_div_bounds hr ((Complex.abs_re_le_norm x).trans hxb')
    have him := floor_div_bounds hr ((Complex.abs_im_le_norm x).trans hxb')
    rw [mem_dyadicSquare_iff_floor hr] at hx
    rw [← hx.1, ← hx.2]
    exact ⟨hre, him⟩

theorem closedBall_subset_iUnion_dyadicSquare {r : ℝ} (hr : 0 < r) :
    closedBall (0 : ℂ) (1 / 2) ⊆ ⋃ i ∈ squareIndex r, dyadicSquare r i := by
  intro x hx
  simp only [Set.mem_iUnion]
  exact ⟨(⌊x.re / r⌋, ⌊x.im / r⌋),
    (mem_squareIndex hr).2 ⟨x, exists_mem_dyadicSquare hr x, hx⟩, exists_mem_dyadicSquare hr x⟩

/-- The centre of a square of the family has norm `< 1/2 + r`. -/
theorem norm_dyadicSquareCentre_lt {r : ℝ} (hr : 0 < r) {i : ℤ × ℤ} (hi : i ∈ squareIndex r) :
    ‖dyadicSquareCentre r i‖ < 1 / 2 + r := by
  obtain ⟨x, hx, hxb⟩ := (mem_squareIndex hr).1 hi
  have hxb' : ‖x‖ ≤ 1 / 2 := by simpa using hxb
  have h1 := norm_sub_centre_lt hr hx
  calc ‖dyadicSquareCentre r i‖ = ‖x - (x - dyadicSquareCentre r i)‖ := by congr 1; ring
    _ ≤ ‖x‖ + ‖x - dyadicSquareCentre r i‖ := norm_sub_le _ _
    _ < 1 / 2 + r := by linarith

/-- The number of squares of side `r ≤ 1` meeting the disc is at most `16 / r²`. -/
theorem card_squareIndex_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ((squareIndex r).card : ℝ) ≤ 16 / r ^ 2 := by
  classical
  set M := ⌈1 / (2 * r)⌉₊ with hM
  have hIcc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  have hcard : (squareIndex r).card ≤ (2 * M + 1) * (2 * M + 1) := by
    unfold squareIndex
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, hIcc]
  have hM1 : (M : ℝ) < 1 / (2 * r) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h4 : ((2 * M + 1 : ℕ) : ℝ) ≤ 4 / r := by
    push_cast
    have h3 : (3 : ℝ) ≤ 3 / r := by
      rw [le_div_iff₀ hr]
      nlinarith
    have e : 4 / r = 1 / r + 3 / r := by ring
    have e2 : 2 * (1 / (2 * r)) = 1 / r := by field_simp
    linarith
  calc ((squareIndex r).card : ℝ) ≤ (((2 * M + 1) * (2 * M + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((2 * M + 1 : ℕ) : ℝ) * ((2 * M + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 4 / r * (4 / r) := mul_le_mul h4 h4 (by positivity) (by positivity)
    _ = 16 / r ^ 2 := by field_simp; ring

/-- The parity class of a square: the parities of its two integer coordinates. -/
def squareClass (i : ℤ × ℤ) : ZMod 2 × ZMod 2 := ((i.1 : ZMod 2), (i.2 : ZMod 2))

private theorem sep_one {r : ℝ} (hr : 0 < r) {a b : ℤ} (hab : a + 2 ≤ b) {u v : ℝ}
    (hu : (a : ℝ) * r ≤ u ∧ u < ((a : ℝ) + 1) * r)
    (hv : (b : ℝ) * r ≤ v ∧ v < ((b : ℝ) + 1) * r) : r ≤ v - u := by
  have h : (a : ℝ) + 2 ≤ b := by exact_mod_cast hab
  have := mul_le_mul_of_nonneg_right h hr.le
  nlinarith [hu.2, hv.1]

private theorem sep_abs {r : ℝ} (hr : 0 < r) {a b : ℤ} (hne : a ≠ b) (hd : (2 : ℤ) ∣ b - a)
    {u v : ℝ} (hu : (a : ℝ) * r ≤ u ∧ u < ((a : ℝ) + 1) * r)
    (hv : (b : ℝ) * r ≤ v ∧ v < ((b : ℝ) + 1) * r) : r ≤ |u - v| := by
  rcases (show a + 2 ≤ b ∨ b + 2 ≤ a by omega) with h | h
  · rw [abs_sub_comm]
    exact (sep_one hr h hu hv).trans (le_abs_self _)
  · exact (sep_one hr h hv hu).trans (le_abs_self _)

/-- Two distinct squares of the same parity class are at distance `≥ r`. -/
theorem le_norm_sub_of_squareClass_eq {r : ℝ} (hr : 0 < r) {i j : ℤ × ℤ} (hij : i ≠ j)
    (hc : squareClass i = squareClass j) {x y : ℂ} (hx : x ∈ dyadicSquare r i)
    (hy : y ∈ dyadicSquare r j) : r ≤ ‖x - y‖ := by
  obtain ⟨hc1, hc2⟩ := Prod.mk.inj hc
  have d1 : (2 : ℤ) ∣ j.1 - i.1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub i.1 j.1 2).1 hc1
    exact_mod_cast this
  have d2 : (2 : ℤ) ∣ j.2 - i.2 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub i.2 j.2 2).1 hc2
    exact_mod_cast this
  rw [mem_dyadicSquare] at hx hy
  by_cases h1 : i.1 = j.1
  · have h2 : i.2 ≠ j.2 := fun h2 => hij (Prod.ext h1 h2)
    have := sep_abs hr h2 d2 hx.2 hy.2
    exact this.trans (by simpa using Complex.abs_im_le_norm (x - y))
  · have := sep_abs hr h1 d1 hx.1 hy.1
    exact this.trans (by simpa using Complex.abs_re_le_norm (x - y))

/-- **Splitting an integral over the squares.** If `f` vanishes off the closed disc of radius
`1/2`, its integral is the sum of its integrals over the squares meeting the disc. -/
theorem lintegral_eq_sum_dyadicSquare {r : ℝ} (hr : 0 < r) (μ : Measure ℂ) {f : ℂ → ℝ≥0∞}
    (hf0 : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0) :
    ∫⁻ x, f x ∂μ = ∑ i ∈ squareIndex r, ∫⁻ x in dyadicSquare r i, f x ∂μ := by
  rw [← lintegral_biUnion_finset (fun i _ j _ hij => disjoint_dyadicSquare hr hij)
    (fun i _ => measurableSet_dyadicSquare r i) f]
  refine (setLIntegral_eq_of_support_subset ?_).symm
  intro x hx
  refine closedBall_subset_iUnion_dyadicSquare hr ?_
  by_contra hxb
  exact hx (hf0 x hxb)

end LatticeProb
