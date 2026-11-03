/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSLemma27.Grid at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# The `(δ/4)ℤ²` grid of the union bound in [18] Lemma 2.8

[18]: "We obtain (2.10) by applying (2.11) with `δ/2` in place of `δ` then taking a union bound over all
`z ∈ (δ/4 ℤ²) ∩ B_ρ(0)`." We use the grid points `w ∈ (δ/4)ℤ²` with `|w| < ρ + δ/4` (`ballGrid δ ρ`): every
`z ∈ B_ρ(0)` is within `δ/4` of one of them (`exists_mem_ballGrid`, so `B_{δ/2}(w) ⊆ B_δ(z)`), and there are at most
`169 δ⁻²` of them for `δ ∈ (0, 1]`, `ρ ≤ 1` (`card_ballGrid_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace MatedCRTHarmonic.GMSLemma27

/-- The grid point `s(m + n i)`. -/
def ballGridPt (s : ℝ) (i : ℤ × ℤ) : ℂ := (s : ℂ) * ((i.1 : ℂ) + (i.2 : ℂ) * Complex.I)

theorem gridPt_re (s : ℝ) (i : ℤ × ℤ) : (ballGridPt s i).re = s * i.1 := by
  simp [ballGridPt]

theorem gridPt_im (s : ℝ) (i : ℤ × ℤ) : (ballGridPt s i).im = s * i.2 := by
  simp [ballGridPt]

/-- The half-width `⌈4ρ/δ⌉ + 1` of the index square. -/
def ballGridBound (δ ρ : ℝ) : ℤ := ⌈4 * ρ / δ⌉ + 1

/-- The grid points of `(δ/4)ℤ²` at distance `< ρ + δ/4` from `0`, as integer pairs. -/
def ballGrid (δ ρ : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-ballGridBound δ ρ) (ballGridBound δ ρ) ×ˢ Finset.Icc (-ballGridBound δ ρ) (ballGridBound δ ρ)).filter
    fun i => ‖ballGridPt (δ / 4) i‖ < ρ + δ / 4

/-- Every point of `B_ρ(0)` is within `δ/4` of a point of the grid. -/
theorem exists_mem_ballGrid {δ ρ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    ∃ i ∈ ballGrid δ ρ, ‖z - ballGridPt (δ / 4) i‖ ≤ δ / 4 := by
  rw [mem_ball_zero_iff] at hz
  set s : ℝ := δ / 4 with hs
  have hs0 : 0 < s := by positivity
  set i : ℤ × ℤ := (round (z.re / s), round (z.im / s)) with hi
  have hre : |z.re - s * i.1| ≤ s / 2 := by
    have h := abs_sub_round (z.re / s)
    have e : z.re - s * i.1 = s * (z.re / s - round (z.re / s)) := by
      simp only [hi]; field_simp
    rw [e, abs_mul, abs_of_pos hs0]
    nlinarith
  have him : |z.im - s * i.2| ≤ s / 2 := by
    have h := abs_sub_round (z.im / s)
    have e : z.im - s * i.2 = s * (z.im / s - round (z.im / s)) := by
      simp only [hi]; field_simp
    rw [e, abs_mul, abs_of_pos hs0]
    nlinarith
  have hdist : ‖z - ballGridPt s i‖ ≤ s := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, gridPt_re, gridPt_im]
    linarith
  -- the index bound: `|z.re| < ρ`, so `|i.1| ≤ ρ/s + 1/2 ≤ ⌈4ρ/δ⌉ + 1`
  have hρs : ρ / s = 4 * ρ / δ := by rw [hs]; field_simp
  have hcoord : ∀ (x : ℝ) (m : ℤ), |x| < ρ → |x - s * m| ≤ s / 2 →
      -ballGridBound δ ρ ≤ m ∧ m ≤ ballGridBound δ ρ := by
    intro x m hx hxm
    have h1 : |(m : ℝ)| ≤ ρ / s + 1 / 2 := by
      have h2 : |s * (m : ℝ)| ≤ |x| + s / 2 := by
        calc |s * (m : ℝ)| = |x - (x - s * m)| := by ring_nf
          _ ≤ |x| + |x - s * m| := abs_sub _ _
          _ ≤ |x| + s / 2 := by linarith
      rw [abs_mul, abs_of_pos hs0] at h2
      have : s * |(m : ℝ)| ≤ ρ + s / 2 := by linarith
      calc |(m : ℝ)| = (s * |(m : ℝ)|) / s := by field_simp
        _ ≤ (ρ + s / 2) / s := by gcongr
        _ = ρ / s + 1 / 2 := by field_simp
    have hceil : (4 * ρ / δ : ℝ) ≤ ⌈4 * ρ / δ⌉ := Int.le_ceil _
    rw [hρs] at h1
    have h3 : |(m : ℝ)| ≤ (ballGridBound δ ρ : ℝ) := by
      simp only [ballGridBound, Int.cast_add, Int.cast_one]
      linarith
    rw [abs_le] at h3
    exact ⟨by exact_mod_cast (by linarith [h3.1] : (-(ballGridBound δ ρ : ℝ)) ≤ m), by exact_mod_cast h3.2⟩
  have hzre : |z.re| < ρ := (Complex.abs_re_le_norm z).trans_lt hz
  have hzim : |z.im| < ρ := (Complex.abs_im_le_norm z).trans_lt hz
  refine ⟨i, ?_, hdist⟩
  simp only [ballGrid, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨hcoord z.re i.1 hzre hre, hcoord z.im i.2 hzim him⟩, ?_⟩
  calc ‖ballGridPt s i‖ = ‖z - (z - ballGridPt s i)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖z‖ + ‖z - ballGridPt s i‖ := norm_sub_le _ _
    _ < ρ + s := by linarith

/-- The grid has at most `169 δ⁻²` points for `δ ∈ (0, 1]` and `0 ≤ ρ ≤ 1`. -/
theorem card_ballGrid_le {δ ρ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ((ballGrid δ ρ).card : ℝ) ≤ 169 / δ ^ 2 := by
  set M := ballGridBound δ ρ with hM
  have hM0 : 0 ≤ M := by
    simp only [hM, ballGridBound]
    have : (0 : ℤ) ≤ ⌈4 * ρ / δ⌉ := Int.ceil_nonneg (by positivity)
    omega
  have hcardI : ((Finset.Icc (-M) M).card : ℝ) = 2 * M + 1 := by
    have h : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
      rw [Int.card_Icc]; omega
    exact_mod_cast h
  have hMle : (M : ℝ) ≤ 4 / δ + 2 := by
    have h1 : (⌈4 * ρ / δ⌉ : ℝ) < 4 * ρ / δ + 1 := Int.ceil_lt_add_one _
    have h2 : 4 * ρ / δ ≤ 4 / δ := by gcongr; linarith
    simp only [hM, ballGridBound, Int.cast_add, Int.cast_one]
    linarith
  have h1 : ((ballGrid δ ρ).card : ℝ) ≤ (2 * M + 1) ^ 2 := by
    have := Finset.card_filter_le
      (Finset.Icc (-M) M ×ˢ Finset.Icc (-M) M) (fun i => ‖ballGridPt (δ / 4) i‖ < ρ + δ / 4)
    rw [Finset.card_product] at this
    calc ((ballGrid δ ρ).card : ℝ) ≤ ((Finset.Icc (-M) M).card * (Finset.Icc (-M) M).card : ℕ) := by
          exact_mod_cast this
      _ = (2 * M + 1) ^ 2 := by push_cast; rw [hcardI]; ring
  have h2 : (2 * (M : ℝ) + 1) ≤ 13 / δ := by
    have : 5 ≤ 5 / δ := by rw [le_div_iff₀ hδ]; linarith
    have e : 13 / δ = 8 / δ + 5 / δ := by ring
    have e2 : 2 * (4 / δ + 2) + 1 = 8 / δ + 5 := by ring
    linarith
  have hpos : (0 : ℝ) ≤ 2 * M + 1 := by have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
                                        linarith
  calc ((ballGrid δ ρ).card : ℝ) ≤ (2 * M + 1) ^ 2 := h1
    _ ≤ (13 / δ) ^ 2 := pow_le_pow_left₀ hpos h2 2
    _ = 169 / δ ^ 2 := by ring

end MatedCRTHarmonic.GMSLemma27
