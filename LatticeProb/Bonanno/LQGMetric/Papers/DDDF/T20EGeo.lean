/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20EGeo at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EPw

/-!
# DDDF Theorem 20, Step 4: the box around a visited block (task P2-DDDFT20e)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1097–1101 (`P^K`, the blocks within `C K^{ε₀} 2^{-K}`
of `P`) and l. 1103–1105. For a block `b` and a point `x ∈ [0,1]²` within `2s` of it, with
`2 s 2^K ≤ m`: the box `[b₁ − m, b₁ + 1 + m] × [b₂ − m, b₂ + 1 + m]` (block units) satisfies
`BoxOK` (`floor_facts`), every point of `[0,1]²` outside it is at distance `≥ 2s` from the block
(`outBox_far`), and the block of `x` is within `m` blocks of `b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF
namespace T20E

lemma scale_eq (K : ℕ) (r : ℝ) : r * 2 ^ K * (2 : ℝ)⁻¹ ^ K = r := by
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]

/-- the integer facts behind the box -/
lemma floor_facts {X Y N : ℝ} {b : ℤ} {m : ℕ} (hX0 : 0 ≤ X) (hX1 : X ≤ N) (hY : ⌊Y⌋ = b)
    (hXY : |X - Y| < m) :
    (b : ℝ) - m < N ∧ -(m : ℤ) < b + 1 ∧ b - m ≤ ⌊X⌋ ∧ ⌊X⌋ ≤ b + m := by
  have h1 := Int.floor_le Y
  have h2 := Int.lt_floor_add_one Y
  have h3 := Int.floor_le X
  have h4 := Int.lt_floor_add_one X
  rw [hY] at h1 h2
  rw [abs_lt] at hXY
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · have : (-(m : ℝ)) < b + 1 := by linarith
    exact_mod_cast this
  · have : ((b : ℝ) - m) < ⌊X⌋ + 1 := by linarith
    have : b - (m : ℤ) < ⌊X⌋ + 1 := by exact_mod_cast this
    omega
  · have : ((⌊X⌋ : ℤ) : ℝ) < b + 1 + m := by linarith
    have : ⌊X⌋ < b + 1 + (m : ℤ) := by exact_mod_cast this
    omega

/-- points of `[0,1]²` outside the box are far from the block -/
lemma outBox_far {K : ℕ} {b : ℤ × ℤ} {s : ℝ} {m : ℕ} (hm : 2 * s * 2 ^ K ≤ m) {x : ℂ}
    (hx : x ∈ outBox K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m)) :
    x ∈ T20B.farSet (T20B.hoBlock K b) s := by
  intro y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have e1 : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [← mul_pow]; norm_num
  have hms : 2 * s ≤ (m : ℝ) * (2 : ℝ)⁻¹ ^ K := by
    have := mul_le_mul_of_nonneg_right hm hp.le
    rwa [mul_assoc, e1, mul_one] at this
  have a1 := Int.floor_le (y.re * 2 ^ K)
  have a2 := Int.lt_floor_add_one (y.re * 2 ^ K)
  have a3 := Int.floor_le (y.im * 2 ^ K)
  have a4 := Int.lt_floor_add_one (y.im * 2 ^ K)
  rw [hy1] at a1 a2
  rw [hy2] at a3 a4
  have r1 := scale_eq K y.re
  have r2 := scale_eq K y.im
  have b1 : (b.1 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ y.re := by nlinarith
  have b2 : y.re < ((b.1 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by nlinarith
  have b3 : (b.2 : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ y.im := by nlinarith
  have b4 : y.im < ((b.2 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by nlinarith
  have hre := Complex.abs_re_le_norm (x - y)
  have him := Complex.abs_im_le_norm (x - y)
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  simp only [outBox, mem_union, mem_setOf_eq] at hx
  push_cast at hx
  rcases hx with ((h | h) | h) | h
  · have := neg_abs_le (x.im - y.im); nlinarith
  · have := le_abs_self (x.im - y.im); nlinarith
  · have := neg_abs_le (x.re - y.re); nlinarith
  · have := le_abs_self (x.re - y.re); nlinarith

/-- the block of a point of `[0,1]` -/
lemma floor_block (K : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (-1 : ℤ) ≤ ⌊r * 2 ^ K⌋ ∧ ⌊r * 2 ^ K⌋ ≤ 2 ^ K ∧
      (⌊r * 2 ^ K⌋ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ r ∧ r ≤ ((⌊r * 2 ^ K⌋ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have hp2 : (0 : ℝ) < 2 ^ K := by positivity
  have a1 := Int.floor_le (r * 2 ^ K)
  have a2 := Int.lt_floor_add_one (r * 2 ^ K)
  have r1 := scale_eq K r
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (0 : ℤ) ≤ ⌊r * 2 ^ K⌋ := Int.floor_nonneg.2 (by positivity)
    omega
  · have h3 : r * 2 ^ K ≤ 2 ^ K := by nlinarith
    have : ((⌊r * 2 ^ K⌋ : ℤ) : ℝ) ≤ ((2 ^ K : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have := mul_le_mul_of_nonneg_right a1 hp.le; linarith
  · have := mul_le_mul_of_nonneg_right a2.le hp.le; linarith

/-- a point of the `3`-neighbourhood of the box is near the centre of a block within `m` -/
lemma elem_near {K : ℕ} {m : ℕ} {b P' : ℤ × ℤ} (c1 : b.1 - m ≤ P'.1) (c2 : P'.1 ≤ b.1 + m)
    (c3 : b.2 - m ≤ P'.2) (c4 : P'.2 ≤ b.2 + m) {x : ℂ}
    (hx : x ∈ gRect K (b.1 - m - 3) (b.1 + 1 + m + 3) (b.2 - m - 3) (b.2 + 1 + m + 3)) :
    ‖x - T20.dyCenter K P'‖ ≤ (4 * m + 8) * (2 : ℝ)⁻¹ ^ K := by
  have hp : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hx
  have d1 : ((b.1 - m : ℤ) : ℝ) ≤ (P'.1 : ℝ) := by exact_mod_cast c1
  have d2 : (P'.1 : ℝ) ≤ ((b.1 + m : ℤ) : ℝ) := by exact_mod_cast c2
  have d3 : ((b.2 - m : ℤ) : ℝ) ≤ (P'.2 : ℝ) := by exact_mod_cast c3
  have d4 : (P'.2 : ℝ) ≤ ((b.2 + m : ℤ) : ℝ) := by exact_mod_cast c4
  push_cast at a1 a2 a3 a4 d1 d2 d3 d4
  have hd1 : |(x - T20.dyCenter K P').re| ≤ (2 * m + 4) * (2 : ℝ)⁻¹ ^ K := by
    rw [abs_le]; simp only [Complex.sub_re, T20.dyCenter]
    constructor <;> nlinarith
  have hd2 : |(x - T20.dyCenter K P').im| ≤ (2 * m + 4) * (2 : ℝ)⁻¹ ^ K := by
    rw [abs_le]; simp only [Complex.sub_im, T20.dyCenter]
    constructor <;> nlinarith
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  linarith

end T20E
end DDDF
end LQGMetric
