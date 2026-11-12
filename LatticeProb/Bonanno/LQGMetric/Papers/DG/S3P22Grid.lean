/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P22Grid at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P22Main
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.22: the dyadic grid satisfies the geometric fields of `DGP322Hyp`

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, proof of Proposition 3.22
(DG:1739–1756): `𝒮_{δ_ε}(1/2)` is "the set of squares `S ⊂ 𝕊(1/2)` with side length `δ_ε` and
corners in `δ_ε ℤ²`", `S(1)` the concentric square of three times the side length.

Here `U = (−1/2, 3/2)²` (so `closure U = 𝕊(1/2) = [−1/2,3/2]²`), `a = 2^{-n}` (`n ≥ 1`), the
squares are `gridSq a k = [k₁a,(k₁+1)a] × [k₂a,(k₂+1)a]` for `k` in `gridIdx a` (exactly the
`k` with `gridSq a k ⊆ 𝕊(1/2)`, `gridIdx_iff`), and `gridSqOne a k = S(1)`. We prove the fields
`convex`, `cell`, `sub`, `conv`, `closed`, `sep` (with `a`) and `diam` (with `A = 3√2 a`) of
`DGP322Hyp`, and `S(1) ⊆ [−1,2]² = 𝕊(1)` (`gridSqOne_subset`), and bundle them
(`dgP322Hyp_grid`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the open square `(−1/2, 3/2)²`, interior of DG's `𝕊(1/2)` -/
def sqHalfOpen : Set ℂ := Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-1 / 2 : ℝ) (3 / 2)

/-- the dyadic square `[k₁a,(k₁+1)a] × [k₂a,(k₂+1)a]` -/
def gridSq (a : ℝ) (k : ℤ × ℤ) : Set ℂ :=
  Icc (k.1 * a) ((k.1 + 1) * a) ×ℂ Icc (k.2 * a) ((k.2 + 1) * a)

/-- the expanded square `S(1)` (same centre, three times the side length) -/
def gridSqOne (a : ℝ) (k : ℤ × ℤ) : Set ℂ :=
  Icc ((k.1 - 1) * a) ((k.1 + 2) * a) ×ℂ Icc ((k.2 - 1) * a) ((k.2 + 2) * a)

lemma convex_reProdIm_of {s t : Set ℝ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    Convex ℝ (s ×ℂ t) := by
  have h := convex_convexHull ℝ (s ×ℂ t)
  rwa [Complex.convexHull_reProdIm, hs.convexHull_eq, ht.convexHull_eq] at h

lemma interior_gridSqOne (a : ℝ) (k : ℤ × ℤ) :
    interior (gridSqOne a k) =
      Ioo ((k.1 - 1) * a) ((k.1 + 2) * a) ×ℂ Ioo ((k.2 - 1) * a) ((k.2 + 2) * a) := by
  rw [gridSqOne, Complex.interior_reProdIm, interior_Icc, interior_Icc]

/-- field `sub`: `S ⊆ interior S(1)` -/
lemma gridSq_subset_interior {a : ℝ} (ha : 0 < a) (k : ℤ × ℤ) :
    gridSq a k ⊆ interior (gridSqOne a k) := by
  rw [interior_gridSqOne]
  intro z hz
  rw [gridSq, Complex.mem_reProdIm] at hz
  rw [Complex.mem_reProdIm]
  exact ⟨⟨by nlinarith [hz.1.1], by nlinarith [hz.1.2]⟩, ⟨by nlinarith [hz.2.1], by
    nlinarith [hz.2.2]⟩⟩

/-- field `conv` -/
lemma convex_gridSqOne (a : ℝ) (k : ℤ × ℤ) : Convex ℝ (gridSqOne a k) :=
  convex_reProdIm_of (convex_Icc _ _) (convex_Icc _ _)

/-- field `closed` -/
lemma isClosed_gridSqOne (a : ℝ) (k : ℤ × ℤ) : IsClosed (gridSqOne a k) :=
  isClosed_Icc.reProdIm isClosed_Icc

/-- field `sep`: points of `S` are at distance `≥ a` from `∂S(1)` -/
lemma gridSq_sep {a : ℝ} (ha : 0 < a) (k : ℤ × ℤ) :
    ∀ x ∈ gridSq a k, ∀ y ∈ frontier (gridSqOne a k), a ≤ ‖x - y‖ := by
  intro x hx y hy
  rw [frontier, (isClosed_gridSqOne a k).closure_eq, interior_gridSqOne] at hy
  obtain ⟨hyT, hyI⟩ := hy
  rw [gridSq, Complex.mem_reProdIm] at hx
  rw [Complex.mem_reProdIm, not_and_or] at hyI
  rcases hyI with h | h
  · have h' : y.re ≤ (k.1 - 1) * a ∨ (k.1 + 2) * a ≤ y.re := by
      by_contra hc; push Not at hc; exact h ⟨hc.1, hc.2⟩
    refine le_trans ?_ (Complex.abs_re_le_norm (x - y))
    rw [Complex.sub_re]
    rcases h' with h' | h'
    · rw [abs_of_nonneg (by nlinarith [hx.1.1])]; nlinarith [hx.1.1]
    · rw [abs_of_nonpos (by nlinarith [hx.1.2])]; nlinarith [hx.1.2]
  · have h' : y.im ≤ (k.2 - 1) * a ∨ (k.2 + 2) * a ≤ y.im := by
      by_contra hc; push Not at hc; exact h ⟨hc.1, hc.2⟩
    refine le_trans ?_ (Complex.abs_im_le_norm (x - y))
    rw [Complex.sub_im]
    rcases h' with h' | h'
    · rw [abs_of_nonneg (by nlinarith [hx.2.1])]; nlinarith [hx.2.1]
    · rw [abs_of_nonpos (by nlinarith [hx.2.2])]; nlinarith [hx.2.2]

/-- field `diam`: `diam S(1) ≤ 3√2 a` -/
lemma gridSqOne_diam {a : ℝ} (ha : 0 < a) (k : ℤ × ℤ) :
    ∀ x ∈ gridSqOne a k, ∀ y ∈ gridSqOne a k, ‖x - y‖ ≤ 3 * Real.sqrt 2 * a := by
  intro x hx y hy
  rw [gridSqOne, Complex.mem_reProdIm] at hx hy
  have hre : |(x - y).re| ≤ 3 * a := by
    rw [Complex.sub_re, abs_le]; constructor <;> nlinarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
  have him : |(x - y).im| ≤ 3 * a := by
    rw [Complex.sub_im, abs_le]; constructor <;> nlinarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  have hsq : ‖x - y‖ ^ 2 ≤ (3 * Real.sqrt 2 * a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have h1 : (x - y).re * (x - y).re ≤ (3 * a) ^ 2 := by
      rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
    have h2 : (x - y).im * (x - y).im ≤ (3 * a) ^ 2 := by
      rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end DG
end LQGMetric
