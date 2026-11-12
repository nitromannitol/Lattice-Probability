/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L13Approx at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening

/-!
# DDDF Lemma 13: the piecewise-constant approximation (task P2-DDDFL913; DDDF.L13)

DF (Ding–Falconet, arXiv:1809.02607) §2.3, DF:226–236, used by DDDF Lemma 13 (arXiv:1904.08021,
`tightness.tex` l. 771–780): `L(R, k)` is the crossing length for the field `φ^k`, constant on each
dyadic block of size `2^{-k}`, so that it is an increasing function of finitely many values of
the field, and `L(R, k) → L(R)` for a continuous field.

Here: `dyRound k x` is the lower-left corner of the dyadic block of `x` (DF takes the centre; any
point of the block works, the only property used is `|dyRound k x − x| ≤ 2 · 2^{-k}`).
`blockField k D v` is the piecewise-constant field with values `v : D → ℝ` at the corners in the
finite set `D` (`0` elsewhere). Results:
* `rectLen_congr`: `L(R, f)` depends only on `f` on `R`;
* `rectLen_mono`: monotonicity in the field (`ξ ≥ 0`);
* `isOpen_lenUpper`, `isUpperSet_lenUpper`: `{v | x < L(R, blockField v)}` is an open upper set;
* `finite_dyRound_image`: finitely many corners over a bounded set;
* `tendsto_rectLen_dyRound`: `L(R, Y ∘ dyRound k) → L(R, Y)` for continuous `Y` (DF's comparison
  `e^{∓O(2^{-k})‖∇φ‖} L(R) ≤ L(R,k) ≤ …`, with the modulus of continuity instead of the gradient).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

variable {ξ : ℝ}

/-- `L(R, f)` depends only on `f` on `R` -/
theorem rectLen_congr (R : MarkedRect) {f g : ℂ → ℝ} (h : ∀ x ∈ R.toSet, f x = g x) :
    rectLen ξ f R = rectLen ξ g R := by
  have h1 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := R.side₁) (B := R.side₂) (c := 0)
    (U := R.toSet) (f := f) (g := g) fun x hx => by rw [h x hx, sub_self, abs_zero]
  have h2 := crossLenIn_le_of_abs_sub_le (ξ := ξ) (A := R.side₁) (B := R.side₂) (c := 0)
    (U := R.toSet) (f := g) (g := f) fun x hx => by rw [h x hx, sub_self, abs_zero]
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h1 h2
  exact le_antisymm h1 h2

/-- dyadic rounding: the lower-left corner of the dyadic block of side `2^{-k}` containing `x` -/
def dyRound (k : ℕ) (x : ℂ) : ℂ :=
  ⟨(⌊(2 : ℝ) ^ k * x.re⌋ : ℝ) / 2 ^ k, (⌊(2 : ℝ) ^ k * x.im⌋ : ℝ) / 2 ^ k⟩

theorem abs_floor_div_sub_le (k : ℕ) (t : ℝ) :
    |(⌊(2 : ℝ) ^ k * t⌋ : ℝ) / 2 ^ k - t| ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := Int.floor_le ((2 : ℝ) ^ k * t)
  have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ k * t)
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add, div_add' _ _ _ hk.ne', le_div_iff₀ hk]
    rw [inv_mul_cancel₀ hk.ne']; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hk, add_mul, inv_mul_cancel₀ hk.ne']; nlinarith

theorem dist_dyRound_le (k : ℕ) (x : ℂ) : dist (dyRound k x) x ≤ 2 * ((2 : ℝ) ^ k)⁻¹ := by
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have h1 := abs_floor_div_sub_le k x.re
  have h2 := abs_floor_div_sub_le k x.im
  simp only [dyRound, Complex.sub_re, Complex.sub_im]
  linarith

/-- finitely many dyadic corners over a bounded set -/
theorem finite_dyRound_image (k : ℕ) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    (dyRound k '' K).Finite := by
  obtain ⟨B, hB⟩ := hK.subset_closedBall 0
  set N : ℤ := ⌈(2 : ℝ) ^ k * B⌉ + 1
  have hfin : ((fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / 2 ^ k, (p.2 : ℝ) / 2 ^ k⟩ : ℂ)) ''
      (Icc (-N) N ×ˢ Icc (-N) N)).Finite :=
    ((finite_Icc _ _).prod (finite_Icc _ _)).image _
  refine hfin.subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxB : ‖x‖ ≤ B := by simpa using hB hx
  have hk : (0 : ℝ) ≤ 2 ^ k := by positivity
  have hfl : ∀ t : ℝ, |t| ≤ B → ⌊(2 : ℝ) ^ k * t⌋ ∈ Icc (-N) N := fun t ht => by
    have ht' := abs_le.1 ht
    have hc := Int.le_ceil ((2 : ℝ) ^ k * B)
    constructor
    · have : (-(N : ℝ)) ≤ ⌊(2 : ℝ) ^ k * t⌋ := by
        have := Int.lt_floor_add_one ((2 : ℝ) ^ k * t)
        have := mul_le_mul_of_nonneg_left ht'.1 hk
        push_cast [N]; nlinarith
      exact_mod_cast this
    · have : (⌊(2 : ℝ) ^ k * t⌋ : ℝ) ≤ N := by
        have := Int.floor_le ((2 : ℝ) ^ k * t)
        have := mul_le_mul_of_nonneg_left ht'.2 hk
        push_cast [N]; nlinarith
      exact_mod_cast this
  exact ⟨(⌊(2 : ℝ) ^ k * x.re⌋, ⌊(2 : ℝ) ^ k * x.im⌋),
    ⟨hfl _ ((Complex.abs_re_le_norm x).trans hxB), hfl _ ((Complex.abs_im_le_norm x).trans hxB)⟩,
    rfl⟩

open Classical in
/-- the piecewise-constant field with values `v` at the dyadic corners in `D` (`0` elsewhere) -/
def blockField (k : ℕ) (D : Finset ℂ) (v : D → ℝ) (x : ℂ) : ℝ :=
  if h : dyRound k x ∈ D then v ⟨dyRound k x, h⟩ else 0

theorem blockField_mono (k : ℕ) (D : Finset ℂ) {v v' : D → ℝ} (h : v ≤ v') (x : ℂ) :
    blockField k D v x ≤ blockField k D v' x := by
  unfold blockField; split_ifs; exacts [h _, le_rfl]

theorem abs_blockField_sub_le (k : ℕ) (D : Finset ℂ) (v v' : D → ℝ) (x : ℂ) :
    |blockField k D v x - blockField k D v' x| ≤ ‖v - v'‖ := by
  unfold blockField; split_ifs
  · have := norm_le_pi_norm (v - v') ⟨dyRound k x, by assumption⟩
    simpa [Real.norm_eq_abs] using this
  · simp

theorem abs_blockField_le (k : ℕ) (D : Finset ℂ) (v : D → ℝ) (x : ℂ) :
    |blockField k D v x| ≤ ‖v‖ := by
  unfold blockField; split_ifs
  · simpa [Real.norm_eq_abs] using norm_le_pi_norm v ⟨dyRound k x, by assumption⟩
  · simp

theorem blockField_eq (k : ℕ) (D : Finset ℂ) (Y : ℂ → ℝ) {x : ℂ} (hx : dyRound k x ∈ D) :
    blockField k D (fun s => Y s) x = Y (dyRound k x) := by
  simp [blockField, hx]

end DDDF
end LQGMetric
