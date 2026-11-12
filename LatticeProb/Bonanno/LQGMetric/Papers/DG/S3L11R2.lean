/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11R2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Sc
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3TrInv5

/-!
# DG L3.11 at `μ = μ_ĥ`: node 1 and the geometry of the `s/32` grid (P2-DG105p, D116)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1236–1276.

* `muTrSqInv_of_whiteNoise`: node 1 (`MuTrSqInv`, S3L11In6) from P2-DGTRINV's
  `prob_lgdPts_muTr_eq` (S3TrInv5).
* The geometry of the grid of side `s/32` (D116): the unit-frame square
  `sqOne (1/32) l311UnitB (0,0) = [29/64,35/64]²` has its side midpoints in DZZ's `𝕍̄`
  (`dg_lemma312` applies) and lies in the interior of `K₀ = [1/10, 9/10]²`; for a rectangle
  `sℛ_n + b ⊆ [1/6,5/6]²` every grid square maps `K₀` into its interior (the hypothesis of
  `ae_goodSq_scale`); the dependence regions `l311LocReg` of sites at `ℓ^∞`-distance `> 9`
  are disjoint (DG:1267–1276, `|P|/100` pairwise independent sites).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the box `K₀ = [1/10, 9/10]²` of `μ_ĥ` used by the consumers (S3P18D `p18_hK0`) -/
abbrev l311K0 : Set ℂ := ferniqueBox ⟨1 / 10, 1 / 10⟩ (4 / 5)

lemma l311_unit_mids : sqMids (1 / 32) l311UnitB (0, 0) ⊆ l312Vbar := by
  intro u hu
  simp only [sqMids, mem_insert_iff, mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
    simp only [l312Vbar, l312Box, sqX, sqY, l311UnitB, mem_setOf_eq] <;> norm_num [abs_le]

lemma l311_unit_sub_int : sqOne (1 / 32) l311UnitB (0, 0) ⊆ interior l311K0 := by
  unfold l311K0 ferniqueBox
  rw [Complex.interior_reProdIm]; simp only [interior_Icc]
  intro u hu
  simp only [sqOne, sqX, sqY, l311UnitB, Complex.mem_reProdIm, mem_Icc, mem_Ioo] at hu ⊢
  norm_num at hu ⊢
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hu.1.1, hu.1.2, hu.2.1, hu.2.2]

lemma l311_unit_sub : sqOne (1 / 32) l311UnitB (0, 0) ⊆ l311K0 :=
  l311_unit_sub_int.trans interior_subset

/-- the grid of `s ℛ_n + b` (side `s/32`) -/
abbrev l311Grid (n : ℕ) (x : ℤ × ℤ) : Prop :=
  percInGrid (2 * ((32 * n : ℕ) : ℤ)) (((32 * n : ℕ) : ℤ) - 2) x

/-- coordinates of a grid square: `0 ≤ x₁ ≤ 64n − 1`, `0 ≤ x₂ ≤ 32n − 3`, `1 ≤ n` -/
lemma l311Grid_bounds {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) {s : ℝ} (hs : 0 < s) :
    1 ≤ (n : ℝ) ∧ 0 ≤ s / 32 * (x.1 : ℝ) ∧ s / 32 * (x.1 : ℝ) ≤ 2 * (s * n) - s / 32 ∧
      s / 32 ≤ s / 32 * ((x.2 : ℝ) + 1) ∧ s / 32 * ((x.2 : ℝ) + 1) ≤ s * n - s / 16 := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  push_cast at h2 h4
  have hn : (1 : ℤ) ≤ n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have a1 : (0 : ℝ) ≤ x.1 := by exact_mod_cast h1
  have a2 : (x.1 : ℝ) ≤ 64 * n - 1 := by
    have : x.1 ≤ 64 * (n : ℤ) - 1 := by omega
    exact_mod_cast this
  have a3 : (0 : ℝ) ≤ x.2 := by exact_mod_cast h3
  have a4 : (x.2 : ℝ) ≤ 32 * n - 3 := by
    have : x.2 ≤ 32 * (n : ℤ) - 3 := by omega
    exact_mod_cast this
  have hs' : 0 ≤ s / 32 := by positivity
  refine ⟨hn', by positivity, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left a2 hs'
    linarith
  · have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (x.2 : ℝ) + 1 by linarith) hs'
    linarith
  · have := mul_le_mul_of_nonneg_left (show (x.2 : ℝ) + 1 ≤ 32 * n - 2 by linarith) hs'
    linarith

/-- every grid square's `S(1)` lies in `s ℛ_n' + b` -/
lemma l311_sqOne_sub_str {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) {s : ℝ} (hs : 0 < s)
    (b : ℂ) : sqOne (s / 32) b x ⊆ l313Str s b n := by
  obtain ⟨hn, a1, a2, a3, a4⟩ := l311Grid_bounds hx hs
  have ht : s ≤ s * n := by nlinarith
  intro u hu
  simp only [sqOne, sqX, sqY, l313Str, Complex.mem_reProdIm, mem_Icc] at hu ⊢
  obtain ⟨⟨u1, u2⟩, u3, u4⟩ := hu
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- for `s ℛ_n + b ⊆ [1/6,5/6]²`, the scaling of every grid square maps `K₀` into its interior
(the hypothesis `hTK` of `ae_goodSq_scale`) -/
lemma l311_affine_K0 {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) {s : ℝ} (hs : 0 < s) {b : ℂ}
    (hQ : l313Str s b n ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    affineC s (l311Corner s b x) '' l311K0 ⊆ interior l311K0 := by
  obtain ⟨hn, a1, a2, a3, a4⟩ := l311Grid_bounds hx hs
  have ht : s ≤ s * n := by nlinarith
  have hsn : 0 ≤ s * n := by positivity
  have c1 := hQ (show (⟨b.re - s * n, b.im⟩ : ℂ) ∈ l313Str s b n by
    simp only [l313Str, Complex.mem_reProdIm, mem_Icc]; refine ⟨⟨le_rfl, ?_⟩, le_rfl, ?_⟩ <;>
      linarith)
  have c2 := hQ (show (⟨b.re + 3 * (s * n), b.im + s * n⟩ : ℂ) ∈ l313Str s b n by
    simp only [l313Str, Complex.mem_reProdIm, mem_Icc]; refine ⟨⟨?_, le_rfl⟩, ?_, le_rfl⟩ <;>
      linarith)
  simp only [Complex.mem_reProdIm, mem_Icc] at c1 c2
  unfold l311K0 ferniqueBox
  rw [Complex.interior_reProdIm]; simp only [interior_Icc]
  rintro _ ⟨w, hw, rfl⟩
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc] at hw
  norm_num at hw
  obtain ⟨⟨w1, w2⟩, w3, w4⟩ := hw
  have e1 := mul_le_mul_of_nonneg_left w1 hs.le
  have e2 := mul_le_mul_of_nonneg_left w2 hs.le
  have e3 := mul_le_mul_of_nonneg_left w3 hs.le
  have e4 := mul_le_mul_of_nonneg_left w4 hs.le
  simp only [Complex.mem_reProdIm, mem_Ioo, affineC_re, affineC_im, l311Corner, sqX, sqY]
  norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- the hypothesis `hsq` of `ae_goodSq_scale` -/
lemma l311_sqOne_sub_affine {s : ℝ} (hs : 0 < s) (b : ℂ) (x : ℤ × ℤ) :
    sqOne (s / 32) b x ⊆ affineC s (l311Corner s b x) '' interior l311K0 := by
  intro u hu
  refine ⟨(u - l311Corner s b x) / (s : ℂ), ?_, ?_⟩
  · apply l311_unit_sub_int
    rw [← preimage_sqOne_l311 hs b x, mem_preimage]
    convert hu using 1
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [affineC]; field_simp; ring
  · have : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [affineC]; field_simp; ring

/-- the dependence region of a grid square, in coordinates: centre `sqX + s/64`, `sqY + s/64`,
half-width `s (3/64 + 1/10)` -/
lemma l311LocReg_center {j : ℕ} {b : ℂ} {x : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ affineC ((2 : ℝ)⁻¹ ^ j) (l311Corner ((2 : ℝ)⁻¹ ^ j) b x) ''
      Metric.thickening (1 / 10) (sqOne (1 / 32) l311UnitB (0, 0))) :
    |z.re - (sqX ((2 : ℝ)⁻¹ ^ j / 32) b x + (2 : ℝ)⁻¹ ^ j / 64)| <
        (2 : ℝ)⁻¹ ^ j * (3 / 64 + 1 / 10) ∧
      |z.im - (sqY ((2 : ℝ)⁻¹ ^ j / 32) b x + (2 : ℝ)⁻¹ ^ j / 64)| <
        (2 : ℝ)⁻¹ ^ j * (3 / 64 + 1 / 10) := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ j
  have hs : 0 < s := by positivity
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨u, hu, hd⟩ := Metric.mem_thickening_iff.1 hw
  simp only [sqOne, sqX, sqY, l311UnitB, Complex.mem_reProdIm, mem_Icc] at hu
  norm_num at hu
  have hre : |w.re - u.re| < 1 / 10 := by
    rw [dist_eq_norm] at hd
    exact lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - u)) hd
  have him : |w.im - u.im| < 1 / 10 := by
    rw [dist_eq_norm] at hd
    exact lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - u)) hd
  have er : (affineC s (l311Corner s b x) w).re - (sqX (s / 32) b x + s / 64) =
      s * (w.re - 1 / 2) := by
    simp only [affineC_re, l311Corner]; ring
  have ei : (affineC s (l311Corner s b x) w).im - (sqY (s / 32) b x + s / 64) =
      s * (w.im - 1 / 2) := by
    simp only [affineC_im, l311Corner]; ring
  rw [er, ei, abs_mul, abs_mul, abs_of_pos hs]
  rw [abs_lt] at hre him
  constructor <;> refine mul_lt_mul_of_pos_left ?_ hs <;> rw [abs_lt] <;>
    constructor <;> linarith [hu.1.1, hu.1.2, hu.2.1, hu.2.2]

/-- **DG:1267–1276**: the dependence regions of sites at `ℓ^∞`-distance `> 9` are disjoint -/
lemma l311LocReg_disjoint {j : ℕ} {b : ℂ} {x y : ℤ × ℤ} (hxy : PercFar 9 x y) :
    Disjoint (l311LocReg j (l311Corner ((2 : ℝ)⁻¹ ^ j) b x))
      (l311LocReg j (l311Corner ((2 : ℝ)⁻¹ ^ j) b y)) := by
  rw [Set.disjoint_left]
  rintro ⟨t, z⟩ hx hy
  obtain ⟨-, hx⟩ := hx
  obtain ⟨-, hy⟩ := hy
  have h1 := l311LocReg_center hx
  have h2 := l311LocReg_center hy
  set s : ℝ := (2 : ℝ)⁻¹ ^ j
  have hs : 0 < s := by positivity
  simp only [sqX, sqY] at h1 h2
  simp only [abs_lt] at h1 h2
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h1
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := h2
  unfold PercFar at hxy
  have key : ∀ p q : ℤ, (9 : ℤ) < p - q → s / 32 * 10 ≤ s / 32 * (p : ℝ) - s / 32 * q := by
    intro p q h
    have : (10 : ℝ) ≤ (p : ℝ) - q := by
      have : (10 : ℤ) ≤ p - q := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ s / 32)
    linarith
  rcases hxy with h | h | h | h
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith

/-- the index set of the exceptional event: `[0,64n) × [0,32n)` -/
def l311Idx (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Ico 0 ((64 * n : ℕ) : ℤ) ×ˢ Finset.Ico 0 ((32 * n : ℕ) : ℤ)

lemma mem_l311Idx {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) : x ∈ l311Idx n := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  simp only [l311Idx, Finset.mem_product, Finset.mem_Ico]
  push_cast at h2 h4 ⊢
  omega

lemma card_l311Idx (n : ℕ) : ((l311Idx n).card : ℝ) ≤ 2048 * ((n : ℝ) + 1) ^ 2 := by
  simp only [l311Idx, Finset.card_product, Int.card_Ico, sub_zero, Int.toNat_natCast]
  push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end DG
end LQGMetric
