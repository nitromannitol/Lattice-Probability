/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L19R5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19R4
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L19Sc
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R2

/-!
# DG Lemma 3.19 at `μ = μ_ĥ`: the geometry of the annulus grid (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1641 (`S(1) ⊂ 𝒜_n`), on the
grid of side `s/32` of `s𝒜_n + b` (D116), sites recentred at `c₀ = ⌊32n/2⌋`. For a site `z` of
the annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ 32n − 2 + c₀` (the sites of `L319LevelInput`), the cell map
`T y = s y + l319Corner s b c₀ z` sends `u = 1/2 + i/2` to the centre of the cell, and

* `f(annSq) ⊆ l312Box u (1/32) = 𝕍̄_{u,5/8}` and `f^{-1}(𝕍̄_u) ⊆ annSqHalf` (`l319_hA₀`,
  `l319_hB₀`);
* `T(B̄(u, 13/280)) ⊆ s𝒜_n' + b = l321Out` (`l319_TD`: the margin of the cell centre to the
  outer boundary is `3s/64 > 13s/280`), so the minimum of `ĥ_s` in DG's `T_S` bounds `ĥ_s` there;
* `T(K₀) ⊆ int K₀` when `l321Out ⊆ [1/6,5/6]²` (`l319_hTK`, using `s = 2^{-j} ≤ 1/8`);
* the regions `l319LocReg` of sites at `ℓ^∞`-distance `> 9` are disjoint
  (`l319LocReg_disjoint`: half-width `(1/10 + 13/280) s < 5s/32`).
Own elementary geometric glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open SupTail

/-- the sites of `L319LevelInput` (the annulus `c₀ + 2 ≤ ‖z‖_∞ ≤ 32n − 2 + c₀`) -/
def l319Site (n : ℕ) (z : ℤ × ℤ) : Prop :=
  ∃ d, z ∈ annRect ((32 * n / 2 + 2 : ℕ) : ℤ) ((32 * n - 2 + 32 * n / 2 : ℕ) : ℤ) d

/-- the corner `c` of the cell map `y ↦ s y + c` of site `z` (it sends `1/2 + i/2` to the centre
of the cell `annSq (s/32) b c₀ z`) -/
def l319Corner (s : ℝ) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) : ℂ :=
  ⟨b.re + s / 32 * ((c₀ + z.1 : ℤ) : ℝ) + s / 64 - s / 2,
    b.im + s / 32 * ((c₀ + z.2 : ℤ) : ℝ) + s / 64 - s / 2⟩

lemma l319Site_bounds {n : ℕ} {z : ℤ × ℤ} (hz : l319Site n z) :
    1 ≤ n ∧ 2 - 32 * (n : ℤ) ≤ ((32 * n / 2 : ℕ) : ℤ) + z.1 ∧
      ((32 * n / 2 : ℕ) : ℤ) + z.1 ≤ 64 * n - 2 ∧
      2 - 32 * (n : ℤ) ≤ ((32 * n / 2 : ℕ) : ℤ) + z.2 ∧
      ((32 * n / 2 : ℕ) : ℤ) + z.2 ≤ 64 * n - 2 := by
  obtain ⟨d, ⟨h1, h2, h3, h4⟩, hd⟩ := hz
  cases d <;> simp only [annDir] at hd <;> omega

lemma l319Site_real {n : ℕ} {z : ℤ × ℤ} (hz : l319Site n z) {s : ℝ} (hs : 0 < s) :
    1 ≤ (n : ℝ) ∧
      s / 16 - s * n ≤ s / 32 * ((((32 * n / 2 : ℕ) : ℤ) + z.1 : ℤ) : ℝ) ∧
      s / 32 * ((((32 * n / 2 : ℕ) : ℤ) + z.1 : ℤ) : ℝ) ≤ 2 * (s * n) - s / 16 ∧
      s / 16 - s * n ≤ s / 32 * ((((32 * n / 2 : ℕ) : ℤ) + z.2 : ℤ) : ℝ) ∧
      s / 32 * ((((32 * n / 2 : ℕ) : ℤ) + z.2 : ℤ) : ℝ) ≤ 2 * (s * n) - s / 16 := by
  obtain ⟨hn, a1, a2, a3, a4⟩ := l319Site_bounds hz
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs' : 0 ≤ s / 32 := by positivity
  have c1 : (2 : ℝ) - 32 * n ≤ ((((32 * n / 2 : ℕ) : ℤ) + z.1 : ℤ) : ℝ) := by exact_mod_cast a1
  have c2 : ((((32 * n / 2 : ℕ) : ℤ) + z.1 : ℤ) : ℝ) ≤ 64 * n - 2 := by exact_mod_cast a2
  have c3 : (2 : ℝ) - 32 * n ≤ ((((32 * n / 2 : ℕ) : ℤ) + z.2 : ℤ) : ℝ) := by exact_mod_cast a3
  have c4 : ((((32 * n / 2 : ℕ) : ℤ) + z.2 : ℤ) : ℝ) ≤ 64 * n - 2 := by exact_mod_cast a4
  have d1 := mul_le_mul_of_nonneg_left c1 hs'
  have d2 := mul_le_mul_of_nonneg_left c2 hs'
  have d3 := mul_le_mul_of_nonneg_left c3 hs'
  have d4 := mul_le_mul_of_nonneg_left c4 hs'
  refine ⟨hn', ?_, ?_, ?_, ?_⟩ <;> linarith

lemma l319f_re (s : ℝ) (c y : ℂ) : (l319f s c y).re = s⁻¹ * (y.re - c.re) := by
  simp only [l319f]; rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.sub_re]

lemma l319f_im (s : ℝ) (c y : ℂ) : (l319f s c y).im = s⁻¹ * (y.im - c.im) := by
  simp only [l319f]; rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, Complex.sub_im]

lemma l319_unit1 {s a x : ℝ} (hs : 0 < s) (h1 : a ≤ x) (h2 : x ≤ a + s / 32) :
    |s⁻¹ * (x - (a + s / 64 - s / 2)) - 1 / 2| ≤ 1 / 32 / 2 := by
  set r := s⁻¹ * (x - (a + s / 64 - s / 2))
  have hr : s * r = x - (a + s / 64 - s / 2) := by
    simp only [r]; rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [abs_le]
  constructor
  · have := le_of_mul_le_mul_left (show s * (1 / 2 - 1 / 64) ≤ s * r by rw [hr]; linarith) hs
    linarith
  · have := le_of_mul_le_mul_left (show s * r ≤ s * (1 / 2 + 1 / 64) by rw [hr]; linarith) hs
    linarith

lemma l319_unit2 {s a x : ℝ} (hs : 0 < s)
    (h : |s⁻¹ * (x - (a + s / 64 - s / 2)) - 1 / 2| ≤ 1 / 20 / 2) :
    a - s / 32 / 2 ≤ x ∧ x ≤ a + s / 32 + s / 32 / 2 := by
  set r := s⁻¹ * (x - (a + s / 64 - s / 2))
  have hr : s * r = x - (a + s / 64 - s / 2) := by
    simp only [r]; rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  obtain ⟨h1, h2⟩ := abs_le.1 h
  have e1 := mul_le_mul_of_nonneg_left (show 1 / 2 - 1 / 40 ≤ r by linarith) hs.le
  have e2 := mul_le_mul_of_nonneg_left (show r ≤ 1 / 2 + 1 / 40 by linarith) hs.le
  constructor <;> linarith

/-- `f(S) ⊆ 𝕍̄_{u,5/8}` -/
lemma l319_hA₀ {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) :
    ∀ y ∈ annSq (s / 32) b c₀ z, l319f s (l319Corner s b c₀ z) y ∈ l312Box l319U (1 / 32) := by
  intro y hy
  simp only [annSq, Complex.mem_reProdIm, mem_Icc] at hy
  refine ⟨?_, ?_⟩
  · rw [l319f_re]; exact l319_unit1 hs hy.1.1 hy.1.2
  · rw [l319f_im]; exact l319_unit1 hs hy.2.1 hy.2.2

/-- `f^{-1}(𝕍̄_u) ⊆ S(1/2)` -/
lemma l319_hB₀ {s : ℝ} (hs : 0 < s) (b : ℂ) (c₀ : ℤ) (z : ℤ × ℤ) :
    ∀ y, l319f s (l319Corner s b c₀ z) y ∈ l312Box l319U (1 / 20) →
      y ∈ annSqHalf (s / 32) b c₀ z := by
  intro y ⟨h1, h2⟩
  rw [l319f_re] at h1
  rw [l319f_im] at h2
  obtain ⟨a1, a2⟩ := l319_unit2 hs h1
  obtain ⟨a3, a4⟩ := l319_unit2 hs h2
  simp only [annSqHalf, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨a1, a2⟩, a3, a4⟩

lemma abs_re_sub_le {w u : ℂ} : |w.re - u.re| ≤ ‖w - u‖ := by
  simpa using Complex.abs_re_le_norm (w - u)

lemma abs_im_sub_le {w u : ℂ} : |w.im - u.im| ≤ ‖w - u‖ := by
  simpa using Complex.abs_im_le_norm (w - u)

/-- `T(B̄(u, 13/280)) ⊆ l321Out` -/
lemma l319_TD {n : ℕ} {z : ℤ × ℤ} (hz : l319Site n z) {s : ℝ} (hs : 0 < s) (b : ℂ) :
    affineC s (l319Corner s b ((32 * n / 2 : ℕ) : ℤ) z) '' closedBall l319U l319r ⊆
      l321Out s b n := by
  obtain ⟨hn, a1, a2, a3, a4⟩ := l319Site_real hz hs
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  have hr := abs_le.1 (abs_re_sub_le.trans hw)
  have hi := abs_le.1 (abs_im_sub_le.trans hw)
  simp only [l319U, l319r] at hr hi
  have e1 := mul_le_mul_of_nonneg_left hr.1 hs.le
  have e2 := mul_le_mul_of_nonneg_left hr.2 hs.le
  have e3 := mul_le_mul_of_nonneg_left hi.1 hs.le
  have e4 := mul_le_mul_of_nonneg_left hi.2 hs.le
  simp only [l321Out, Complex.mem_reProdIm, mem_Icc, affineC_re, affineC_im, l319Corner]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

lemma two_inv_pow_le_eighth {j : ℕ} (h : (2 : ℝ)⁻¹ ^ j ≤ 2 / 9) : (2 : ℝ)⁻¹ ^ j ≤ 1 / 8 := by
  by_cases hj : j ≤ 2
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) hj
    norm_num at this; linarith
  · have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
      (show 3 ≤ j by omega)
    norm_num at this ⊢; linarith

/-- the hypothesis `hTK` of `ae_muHat_scale_set` for the annulus cells -/
lemma l319_hTK {n : ℕ} {z : ℤ × ℤ} (hz : l319Site n z) (j : ℕ) {b : ℂ}
    (hQ : l321Out ((2 : ℝ)⁻¹ ^ j) b n ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    affineC ((2 : ℝ)⁻¹ ^ j) (l319Corner ((2 : ℝ)⁻¹ ^ j) b ((32 * n / 2 : ℕ) : ℤ) z) ''
      l311K0 ⊆ interior l311K0 := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ j with hsdef
  have hs : 0 < s := by positivity
  obtain ⟨hn, a1, a2, a3, a4⟩ := l319Site_real hz hs
  have hsn : s ≤ s * n := by nlinarith
  have c1 := hQ (show (⟨b.re - s * n, b.im - s * n⟩ : ℂ) ∈ l321Out s b n by
    simp only [l321Out, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨le_rfl, ?_⟩, le_rfl, ?_⟩ <;> nlinarith)
  have c2 := hQ (show (⟨b.re + 2 * (s * n), b.im + 2 * (s * n)⟩ : ℂ) ∈ l321Out s b n by
    simp only [l321Out, Complex.mem_reProdIm, mem_Icc]
    refine ⟨⟨?_, le_rfl⟩, ?_, le_rfl⟩ <;> nlinarith)
  simp only [Complex.mem_reProdIm, mem_Icc] at c1 c2
  have hs8 : s ≤ 1 / 8 := two_inv_pow_le_eighth (by nlinarith)
  unfold l311K0 ferniqueBox
  rw [Complex.interior_reProdIm]; simp only [interior_Icc]
  rintro _ ⟨w, hw, rfl⟩
  simp only [Complex.mem_reProdIm, mem_Icc] at hw
  norm_num at hw
  obtain ⟨⟨w1, w2⟩, w3, w4⟩ := hw
  have e1 := mul_le_mul_of_nonneg_left w1 hs.le
  have e2 := mul_le_mul_of_nonneg_left w2 hs.le
  have e3 := mul_le_mul_of_nonneg_left w3 hs.le
  have e4 := mul_le_mul_of_nonneg_left w4 hs.le
  simp only [Complex.mem_reProdIm, mem_Ioo, affineC_re, affineC_im, l319Corner]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

/-- the region of a site, in coordinates: `|x − centre| < (1/10 + 13/280) s` -/
lemma l319LocReg_center {j : ℕ} {b : ℂ} {c₀ : ℤ} {z : ℤ × ℤ} {x : ℂ}
    (hx : x ∈ affineC ((2 : ℝ)⁻¹ ^ j) (l319Corner ((2 : ℝ)⁻¹ ^ j) b c₀ z) ''
      thickening (1 / 10) (closedBall l319U l319r)) :
    |x.re - (b.re + (2 : ℝ)⁻¹ ^ j / 32 * ((c₀ + z.1 : ℤ) : ℝ) + (2 : ℝ)⁻¹ ^ j / 64)| <
        (2 : ℝ)⁻¹ ^ j * (1 / 10 + 13 / 280) ∧
      |x.im - (b.im + (2 : ℝ)⁻¹ ^ j / 32 * ((c₀ + z.2 : ℤ) : ℝ) + (2 : ℝ)⁻¹ ^ j / 64)| <
        (2 : ℝ)⁻¹ ^ j * (1 / 10 + 13 / 280) := by
  set s : ℝ := (2 : ℝ)⁻¹ ^ j
  have hs : 0 < s := by positivity
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨v, hv, hd⟩ := Metric.mem_thickening_iff.1 hw
  rw [mem_closedBall, dist_eq_norm] at hv
  rw [dist_eq_norm] at hd
  have hwu : ‖w - l319U‖ < 1 / 10 + 13 / 280 := by
    have := norm_sub_le_norm_sub_add_norm_sub w v l319U
    simp only [l319r] at hv; linarith
  have er : (affineC s (l319Corner s b c₀ z) w).re -
      (b.re + s / 32 * ((c₀ + z.1 : ℤ) : ℝ) + s / 64) = s * (w.re - 1 / 2) := by
    simp only [affineC_re, l319Corner]; ring
  have ei : (affineC s (l319Corner s b c₀ z) w).im -
      (b.im + s / 32 * ((c₀ + z.2 : ℤ) : ℝ) + s / 64) = s * (w.im - 1 / 2) := by
    simp only [affineC_im, l319Corner]; ring
  rw [er, ei, abs_mul, abs_mul, abs_of_pos hs]
  have h1 : |w.re - 1 / 2| < 1 / 10 + 13 / 280 := lt_of_le_of_lt (abs_re_sub_le (u := l319U)) hwu
  have h2 : |w.im - 1 / 2| < 1 / 10 + 13 / 280 := lt_of_le_of_lt (abs_im_sub_le (u := l319U)) hwu
  exact ⟨mul_lt_mul_of_pos_left h1 hs, mul_lt_mul_of_pos_left h2 hs⟩

/-- **DG:1656 (as DG:1267–1276)**: the regions of sites at `ℓ^∞`-distance `> 9` are disjoint -/
lemma l319LocReg_disjoint {j : ℕ} {b : ℂ} {c₀ : ℤ} {x y : ℤ × ℤ} (hxy : PercFar 9 x y) :
    Disjoint (l319LocReg j (l319Corner ((2 : ℝ)⁻¹ ^ j) b c₀ x))
      (l319LocReg j (l319Corner ((2 : ℝ)⁻¹ ^ j) b c₀ y)) := by
  rw [Set.disjoint_left]
  rintro ⟨t, z⟩ hx hy
  obtain ⟨-, hx⟩ := hx
  obtain ⟨-, hy⟩ := hy
  have h1 := l319LocReg_center hx
  have h2 := l319LocReg_center hy
  set s : ℝ := (2 : ℝ)⁻¹ ^ j
  have hs : 0 < s := by positivity
  simp only [abs_lt] at h1 h2
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h1
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := h2
  unfold PercFar at hxy
  have key : ∀ p q : ℤ, (9 : ℤ) < p - q →
      s / 32 * 10 ≤ s / 32 * ((c₀ + p : ℤ) : ℝ) - s / 32 * ((c₀ + q : ℤ) : ℝ) := by
    intro p q h
    have : (10 : ℝ) ≤ ((c₀ + p : ℤ) : ℝ) - ((c₀ + q : ℤ) : ℝ) := by
      have : (10 : ℤ) ≤ (c₀ + p) - (c₀ + q) := by omega
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ s / 32)
    linarith
  rcases hxy with h | h | h | h
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith
  · have := key _ _ h; nlinarith

/-- the index set of the exceptional event: `[−48n, 48n]²` -/
def l319Idx (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(48 * n : ℤ)) (48 * n) ×ˢ Finset.Icc (-(48 * n : ℤ)) (48 * n)

lemma mem_l319Idx {n : ℕ} {z : ℤ × ℤ} (hz : l319Site n z) : z ∈ l319Idx n := by
  obtain ⟨d, ⟨h1, h2, h3, h4⟩, -⟩ := hz
  simp only [l319Idx, Finset.mem_product, Finset.mem_Icc]
  omega

lemma card_l319Idx (n : ℕ) : ((l319Idx n).card : ℝ) ≤ 9409 * ((n : ℝ) + 1) ^ 2 := by
  simp only [l319Idx, Finset.card_product, Int.card_Icc]
  have e : (48 * (n : ℤ) + 1 - -(48 * n)).toNat = 96 * n + 1 := by omega
  rw [e]
  push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- the fixed unit-frame inclusions -/
lemma l319_hDK : closedBall l319U l319r ⊆ interior l311K0 := by
  unfold l311K0 ferniqueBox
  rw [Complex.interior_reProdIm]; simp only [interior_Icc]
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hr := abs_le.1 (abs_re_sub_le.trans hw)
  have hi := abs_le.1 (abs_im_sub_le.trans hw)
  simp only [l319U, l319r] at hr hi
  simp only [Complex.mem_reProdIm, mem_Ioo]
  norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma l319_hR : closedBall l319U (1 / 10) ⊆ l311K0 := by
  unfold l311K0 ferniqueBox
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hr := abs_le.1 (abs_re_sub_le.trans hw)
  have hi := abs_le.1 (abs_im_sub_le.trans hw)
  simp only [l319U] at hr hi
  simp only [Complex.mem_reProdIm, mem_Icc]
  norm_num
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

end DG
end LQGMetric
