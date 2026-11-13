/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.KoebeLoewner at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeHalfPlane

/-!
# Distortion of a univalent map of the half-plane along vertical and horizontal moves
(EXT-RS node KD(a): Kemppainen Lemma 6.6)

A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24 (2017)
(`literature/Kemppainen_SLE_2017.pdf`; not arXiv:1012.4797, which is Sheffield's paper),
Lemma 6.6, p. 110
(proof in Appendix D) states the distortion of a conformal map `f` of the upper half-plane `ℍ`
along the two families of moves used by the Loewner flow: a vertical rescaling `iy ↦ isy`,
`s ∈ [1/2,2]`, and a horizontal move `iy ↦ y(x+i)`. With the sharp Koebe constants of the cited
proof both ratios are bounded by a constant times `(1+x²)³`.

Here we *chain* the two-sided Koebe derivative-ratio estimate `CA.Koebe.deriv_ratio_le` (K5b,
non-sharp exponent `koebeDistExp`) along `O(log(1+|x|))` Whitney steps of the half-plane,

* up the imaginary axis from `iy` to `iy2^n` with `2^n ≥ 1+|x|` (each doubling is two K5b steps),
* across at height `y2^n` (two K5b steps, since the displacement is `y|x| ≤ y2^n`),
* back down to `y(x+i)`;

the total loss is `K^{4n+2}` with `K = 2^koebeDistExp`, which is `≤ C(1+x²)^C` for the explicit
constant `C = 256^m + 2m + 1` of `kdConst`, `m = ⌈koebeDistExp⌉`. This is our own elementary
chaining of K5b with non-sharp constants (the exponent is `2m` instead of Kemppainen's `3`).

`kd_distortion` is the `(a)` part of node KD of `blueprint/EXT_RS_BLUEPRINT.md`; the Loewner-time
part KD(b) (Kemppainen Lemma 6.7) is not proved here.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology Real

namespace QuantumZipper.RS

open QuantumZipper.CA
open QuantumZipper.CA.Koebe

/-- `K = 2 ^ koebeDistExp`: the one-step derivative ratio of `Koebe.deriv_ratio_le` (K5b). -/
def koebeStepConst : ℝ := 2 ^ koebeDistExp

theorem one_le_koebeStepConst : 1 ≤ koebeStepConst := by
  rw [koebeStepConst]
  exact Real.one_le_rpow (by norm_num) koebeDistExp_pos.le

theorem le_koebeStepConst_sq : koebeStepConst ≤ koebeStepConst ^ 2 := by
  rw [sq]
  calc koebeStepConst = koebeStepConst * 1 := (mul_one _).symm
    _ ≤ koebeStepConst * koebeStepConst :=
        mul_le_mul_of_nonneg_left one_le_koebeStepConst (le_trans zero_le_one one_le_koebeStepConst)

/-! ## Two elementary steps of the Koebe chaining -/

/-- Two K5b steps: `‖f'u‖ ≤ K²‖f'z‖` and `‖f'z‖ ≤ K²‖f'u‖`, where each step stays inside the
Whitney ball of its starting point. -/
theorem deriv_ratio_le_two {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {z w u : ℂ} (hz : 0 < z.im)
    (h1 : dist w z ≤ z.im / 2) (h2 : dist u w ≤ w.im / 2) :
    ‖deriv f u‖ ≤ koebeStepConst ^ 2 * ‖deriv f z‖ ∧
    ‖deriv f z‖ ≤ koebeStepConst ^ 2 * ‖deriv f u‖ := by
  have hw : 0 < w.im := by
    have hle : |w.im - z.im| ≤ z.im / 2 := by
      have h := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, ← dist_eq_norm] at h
      exact h.trans h1
    linarith [(abs_le.1 hle).1]
  rw [koebeStepConst]
  obtain ⟨ha, hb⟩ := Koebe.deriv_ratio_le hd hinj hz h1
  obtain ⟨hc, hd'⟩ := Koebe.deriv_ratio_le hd hinj hw h2
  have hK : (0:ℝ) ≤ 2 ^ koebeDistExp := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  constructor
  · calc ‖deriv f u‖ ≤ 2 ^ koebeDistExp * ‖deriv f w‖ := hc
      _ ≤ 2 ^ koebeDistExp * (2 ^ koebeDistExp * ‖deriv f z‖) :=
          mul_le_mul_of_nonneg_left ha hK
      _ = (2 ^ koebeDistExp) ^ 2 * ‖deriv f z‖ := by ring
  · calc ‖deriv f z‖ ≤ 2 ^ koebeDistExp * ‖deriv f w‖ := hb
      _ ≤ 2 ^ koebeDistExp * (2 ^ koebeDistExp * ‖deriv f u‖) :=
          mul_le_mul_of_nonneg_left hd' hK
      _ = (2 ^ koebeDistExp) ^ 2 * ‖deriv f u‖ := by ring

/-! ## Points and distances on the dyadic vertical chain -/

/-- The point `a + i·y·2^j` of the dyadic vertical chain. -/
def zp (a y : ℝ) (j : ℕ) : ℂ := (a : ℂ) + ((y * 2 ^ j : ℝ) : ℂ) * I

theorem zp_zero (a y : ℝ) : zp a y 0 = (a : ℂ) + (y : ℂ) * I := by
  simp [zp]

theorem im_zp (a y : ℝ) (j : ℕ) : (zp a y j).im = y * 2 ^ j := by
  simp only [zp, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_add]

theorem dist_zp (a y₁ y₂ : ℝ) (j₁ j₂ : ℕ) :
    dist (zp a y₁ j₁) (zp a y₂ j₂) = |y₁ * 2 ^ j₁ - y₂ * 2 ^ j₂| := by
  rw [dist_eq_norm]
  have h : zp a y₁ j₁ - zp a y₂ j₂ = (((y₁ * 2 ^ j₁ - y₂ * 2 ^ j₂ : ℝ)) : ℂ) * I := by
    simp only [zp, Complex.ofReal_sub]
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem dist_mul_I_mul_I (a b : ℝ) : dist ((a : ℂ) * I) ((b : ℂ) * I) = |a - b| := by
  rw [dist_eq_norm]
  have h : (a : ℂ) * I - (b : ℂ) * I = ((a - b : ℝ) : ℂ) * I := by
    rw [Complex.ofReal_sub]
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem im_mul_I (a : ℝ) : ((a : ℂ) * I).im = a := by simp

theorem im_ofReal_add_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).im = b := by
  simp [Complex.add_im]

theorem dist_ofReal_add_mul_I_left (b a a' : ℝ) :
    dist ((a : ℂ) + (b : ℂ) * I) ((a' : ℂ) + (b : ℂ) * I) = |a - a'| := by
  rw [dist_eq_norm]
  have h : (a : ℂ) + (b : ℂ) * I - ((a' : ℂ) + (b : ℂ) * I) = ((a - a' : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

theorem dist_ofReal_add_mul_I_bare (b a : ℝ) :
    dist ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I) = |a| := by
  rw [dist_eq_norm]
  have h : (a : ℂ) + (b : ℂ) * I - (b : ℂ) * I = (a : ℂ) := by ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-! ## Vertical moves `iy ↦ isy`, `s ∈ [1/2, 2]` -/

/-- `iy ↦ isy` for `s ∈ [1/2,2]`: one K5b step when `s ≤ 3/2`, two otherwise. -/
theorem deriv_ratio_le_vertical {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {y s : ℝ} (hy : 0 < y) (hs1 : 1 / 2 ≤ s)
    (hs2 : s ≤ 2) :
    ‖deriv f ((s * y : ℝ) * Complex.I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f ((y : ℂ) * Complex.I)‖ ∧
    ‖deriv f ((y : ℂ) * Complex.I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f ((s * y : ℝ) * Complex.I)‖ := by
  rcases le_or_gt s (3 / 2) with hs | hs
  · have hz : 0 < ((y : ℂ) * I).im := by rw [im_mul_I]; exact hy
    have hdist : dist ((s * y : ℝ) * I) ((y : ℂ) * I) ≤ ((y : ℂ) * I).im / 2 := by
      rw [dist_mul_I_mul_I, im_mul_I]
      have h1 : |s - 1| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      have h2 : |s * y - y| = |s - 1| * y := by
        rw [show s * y - y = (s - 1) * y by ring, abs_mul, abs_of_pos hy]
      rw [h2]
      nlinarith
    obtain ⟨ha, hb⟩ := Koebe.deriv_ratio_le hd hinj hz hdist
    exact ⟨ha.trans (mul_le_mul_of_nonneg_right le_koebeStepConst_sq (norm_nonneg _)),
      hb.trans (mul_le_mul_of_nonneg_right le_koebeStepConst_sq (norm_nonneg _))⟩
  · have hz : 0 < ((y : ℂ) * I).im := by rw [im_mul_I]; exact hy
    have hw : 0 < (((3 / 2 * y : ℝ) : ℂ) * I).im := by rw [im_mul_I]; positivity
    have h1 : dist (((3 / 2 * y : ℝ) : ℂ) * I) ((y : ℂ) * I) ≤ ((y : ℂ) * I).im / 2 := by
      rw [dist_mul_I_mul_I, im_mul_I]
      have h2 : |3 / 2 * y - y| = y / 2 := by
        rw [show (3:ℝ) / 2 * y - y = y / 2 by ring, abs_of_nonneg (by positivity)]
      rw [h2]
    have h2 : dist ((s * y : ℝ) * I) (((3 / 2 * y : ℝ) : ℂ) * I)
        ≤ (((3 / 2 * y : ℝ) : ℂ) * I).im / 2 := by
      rw [dist_mul_I_mul_I, im_mul_I]
      have h3 : |s * y - 3 / 2 * y| = (s - 3 / 2) * y := by
        rw [show (s:ℝ) * y - 3 / 2 * y = (s - 3 / 2) * y by ring,
          abs_of_nonneg (by nlinarith)]
      rw [h3]
      nlinarith
    exact deriv_ratio_le_two hd hinj hz h1 h2

/-! ## The vertical dyadic chain -/

/-- A doubling of the height costs two K5b steps. -/
theorem deriv_ratio_le_double {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {a y : ℝ} (hy : 0 < y) (j : ℕ) :
    ‖deriv f (zp a y (j + 1))‖ ≤ koebeStepConst ^ 2 * ‖deriv f (zp a y j)‖ ∧
    ‖deriv f (zp a y j)‖ ≤ koebeStepConst ^ 2 * ‖deriv f (zp a y (j + 1))‖ := by
  have hz : 0 < (zp a y j).im := by rw [im_zp]; positivity
  have h1 : dist (zp a (3 * y / 2) j) (zp a y j) ≤ (zp a y j).im / 2 := by
    rw [dist_zp, im_zp]
    have h2 : 3 * y / 2 * 2 ^ j - y * 2 ^ j = y * 2 ^ j / 2 := by ring
    rw [h2, abs_of_nonneg (by positivity)]
  have h2 : dist (zp a y (j + 1)) (zp a (3 * y / 2) j) ≤ (zp a (3 * y / 2) j).im / 2 := by
    rw [dist_zp, im_zp]
    have hp : (2:ℝ) ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
    have h3 : y * 2 ^ (j + 1) - 3 * y / 2 * 2 ^ j = y * 2 ^ j / 2 := by
      rw [hp]; ring
    rw [h3, abs_of_nonneg (by positivity)]
    have h4 : 3 * y / 2 * 2 ^ j = 3 * (y * 2 ^ j) / 2 := by ring
    rw [h4]
    linarith [show (0:ℝ) < y * 2 ^ j by positivity]
  exact deriv_ratio_le_two hd hinj hz h1 h2

/-- Chaining `n` doublings of the height at fixed real part `a`. -/
theorem deriv_ratio_le_scale {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {a y : ℝ} (hy : 0 < y) (n : ℕ) :
    ‖deriv f (zp a y n)‖ ≤ (koebeStepConst ^ 2) ^ n * ‖deriv f (zp a y 0)‖ ∧
    ‖deriv f (zp a y 0)‖ ≤ (koebeStepConst ^ 2) ^ n * ‖deriv f (zp a y n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨h1, h2⟩ := deriv_ratio_le_double hd hinj hy n
    refine ⟨?_, ?_⟩
    · calc ‖deriv f (zp a y (n + 1))‖ ≤ koebeStepConst ^ 2 * ‖deriv f (zp a y n)‖ := h1
        _ ≤ koebeStepConst ^ 2 * ((koebeStepConst ^ 2) ^ n * ‖deriv f (zp a y 0)‖) :=
            mul_le_mul_of_nonneg_left ih1 (by positivity)
        _ = (koebeStepConst ^ 2) ^ (n + 1) * ‖deriv f (zp a y 0)‖ := by
            rw [pow_succ]; ring
    · calc ‖deriv f (zp a y 0)‖ ≤ (koebeStepConst ^ 2) ^ n * ‖deriv f (zp a y n)‖ := ih2
        _ ≤ (koebeStepConst ^ 2) ^ n * (koebeStepConst ^ 2 * ‖deriv f (zp a y (n + 1))‖) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (koebeStepConst ^ 2) ^ (n + 1) * ‖deriv f (zp a y (n + 1))‖ := by
            rw [pow_succ]; ring

/-- The horizontal move `iH ↦ yx + iH` at height `H`, in two K5b steps (the displacement `y|x|`
is at most `H`). -/
theorem deriv_ratio_le_horiz {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {y x H : ℝ} (hy : 0 < y) (hH : 0 < H)
    (hxy : y * |x| ≤ H) :
    ‖deriv f (((y * x : ℝ) : ℂ) + (H : ℂ) * I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f ((H : ℂ) * I)‖ ∧
    ‖deriv f ((H : ℂ) * I)‖ ≤ koebeStepConst ^ 2 * ‖deriv f (((y * x : ℝ) : ℂ) + (H : ℂ) * I)‖ := by
  have hz : 0 < ((H : ℂ) * I).im := by rw [im_mul_I]; exact hH
  have hstep : dist (((y * x / 2 : ℝ) : ℂ) + (H : ℂ) * I) ((H : ℂ) * I) ≤ ((H : ℂ) * I).im / 2 := by
    rw [dist_ofReal_add_mul_I_bare, im_mul_I]
    have h2 : |y * x / 2| = y * |x| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hy, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [h2]
    linarith
  have hstep2 : dist (((y * x : ℝ) : ℂ) + (H : ℂ) * I) (((y * x / 2 : ℝ) : ℂ) + (H : ℂ) * I)
      ≤ (((y * x / 2 : ℝ) : ℂ) + (H : ℂ) * I).im / 2 := by
    rw [dist_ofReal_add_mul_I_left, im_ofReal_add_mul_I]
    have h2 : |y * x - y * x / 2| = y * |x| / 2 := by
      rw [show y * x - y * x / 2 = y * x / 2 by ring, abs_div, abs_mul, abs_of_pos hy]
      ring
    rw [h2]
    linarith
  exact deriv_ratio_le_two hd hinj hz hstep hstep2

/-- The exponent identity `(K²)^n · K² · (K²)^n = K^{4n+2}`. -/
theorem pow_four_mul_add_two (K : ℝ) (n : ℕ) :
    (K ^ 2) ^ n * K ^ 2 * (K ^ 2) ^ n = K ^ (4 * n + 2) := by
  have h1 : (K ^ 2) ^ n = K ^ (2 * n) := (pow_mul K 2 n).symm
  rw [h1, ← pow_add K (2 * n) 2, ← pow_add K (2 * n + 2) (2 * n)]
  congr 1
  omega

/-- **The distortion of `f` from `iy` to `y(x+i)`**: `K^{4n+2}` where `2^n ≥ 1+|x|`. -/
theorem deriv_ratio_le_full {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im})
    (hinj : InjOn f {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) {x : ℝ} {n : ℕ}
    (hn : 1 + |x| ≤ (2:ℝ) ^ n) :
    ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ ≤ koebeStepConst ^ (4 * n + 2) * ‖deriv f ((y : ℂ) * I)‖ ∧
    ‖deriv f ((y : ℂ) * I)‖ ≤ koebeStepConst ^ (4 * n + 2) * ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ := by
  have hH : 0 < y * 2 ^ n := by positivity
  have hxy : y * |x| ≤ y * 2 ^ n := by
    refine mul_le_mul_of_nonneg_left ?_ hy.le
    linarith [le_abs_self x]
  obtain ⟨hu1, hu2⟩ := deriv_ratio_le_scale (a := 0) hd hinj hy n
  obtain ⟨hd1, hd2⟩ := deriv_ratio_le_scale (a := y * x) hd hinj hy n
  obtain ⟨hh1, hh2⟩ := deriv_ratio_le_horiz hd hinj hy hH hxy
  have hzp0n : zp 0 y n = ((y * 2 ^ n : ℝ) : ℂ) * I := by simp [zp]
  have hzp00 : zp 0 y 0 = (y : ℂ) * I := by simp [zp]
  have hzpan : zp (y * x) y n = ((y * x : ℝ) : ℂ) + ((y * 2 ^ n : ℝ) : ℂ) * I := by simp [zp]
  have hzpa0 : zp (y * x) y 0 = (y : ℂ) * ((x : ℂ) + I) := by
    rw [zp_zero, mul_add, ← Complex.ofReal_mul]
  have hzpan' : ((y * x : ℝ) : ℂ) + ((y * 2 ^ n : ℝ) : ℂ) * I = zp (y * x) y n := hzpan.symm
  have hzp0n' : ((y * 2 ^ n : ℝ) : ℂ) * I = zp 0 y n := hzp0n.symm
  have hK : (0:ℝ) ≤ koebeStepConst ^ 2 := by positivity
  constructor
  · calc ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ = ‖deriv f (zp (y * x) y 0)‖ := by rw [hzpa0]
      _ ≤ (koebeStepConst ^ 2) ^ n * ‖deriv f (zp (y * x) y n)‖ := hd2
      _ = (koebeStepConst ^ 2) ^ n *
            ‖deriv f (((y * x : ℝ) : ℂ) + ((y * 2 ^ n : ℝ) : ℂ) * I)‖ := by rw [hzpan]
      _ ≤ (koebeStepConst ^ 2) ^ n * (koebeStepConst ^ 2 * ‖deriv f (((y * 2 ^ n : ℝ) : ℂ) * I)‖) :=
            mul_le_mul_of_nonneg_left hh1 (by positivity)
      _ = (koebeStepConst ^ 2) ^ n * (koebeStepConst ^ 2 * ‖deriv f (zp 0 y n)‖) := by rw [hzp0n]
      _ ≤ (koebeStepConst ^ 2) ^ n *
            (koebeStepConst ^ 2 * ((koebeStepConst ^ 2) ^ n * ‖deriv f (zp 0 y 0)‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu1 (by positivity)) (by positivity)
      _ = (koebeStepConst ^ 2) ^ n *
            (koebeStepConst ^ 2 * ((koebeStepConst ^ 2) ^ n * ‖deriv f ((y : ℂ) * I)‖)) := by
            rw [hzp00]
      _ = ((koebeStepConst ^ 2) ^ n * koebeStepConst ^ 2 * (koebeStepConst ^ 2) ^ n) *
            ‖deriv f ((y : ℂ) * I)‖ := by ring
      _ = koebeStepConst ^ (4 * n + 2) * ‖deriv f ((y : ℂ) * I)‖ := by
            rw [pow_four_mul_add_two]
  · calc ‖deriv f ((y : ℂ) * I)‖ = ‖deriv f (zp 0 y 0)‖ := by rw [hzp00]
      _ ≤ (koebeStepConst ^ 2) ^ n * ‖deriv f (zp 0 y n)‖ := hu2
      _ = (koebeStepConst ^ 2) ^ n * ‖deriv f (((y * 2 ^ n : ℝ) : ℂ) * I)‖ := by rw [hzp0n]
      _ ≤ (koebeStepConst ^ 2) ^ n * (koebeStepConst ^ 2 * ‖deriv f (((y * x : ℝ) : ℂ) + ((y * 2 ^ n : ℝ) : ℂ) * I)‖) :=
            mul_le_mul_of_nonneg_left hh2 (by positivity)
      _ = (koebeStepConst ^ 2) ^ n * (koebeStepConst ^ 2 * ‖deriv f (zp (y * x) y n)‖) := by
            rw [hzpan']
      _ ≤ (koebeStepConst ^ 2) ^ n *
            (koebeStepConst ^ 2 * ((koebeStepConst ^ 2) ^ n * ‖deriv f (zp (y * x) y 0)‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd1 (by positivity)) (by positivity)
      _ = (koebeStepConst ^ 2) ^ n *
            (koebeStepConst ^ 2 * ((koebeStepConst ^ 2) ^ n * ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖)) := by
            rw [hzpa0]
      _ = ((koebeStepConst ^ 2) ^ n * koebeStepConst ^ 2 * (koebeStepConst ^ 2) ^ n) *
            ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ := by ring
      _ = koebeStepConst ^ (4 * n + 2) * ‖deriv f ((y : ℂ) * ((x : ℂ) + I))‖ := by
            rw [pow_four_mul_add_two]

/-! ## The constant of `kd_distortion` -/

/-- A natural number dominating `koebeDistExp`. -/
def kdNatExp : ℕ := ⌈koebeDistExp⌉₊

/-- The constant `C = 256^m + 2m + 1`, `m = ⌈koebeDistExp⌉`, of `kd_distortion`: it dominates
both `K²` (`K = koebeStepConst`) and the exponent `2m` needed for the horizontal move. -/
def kdConst : ℝ := (256 : ℝ) ^ kdNatExp + 2 * (kdNatExp : ℝ) + 1

theorem one_le_kdConst : 1 ≤ kdConst := by
  have h1 : (0:ℝ) ≤ (256 : ℝ) ^ kdNatExp := by positivity
  have h2 : (0:ℝ) ≤ 2 * (kdNatExp : ℝ) := by positivity
  unfold kdConst; linarith

theorem pow_kdNatExp_le_kdConst : (256 : ℝ) ^ kdNatExp ≤ kdConst := by
  have h1 : (0:ℝ) ≤ 2 * (kdNatExp : ℝ) := by positivity
  unfold kdConst; linarith

theorem two_mul_kdNatExp_le_kdConst : 2 * (kdNatExp : ℝ) ≤ kdConst := by
  have h1 : (0:ℝ) ≤ (256 : ℝ) ^ kdNatExp := by positivity
  unfold kdConst; linarith

theorem koebeStepConst_le_two_pow : koebeStepConst ≤ (2 : ℝ) ^ kdNatExp := by
  have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (Nat.le_ceil koebeDistExp)
  rw [Real.rpow_natCast] at h
  exact h

theorem sq_koebeStepConst_le_kdConst : koebeStepConst ^ 2 ≤ kdConst := by
  have h1 : koebeStepConst ^ 2 ≤ (4 : ℝ) ^ kdNatExp := by
    calc koebeStepConst ^ 2 ≤ ((2 : ℝ) ^ kdNatExp) ^ 2 :=
          pow_le_pow_left₀ (le_trans zero_le_one one_le_koebeStepConst) koebeStepConst_le_two_pow 2
      _ = (2 : ℝ) ^ kdNatExp * (2 : ℝ) ^ kdNatExp := by ring
      _ = ((2 : ℝ) * 2) ^ kdNatExp := (mul_pow (2:ℝ) 2 kdNatExp).symm
      _ = (4 : ℝ) ^ kdNatExp := by rw [show (2:ℝ) * 2 = 4 by norm_num]
  calc koebeStepConst ^ 2 ≤ (4 : ℝ) ^ kdNatExp := h1
    _ ≤ (256 : ℝ) ^ kdNatExp := pow_le_pow_left₀ (by norm_num) (by norm_num) kdNatExp
    _ ≤ kdConst := pow_kdNatExp_le_kdConst

/-- If `2^n` is the least power of two exceeding `1+|x|`, then `2^n ≤ 2(1+|x|)`. -/
theorem two_pow_le_of_min {x : ℝ} {n : ℕ}
    (hmin : ∀ j < n, ¬ (1 + |x| < (2:ℝ) ^ j)) : (2:ℝ) ^ n ≤ 2 * (1 + |x|) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [pow_zero]
    linarith [abs_nonneg x]
  · have hlt : n - 1 < n := by omega
    have h1 : ¬ (1 + |x| < (2:ℝ) ^ (n - 1)) := hmin (n - 1) hlt
    have h2 : (2:ℝ) ^ (n - 1) ≤ 1 + |x| := le_of_not_gt h1
    calc (2:ℝ) ^ n = (2:ℝ) ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hpos]
      _ = (2:ℝ) ^ (n - 1) * 2 := pow_succ _ _
      _ = (2:ℝ) ^ (n - 1) * 2 := pow_succ _ _
      _ ≤ (1 + |x|) * 2 := by linarith
      _ = 2 * (1 + |x|) := by ring

/-- The Koebe factor `K^{4n+2}` of `deriv_ratio_le_full` is at most `C(1+x²)^C`. -/
theorem step_pow_le_kdConst {x : ℝ} {n : ℕ} (hn2 : (2:ℝ) ^ n ≤ 2 * (1 + |x|)) :
    koebeStepConst ^ (4 * n + 2) ≤ kdConst * (1 + x ^ 2) ^ kdConst := by
  have hbase : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
  have h2n : (2:ℝ) ^ (4 * n + 2) ≤ 256 * (1 + x ^ 2) ^ 2 := by
    have h24 : (2:ℝ) ^ (4 * n + 2) = 4 * ((2:ℝ) ^ n) ^ 4 := by
      rw [show 4 * n + 2 = 2 + 4 * n by omega, pow_add]
      rw [show 4 * n = n * 4 by omega, ← pow_mul]
      norm_num
    have h32 : ((2:ℝ) ^ n) ^ 4 ≤ (2 * (1 + |x|)) ^ 4 := pow_le_pow_left₀ (by positivity) hn2 4
    have h34 : (1 + |x|) ^ 4 ≤ 4 * (1 + x ^ 2) ^ 2 := by
      have h4 : ((1 + |x|) ^ 2) ^ 2 ≤ (2 * (1 + x ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
      have h5 : (2 * (1 + x ^ 2)) ^ 2 = 4 * (1 + x ^ 2) ^ 2 := by rw [mul_pow]; norm_num
      rw [← pow_mul, show (2:ℕ) * 2 = 4 by norm_num] at h4
      rw [h5] at h4
      exact h4
    calc (2:ℝ) ^ (4 * n + 2) = 4 * ((2:ℝ) ^ n) ^ 4 := h24
      _ ≤ 4 * (2 * (1 + |x|)) ^ 4 := by linarith
      _ = 64 * (1 + |x|) ^ 4 := by ring
      _ ≤ 64 * (4 * (1 + x ^ 2) ^ 2) := by linarith
      _ = 256 * (1 + x ^ 2) ^ 2 := by ring
  calc koebeStepConst ^ (4 * n + 2)
      ≤ ((2 : ℝ) ^ kdNatExp) ^ (4 * n + 2) :=
        pow_le_pow_left₀ (le_trans zero_le_one one_le_koebeStepConst) koebeStepConst_le_two_pow _
    _ = ((2 : ℝ) ^ (4 * n + 2)) ^ kdNatExp := by
        rw [← pow_mul (2:ℝ) kdNatExp (4 * n + 2),
          ← pow_mul (2:ℝ) (4 * n + 2) kdNatExp, Nat.mul_comm]
    _ ≤ (256 * (1 + x ^ 2) ^ 2) ^ kdNatExp := pow_le_pow_left₀ (by positivity) h2n _
    _ = (256 : ℝ) ^ kdNatExp * ((1 + x ^ 2) ^ 2) ^ kdNatExp := mul_pow _ _ _
    _ = (256 : ℝ) ^ kdNatExp * (1 + x ^ 2) ^ (2 * kdNatExp) := by
        rw [← pow_mul (1 + x ^ 2) 2 kdNatExp]
    _ ≤ (256 : ℝ) ^ kdNatExp * (1 + x ^ 2) ^ kdConst := by
        have hexp : ((2 * kdNatExp : ℕ) : ℝ) ≤ kdConst := by
          have h := two_mul_kdNatExp_le_kdConst
          push_cast
          linarith
        have h := Real.rpow_le_rpow_of_exponent_le hbase hexp
        rw [Real.rpow_natCast] at h
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ kdConst * (1 + x ^ 2) ^ kdConst :=
        mul_le_mul_of_nonneg_right pow_kdNatExp_le_kdConst (by positivity)

/-- **KD(a) (Kemppainen Lemma 6.6, non-sharp constants).** There is a constant `C ≥ 1` such
that for every injective holomorphic `f` on the upper half-plane, every `y > 0`, every
`s ∈ [1/2, 2]` and every `x ∈ ℝ`:
`‖f'(isy)‖ ≤ C‖f'(iy)‖`, `‖f'(iy)‖ ≤ C‖f'(isy)‖` and
`‖f'(y(x+i))‖ ≤ C(1+x²)^C‖f'(iy)‖`, `‖f'(iy)‖ ≤ C(1+x²)^C‖f'(y(x+i))‖`.
Own elementary chaining of `Koebe.deriv_ratio_le` (K5b) with non-sharp constants. -/
theorem kd_distortion : ∃ C : ℝ, 1 ≤ C ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f {z : ℂ | 0 < z.im} →
    Set.InjOn f {z : ℂ | 0 < z.im} → ∀ y : ℝ, 0 < y → ∀ x : ℝ,
      (∀ s ∈ Set.Icc (1 / 2 : ℝ) 2,
        ‖deriv f ((s * y : ℝ) * Complex.I)‖ ≤ C * ‖deriv f ((y : ℂ) * Complex.I)‖ ∧
        ‖deriv f ((y : ℂ) * Complex.I)‖ ≤ C * ‖deriv f ((s * y : ℝ) * Complex.I)‖) ∧
      ‖deriv f ((y : ℂ) * ((x : ℂ) + Complex.I))‖ ≤
        C * (1 + x ^ 2) ^ C * ‖deriv f ((y : ℂ) * Complex.I)‖ ∧
      ‖deriv f ((y : ℂ) * Complex.I)‖ ≤
        C * (1 + x ^ 2) ^ C * ‖deriv f ((y : ℂ) * ((x : ℂ) + Complex.I))‖ := by
  refine ⟨kdConst, one_le_kdConst, fun f hd hinj y hy x => ?_⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, (1 + |x| ≤ (2:ℝ) ^ n) ∧ ∀ j < n, ¬ (1 + |x| < (2:ℝ) ^ j) := by
    have hex : ∃ n : ℕ, 1 + |x| < (2:ℝ) ^ n :=
      pow_unbounded_of_one_lt (1 + |x|) (by norm_num)
    exact ⟨Nat.find hex, (Nat.find_spec hex).le, fun j hj => Nat.find_min hex hj⟩
  obtain ⟨hf1, hf2⟩ := deriv_ratio_le_full hd hinj hy hn
  have hstep := step_pow_le_kdConst (two_pow_le_of_min hmin)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hv1, hv2⟩ := deriv_ratio_le_vertical hd hinj hy hs.1 hs.2
    exact ⟨hv1.trans (mul_le_mul_of_nonneg_right sq_koebeStepConst_le_kdConst (norm_nonneg _)),
      hv2.trans (mul_le_mul_of_nonneg_right sq_koebeStepConst_le_kdConst (norm_nonneg _))⟩
  · exact hf1.trans (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))
  · exact hf2.trans (mul_le_mul_of_nonneg_right hstep (norm_nonneg _))

end QuantumZipper.RS
