/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquare at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Dirichlet heat kernel of a square by the method of images (task P2-DDDFP29, WP-110)

DDDF Prop 29 (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex:1501–1601`) uses the
transition density `p^D_s` of Brownian motion killed on exiting `D` and the kernel comparison
(6.96) (`tightness.tex:1561`), proved there with Brownian bridges. By decision D19
(`decisions/DEC-B.md (d)`) and deviation D-DDDF-11 we only need `D = (−1,2)²` and use the explicit
image series instead: for the interval `(a, a + L)`

  `q_s(u, v) = ∑_{n ∈ ℤ} (g_s(u − v + 2nL) − g_s(u + v − 2a + 2nL))`,
  `g_s(z) = (2πs)^{-1/2} e^{−z²/(2s)}`,

(the classical method of images, e.g. Feller, *An Introduction to Probability Theory and its
Applications* II, §X.5, eq. (5.7); Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*,
Problem 2.8.8), and on the square `[a, a+L]²` the product kernel `q_s(y'₁,y₁) q_s(y'₂,y₂)`.

Main results:
* `HeatSq.abs_intervalDirKernel_sub_le`: for `u ∈ [a, a+L]`, `v ∈ [a+d, a+L−d]`, `0 < s ≤ 1`,
  `|q_s(u,v) − g_s(u−v)| ≤ 2K g_s(d)` (only the images are left, each at distance `≥ d`).
* `HeatSq.abs_sqDirKernel_sub_le`: on the square, for `y'` in the closed square and `y` at
  distance `≥ d` from its boundary (coordinatewise), `|p^D_s(y',y) − p_s(y',y)| ≤ C p_s(0,d)`
  with `p_s` the planar heat kernel `heatKernel` and `C` depending only on `d, L`.
-/

noncomputable section

open Real

namespace LQGMetric
namespace HeatSq

/-- The one-dimensional Gaussian kernel `g_s(z) = (2πs)^{-1/2} e^{−z²/(2s)}`. -/
def gauss1 (s z : ℝ) : ℝ := (Real.sqrt (2 * π * s))⁻¹ * Real.exp (-z ^ 2 / (2 * s))

lemma gauss1_nonneg (s z : ℝ) : 0 ≤ gauss1 s z := by unfold gauss1; positivity

lemma gauss1_le_gauss1_zero (s z : ℝ) (hs : 0 < s) : gauss1 s z ≤ gauss1 s 0 := by
  unfold gauss1
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  rw [show (-(0:ℝ) ^ 2 / (2 * s)) = 0 by ring, neg_div]
  exact neg_nonpos.mpr (by positivity)

/-- The planar heat kernel is the product of two one-dimensional ones. -/
lemma gauss1_mul_gauss1 (s : ℝ) (hs : 0 < s) (z w : ℂ) :
    gauss1 s (z.re - w.re) * gauss1 s (z.im - w.im) = heatKernel s z w := by
  unfold gauss1 heatKernel
  rw [mul_mul_mul_comm, ← mul_inv, Real.mul_self_sqrt (by positivity), ← Real.exp_add]
  congr 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-- Elementary exponent bound: if `d + m ≤ |w|` then `g_s(w) ≤ g_s(d) e^{−dm}` (`s ≤ 1`). -/
lemma gauss1_le_of_le_abs {s d m w : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hw : d + m ≤ |w|) : gauss1 s w ≤ gauss1 s d * Real.exp (-(d * m)) := by
  unfold gauss1
  rw [mul_assoc (Real.sqrt (2 * π * s))⁻¹, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have h1 : (d + m) ^ 2 ≤ w ^ 2 := by
    rw [← sq_abs w]; exact pow_le_pow_left₀ (by positivity) hw 2
  have h2 : d * m ≤ d * m / s := le_div_self (by positivity) hs hs1
  have h3 : (d ^ 2 + 2 * (d * m)) / (2 * s) ≤ w ^ 2 / (2 * s) := by
    gcongr; nlinarith [sq_nonneg m]
  have h4 : (d ^ 2 + 2 * (d * m)) / (2 * s) = d ^ 2 / (2 * s) + d * m / s := by
    field_simp
  rw [neg_div, neg_div]
  linarith

lemma summable_geom_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ n.natAbs) := by
  apply Summable.of_nat_of_neg
  · simpa using summable_geometric_of_lt_one hr0 hr1
  · simpa using summable_geometric_of_lt_one hr0 hr1

/-- The constant `K(d,L) = e^{2dL} ∑_{n∈ℤ} e^{−2dL|n|}` of the image-sum bound. -/
def imgConst (d L : ℝ) : ℝ :=
  Real.exp (2 * d * L) * ∑' n : ℤ, Real.exp (-(2 * d * L)) ^ n.natAbs

lemma imgConst_nonneg (d L : ℝ) : 0 ≤ imgConst d L := by
  unfold imgConst
  exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun n => by positivity)

/-- **Image sums.** If `|w_n| ≥ d` and `|w_n| ≥ d + 2L(|n| − 1)` for all `n ∈ ℤ`, then
`∑ g_s(w_n)` converges and is at most `K(d,L) g_s(d)` for `0 < s ≤ 1`. -/
theorem summable_tsum_gauss1_le {s d L : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hd : 0 < d)
    (hL : 0 < L) (w : ℤ → ℝ) (hw0 : ∀ n, d ≤ |w n|)
    (hw : ∀ n : ℤ, d + 2 * L * ((n.natAbs : ℝ) - 1) ≤ |w n|) :
    Summable (fun n => gauss1 s (w n)) ∧ ∑' n, gauss1 s (w n) ≤ imgConst d L * gauss1 s d := by
  set r := Real.exp (-(2 * d * L)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hbound : ∀ n : ℤ, gauss1 s (w n) ≤ gauss1 s d * (Real.exp (2 * d * L) * r ^ n.natAbs) := by
    intro n
    set m := max (2 * L * ((n.natAbs : ℝ) - 1)) 0
    have hm0 : 0 ≤ m := le_max_right _ _
    have hm1 : 2 * L * ((n.natAbs : ℝ) - 1) ≤ m := le_max_left _ _
    have hdm : d + m ≤ |w n| := by
      rcases le_total (2 * L * ((n.natAbs : ℝ) - 1)) 0 with h | h
      · rw [show m = 0 from max_eq_right h, add_zero]; exact hw0 n
      · rw [show m = _ from max_eq_left h]; exact hw n
    refine (gauss1_le_of_le_abs hs hs1 hd.le hm0 hdm).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (gauss1_nonneg _ _)
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hm1 hd.le]
  have hS : Summable (fun n : ℤ => gauss1 s d * (Real.exp (2 * d * L) * r ^ n.natAbs)) :=
    ((summable_geom_natAbs hr0 hr1).mul_left _).mul_left _
  have hsum : Summable (fun n => gauss1 s (w n)) :=
    Summable.of_nonneg_of_le (fun n => gauss1_nonneg _ _) hbound hS
  refine ⟨hsum, (hsum.tsum_le_tsum hbound hS).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_mul_left]
  unfold imgConst; ring

/-- Every shifted image family `n ↦ g_s(c + 2nL)` is summable (Gaussian decay). -/
theorem summable_gauss1_shift {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) :
    Summable (fun n : ℤ => gauss1 s (c + 2 * n * L)) := by
  set r := Real.exp (-(2 * L / s)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < 2 * L / s := by positivity
    linarith)
  have hbound : ∀ n : ℤ, gauss1 s (c + 2 * n * L) ≤
      (Real.sqrt (2 * π * s))⁻¹ * (Real.exp ((1 + 2 * |c|) / (2 * s)) * r ^ n.natAbs) := by
    intro n
    unfold gauss1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    set w := c + 2 * n * L
    have hn : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h1 : 2 * L * |(n : ℝ)| ≤ |w| + |c| := by
      have := abs_sub w c
      rwa [show w - c = 2 * n * L by simp only [w]; ring, abs_mul, abs_mul, abs_two,
        abs_of_pos hL, show 2 * |(n : ℝ)| * L = 2 * L * |(n : ℝ)| by ring] at this
    have h2 : 2 * |w| - 1 ≤ w ^ 2 := by nlinarith [sq_nonneg (|w| - 1), sq_abs w]
    have e : (1 + 2 * |c|) / (2 * s) + (n.natAbs : ℝ) * -(2 * L / s) =
        (1 + 2 * |c| - 4 * L * |(n : ℝ)|) / (2 * s) := by
      rw [hn]; field_simp; ring
    rw [e, neg_div, ← neg_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  exact Summable.of_nonneg_of_le (fun n => gauss1_nonneg _ _) hbound
    ((summable_geom_natAbs hr0 hr1).mul_left _ |>.mul_left _)

/-- The **Dirichlet heat kernel of the interval `(a, a+L)`** by the method of images
(Feller II §X.5 (5.7)): `q_s(u,v) = ∑_{n∈ℤ} (g_s(u − v + 2nL) − g_s(u + v − 2a + 2nL))`. -/
def intervalDirKernel (a L s u v : ℝ) : ℝ :=
  ∑' n : ℤ, (gauss1 s (u - v + 2 * n * L) - gauss1 s (u + v - 2 * a + 2 * n * L))

/-- **One-dimensional kernel comparison.** For `u ∈ [a, a+L]`, `v ∈ [a+d, a+L−d]` and
`0 < s ≤ 1`, `|q_s(u,v) − g_s(u − v)| ≤ 2 K(d,L) g_s(d)`. -/
theorem abs_intervalDirKernel_sub_le {a L s d u v : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hd : 0 < d)
    (hL : 0 < L) (hu : u ∈ Set.Icc a (a + L)) (hv : v ∈ Set.Icc (a + d) (a + L - d)) :
    |intervalDirKernel a L s u v - gauss1 s (u - v)| ≤ 2 * imgConst d L * gauss1 s d := by
  classical
  set f : ℤ → ℝ := fun n => gauss1 s (u - v + 2 * n * L)
  set g : ℤ → ℝ := fun n => gauss1 s (u + v - 2 * a + 2 * n * L)
  have hf : Summable f := summable_gauss1_shift hs hL (u - v)
  have hg : Summable g := summable_gauss1_shift hs hL (u + v - 2 * a)
  have hn1 : ∀ n : ℤ, (n.natAbs : ℝ) = |(n : ℝ)| := fun n => by rw [Nat.cast_natAbs, Int.cast_abs]
  -- the images of the first family (`n ≠ 0`)
  set w' : ℤ → ℝ := fun n => if n = 0 then d else u - v + 2 * n * L
  have huv : |u - v| ≤ L - d := abs_sub_le_iff.mpr ⟨by linarith [hu.2, hv.1], by
    linarith [hu.1, hv.2]⟩
  have hw'1 : ∀ n : ℤ, n ≠ 0 → 2 * L * (n.natAbs : ℝ) - (L - d) ≤ |u - v + 2 * n * L| := by
    intro n _
    have := abs_sub (u - v + 2 * n * L) (u - v)
    rw [show u - v + 2 * n * L - (u - v) = 2 * n * L by ring, abs_mul, abs_mul, abs_two,
      abs_of_pos hL, ← hn1] at this
    linarith
  have hT1 := summable_tsum_gauss1_le hs hs1 hd hL w'
    (fun n => by
      by_cases hn : n = 0
      · simp [w', hn, abs_of_pos hd]
      · have h1 : (1 : ℝ) ≤ n.natAbs := Nat.one_le_cast.mpr (Int.natAbs_pos.mpr hn)
        simp only [w', hn, ite_false]; nlinarith [hw'1 n hn])
    (fun n => by
      by_cases hn : n = 0
      · simp [w', hn, abs_of_pos hd]; linarith
      · have h1 : (1 : ℝ) ≤ n.natAbs := Nat.one_le_cast.mpr (Int.natAbs_pos.mpr hn)
        simp only [w', hn, ite_false]; nlinarith [hw'1 n hn])
  have hite : ∀ n : ℤ, (if n = 0 then 0 else f n) ≤ gauss1 s (w' n) := by
    intro n; by_cases hn : n = 0
    · simp [hn, gauss1_nonneg]
    · simp [hn, w', f]
  have hite0 : ∀ n : ℤ, 0 ≤ (if n = 0 then 0 else f n) := by
    intro n; by_cases hn : n = 0
    · simp [hn]
    · simp [hn, f, gauss1_nonneg]
  have hiteS : Summable (fun n : ℤ => if n = 0 then 0 else f n) :=
    Summable.of_nonneg_of_le hite0 hite hT1.1
  have hT1' : ∑' n : ℤ, (if n = 0 then 0 else f n) ≤ imgConst d L * gauss1 s d :=
    (hiteS.tsum_le_tsum hite hT1.1).trans hT1.2
  -- the images of the second family
  have hT2 := summable_tsum_gauss1_le hs hs1 hd hL (fun n => u + v - 2 * a + 2 * n * L)
    (fun n => by
      rcases le_or_gt 0 n with hn | hn
      · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
        refine le_abs.mpr (Or.inl ?_); nlinarith [hu.1, hv.1]
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        refine le_abs.mpr (Or.inr ?_); nlinarith [hu.2, hv.2])
    (fun n => by
      rw [hn1]
      rcases le_or_gt 0 n with hn | hn
      · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg hn']
        refine le_abs.mpr (Or.inl ?_); nlinarith [hu.1, hv.1]
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        rw [abs_of_neg (by linarith)]
        refine le_abs.mpr (Or.inr ?_); nlinarith [hu.2, hv.2])
  have hg0 : 0 ≤ ∑' n, g n := tsum_nonneg fun n => gauss1_nonneg _ _
  have hT2' : ∑' n, g n ≤ imgConst d L * gauss1 s d := hT2.2
  have hT10 : 0 ≤ ∑' n : ℤ, (if n = 0 then 0 else f n) := tsum_nonneg hite0
  unfold intervalDirKernel
  rw [hf.tsum_sub hg, hf.tsum_eq_add_tsum_ite 0]
  have hf0 : f 0 = gauss1 s (u - v) := by simp [f]
  rw [hf0, show gauss1 s (u - v) + ∑' n : ℤ, (if n = 0 then 0 else f n) - ∑' n, g n -
    gauss1 s (u - v) = ∑' n : ℤ, (if n = 0 then 0 else f n) - ∑' n, g n by ring]
  rw [abs_sub_le_iff]; constructor <;> linarith

/-- The **Dirichlet heat kernel of the square `(a, a+L)²`**: the product of the interval
kernels in the two coordinates. -/
def sqDirKernel (a L s : ℝ) (y' y : ℂ) : ℝ :=
  intervalDirKernel a L s y'.re y.re * intervalDirKernel a L s y'.im y.im

/-- **Kernel comparison on the square.** For `y'` in the closed square `[a,a+L]²`, `y` in
`[a+d, a+L−d]²` and `0 < s ≤ 1`: `|p^D_s(y',y) − p_s(y',y)| ≤ (4K + 4K²) p_s(d, 0)`. -/
theorem abs_sqDirKernel_sub_le {a L s d : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hd : 0 < d)
    (hL : 0 < L) {y' y : ℂ} (hy're : y'.re ∈ Set.Icc a (a + L))
    (hy'im : y'.im ∈ Set.Icc a (a + L)) (hyre : y.re ∈ Set.Icc (a + d) (a + L - d))
    (hyim : y.im ∈ Set.Icc (a + d) (a + L - d)) :
    |sqDirKernel a L s y' y - heatKernel s y' y| ≤
      (4 * imgConst d L + 4 * imgConst d L ^ 2) * heatKernel s (d : ℂ) 0 := by
  set K := imgConst d L
  have hK : 0 ≤ K := imgConst_nonneg d L
  set q1 := intervalDirKernel a L s y'.re y.re
  set q2 := intervalDirKernel a L s y'.im y.im
  set g1 := gauss1 s (y'.re - y.re)
  set g2 := gauss1 s (y'.im - y.im)
  set gd := gauss1 s d
  set A := gauss1 s 0
  set E := 2 * K * gd
  have h1 : |q1 - g1| ≤ E := abs_intervalDirKernel_sub_le hs hs1 hd hL hy're hyre
  have h2 : |q2 - g2| ≤ E := abs_intervalDirKernel_sub_le hs hs1 hd hL hy'im hyim
  have hg1A : g1 ≤ A := gauss1_le_gauss1_zero _ _ hs
  have hg2A : g2 ≤ A := gauss1_le_gauss1_zero _ _ hs
  have hgdA : gd ≤ A := gauss1_le_gauss1_zero _ _ hs
  have hg1 : 0 ≤ g1 := gauss1_nonneg _ _
  have hg2 : 0 ≤ g2 := gauss1_nonneg _ _
  have hgd : 0 ≤ gd := gauss1_nonneg _ _
  have hE : 0 ≤ E := by positivity
  have hq2 : |q2| ≤ A + E := by
    have := abs_sub_abs_le_abs_sub q2 g2
    rw [abs_of_nonneg hg2] at this; linarith
  have hheat : heatKernel s y' y = g1 * g2 := (gauss1_mul_gauss1 s hs y' y).symm
  have hheatd : heatKernel s (d : ℂ) 0 = gd * A := by
    rw [← gauss1_mul_gauss1 s hs]; simp [gd, A]
  unfold sqDirKernel
  rw [hheat, hheatd, show q1 * q2 - g1 * g2 = (q1 - g1) * q2 + g1 * (q2 - g2) by ring]
  have e1 : |(q1 - g1) * q2| ≤ E * (A + E) := by
    rw [abs_mul]; exact mul_le_mul h1 hq2 (abs_nonneg _) hE
  have e2 : |g1 * (q2 - g2)| ≤ A * E := by
    rw [abs_mul, abs_of_nonneg hg1]; exact mul_le_mul hg1A h2 (abs_nonneg _) (by linarith)
  have e3 : K ^ 2 * gd * gd ≤ K ^ 2 * gd * A := mul_le_mul_of_nonneg_left hgdA (by positivity)
  have e4 : E * (A + E) + A * E = 4 * K * gd * A + 4 * K ^ 2 * gd * gd := by
    simp only [E]; ring
  calc |(q1 - g1) * q2 + g1 * (q2 - g2)| ≤ |(q1 - g1) * q2| + |g1 * (q2 - g2)| := abs_add_le _ _
    _ ≤ E * (A + E) + A * E := add_le_add e1 e2
    _ ≤ (4 * K + 4 * K ^ 2) * (gd * A) := by nlinarith

end HeatSq
end LQGMetric
