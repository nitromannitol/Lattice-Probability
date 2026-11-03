/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.RGeometry at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Core.CellInterfaces

/-!
# Route M,: planar geometry for Lemma R and Lemma D″

(the separation argument, Details (c), (d3)). Pure planar
geometry, no graphs:

* normalized coordinates `tmplCoord z r ϑ w = (w - z) / (r e^{iϑ})`, in which the moved template
  `CellularEmbedding.movedTemplate z r ϑ` becomes the clamped polar template `tmplPt` (TF3 §8: "normalize z = 0,
  r = 1, ϑ = 0");
* the explicit form of the polar template on its radial piece (`tmplPt_radial`, a positive real in `[0.9, 1.1]`) and
  on its final piece (`tmplPt_final`, `exp (i (4s/5 - 7/10))`);
* logarithm bookkeeping (`eq_of_exp_eq_of_abs_im_sub_lt`, `eq_add_two_pi_I_of_exp_eq`), used with TFJ's sector rule
  `logIncr_eq_log_sub_log` (`RouteM/JWinding.lean`);
* the auxiliary spiral `auxSpiral` of Lemma R (TF3 §8 step 1): a path from `Pp` to `Pm` the long way round the unit
  circle, and the location of every point within `1/1000` of it (`auxSpiral_near`): in the annulus
  `0.98 < |·| < 1.02`, off the radial region `{re > 22/25, |im| < 1/60}`, and off the ray `[0, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open Set Real
open MatedCRTHarmonic.Topology

namespace MatedCRTHarmonic.RouteM

/-! ### Normalized coordinates -/

/-- The similarity factor `r e^{iϑ}` of the moved polar template. -/
def tmplFactor (r ϑ : ℝ) : ℂ := (r : ℂ) * Complex.exp ((ϑ : ℂ) * Complex.I)

theorem norm_tmplFactor {r : ℝ} (hr : 0 < r) (ϑ : ℝ) : ‖tmplFactor r ϑ‖ = r := by
  rw [tmplFactor, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

theorem tmplFactor_ne_zero {r : ℝ} (hr : 0 < r) (ϑ : ℝ) : tmplFactor r ϑ ≠ 0 := by
  intro h
  have h' := norm_tmplFactor hr ϑ
  rw [h, norm_zero] at h'
  linarith

/-- Normalized coordinates `w ↦ (w - z) / (r e^{iϑ})`: the moved template becomes the polar template. -/
def tmplCoord (z : ℂ) (r ϑ : ℝ) (w : ℂ) : ℂ := (w - z) / tmplFactor r ϑ

/-- The polar template clamped to `ℝ` (`Set.projIcc`), as in `CellularEmbedding.movedTemplate`. -/
def tmplPt (s : ℝ) : ℂ := polarTemplate (Set.projIcc 0 1 zero_le_one s)

theorem movedTemplate_eq (z : ℂ) (r ϑ s : ℝ) :
    CellularEmbedding.movedTemplate z r ϑ s = z + tmplFactor r ϑ * tmplPt s := rfl

theorem tmplCoord_movedTemplate {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ s : ℝ) :
    tmplCoord z r ϑ (CellularEmbedding.movedTemplate z r ϑ s) = tmplPt s := by
  rw [movedTemplate_eq, tmplCoord, add_sub_cancel_left,
    mul_div_cancel_left₀ _ (tmplFactor_ne_zero hr ϑ)]

theorem norm_tmplCoord_sub {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ : ℝ) (w w' : ℂ) :
    ‖tmplCoord z r ϑ w - tmplCoord z r ϑ w'‖ = ‖w - w'‖ / r := by
  rw [tmplCoord, tmplCoord, ← sub_div, sub_sub_sub_cancel_right, norm_div, norm_tmplFactor hr]

theorem norm_tmplCoord {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ : ℝ) (w : ℂ) :
    ‖tmplCoord z r ϑ w‖ = ‖w - z‖ / r := by
  rw [tmplCoord, norm_div, norm_tmplFactor hr]

theorem norm_tmplCoord_sub_tmplPt {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ s : ℝ) (w : ℂ) :
    ‖tmplCoord z r ϑ w - tmplPt s‖ = ‖w - CellularEmbedding.movedTemplate z r ϑ s‖ / r := by
  rw [← tmplCoord_movedTemplate hr z ϑ s, norm_tmplCoord_sub hr]

/-- `(w - z) / (r e^{iϑ} c) = tmplCoord w / c`. -/
theorem sub_div_tmplFactor_mul (z : ℂ) (r ϑ : ℝ) (w c : ℂ) :
    (w - z) / (tmplFactor r ϑ * c) = tmplCoord z r ϑ w / c := by
  rw [tmplCoord, div_div]

theorem tmplCoord_add_mul {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ : ℝ) (c : ℂ) :
    tmplCoord z r ϑ (z + tmplFactor r ϑ * c) = c := by
  rw [tmplCoord, add_sub_cancel_left, mul_div_cancel_left₀ _ (tmplFactor_ne_zero hr ϑ)]

theorem add_mul_tmplCoord {r : ℝ} (hr : 0 < r) (z : ℂ) (ϑ : ℝ) (w : ℂ) :
    z + tmplFactor r ϑ * tmplCoord z r ϑ w = w := by
  rw [tmplCoord, mul_div_cancel₀ _ (tmplFactor_ne_zero hr ϑ), add_sub_cancel]

theorem inv_mul_sub_eq_tmplCoord (z : ℂ) (r ϑ : ℝ) (w : ℂ) :
    (tmplFactor r ϑ)⁻¹ * (w - z) = tmplCoord z r ϑ w := by
  rw [tmplCoord, div_eq_inv_mul]

/-! ### The polar template on its pieces -/

theorem tmplPt_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    tmplPt s = ((polarRadius (4 * s) : ℝ) : ℂ) *
      Complex.exp (((polarAngle (4 * s) : ℝ) : ℂ) * Complex.I) := by
  rw [tmplPt, Set.projIcc_of_mem _ ⟨h0, h1⟩]
  rfl

/-- On the radial piece `s ∈ [1/4, 1/2]` the template is the positive real `7/10 + 4s/5 ∈ [0.9, 1.1]`. -/
theorem tmplPt_radial {s : ℝ} (h1 : 1 / 4 ≤ s) (h2 : s ≤ 1 / 2) :
    tmplPt s = ((7 / 10 + 4 / 5 * s : ℝ) : ℂ) := by
  rw [tmplPt_of_mem (by linarith) (by linarith), polarAngle_eq_zero_on_radial (by linarith)]
  have hr : polarRadius (4 * s) = 7 / 10 + 4 / 5 * s := by
    unfold polarRadius
    rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  rw [hr]
  simp

/-- On the final piece `s ∈ [3/4, 1]` the template is `exp (i (4s/5 - 7/10))`, an angle in `[-1/10, 1/10]`. -/
theorem tmplPt_final {s : ℝ} (h1 : 3 / 4 ≤ s) (h2 : s ≤ 1) :
    tmplPt s = Complex.exp (((4 / 5 * s - 7 / 10 : ℝ) : ℂ) * Complex.I) := by
  rw [tmplPt_of_mem (by linarith) h2]
  have hr : polarRadius (4 * s) = 1 := by
    unfold polarRadius
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  have hθ : polarAngle (4 * s) = (4 / 5 * s - 7 / 10) + 2 * π := by
    unfold polarAngle
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  rw [hr, hθ, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  have h2pi : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * π : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]

/-- The template radius on `[0, 1]` is in `[9/10, 11/10]`. -/
theorem polarRadius_four_mul_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    9 / 10 ≤ polarRadius (4 * s) ∧ polarRadius (4 * s) ≤ 11 / 10 :=
  polarRadius_bounds (by linarith) (by linarith)

theorem norm_tmplPt_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖tmplPt s‖ = polarRadius (4 * s) := by
  rw [tmplPt_of_mem h0 h1, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith [(polarRadius_four_mul_bounds h0 h1).1])]

/-- Increments of the two kinks of `polarAngle` (auxiliary). -/
theorem polarAngle_kink_aux {u u' : ℝ} (huu : u ≤ u') :
    0 ≤ max (u' - 2) 0 - max (u - 2) 0 ∧ max (u' - 2) 0 - max (u - 2) 0 ≤ u' - u ∧
      0 ≤ max (u' - 3) 0 - max (u - 3) 0 ∧
      max (u' - 3) 0 - max (u - 3) 0 ≤ max (u' - 2) 0 - max (u - 2) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [max_le_max_right 0 (show u - 2 ≤ u' - 2 by linarith)]
  · have := max_le (show u' - 2 ≤ max (u - 2) 0 + (u' - u) by linarith [le_max_left (u - 2) 0])
      (show (0 : ℝ) ≤ max (u - 2) 0 + (u' - u) by linarith [le_max_right (u - 2) 0])
    linarith
  · linarith [max_le_max_right 0 (show u - 3 ≤ u' - 3 by linarith)]
  · rcases le_total u' 3 with h4 | h4
    · rw [max_eq_right (show u' - 3 ≤ 0 by linarith)]
      linarith [max_le_max_right 0 (show u - 2 ≤ u' - 2 by linarith), le_max_right (u - 3) 0]
    · rw [max_eq_left (show 0 ≤ u' - 3 by linarith), max_eq_left (show 0 ≤ u' - 2 by linarith)]
      have := max_le (show u - 2 ≤ 1 + max (u - 3) 0 by linarith [le_max_left (u - 3) 0])
        (show (0 : ℝ) ≤ 1 + max (u - 3) 0 by linarith [le_max_right (u - 3) 0])
      linarith

/-- The polar angle is monotone. -/
theorem polarAngle_mono {u u' : ℝ} (huu : u ≤ u') : polarAngle u ≤ polarAngle u' := by
  have hpi := Real.pi_gt_three
  obtain ⟨hA0, -, hB0, hBA⟩ := polarAngle_kink_aux huu
  unfold polarAngle
  have h1 : (2 * π - 3 / 10) * (max (u' - 3) 0 - max (u - 3) 0) ≤
      (2 * π - 3 / 10) * (max (u' - 2) 0 - max (u - 2) 0) :=
    mul_le_mul_of_nonneg_left hBA (by linarith)
  have h2 : 0 ≤ (1 / 5) * (max (u' - 2) 0 - max (u - 2) 0) := mul_nonneg (by norm_num) hA0
  nlinarith

/-- The polar angle is `7`-Lipschitz (its slopes are `0`, `2π - 1/10` and `1/5`). -/
theorem polarAngle_sub_le {u u' : ℝ} (huu : u ≤ u') : polarAngle u' - polarAngle u ≤ 7 * (u' - u) := by
  have hpi := Real.pi_lt_d2
  have hpi3 := Real.pi_gt_three
  obtain ⟨hA0, hA, hB0, -⟩ := polarAngle_kink_aux huu
  unfold polarAngle
  have h1 : (2 * π - 1 / 10) * (max (u' - 2) 0 - max (u - 2) 0) ≤ (2 * π - 1 / 10) * (u' - u) :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : 0 ≤ (2 * π - 3 / 10) * (max (u' - 3) 0 - max (u - 3) 0) := mul_nonneg (by linarith) hB0
  have h3 : (2 * π - 1 / 10) * (u' - u) ≤ 7 * (u' - u) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-! ### Logarithm bookkeeping -/

/-- Two logarithms of the same number whose imaginary parts differ by less than `2π` are equal. -/
theorem eq_of_exp_eq_of_abs_im_sub_lt {a b : ℂ} (h : Complex.exp a = Complex.exp b)
    (him : |a.im - b.im| < 2 * π) : a = b := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hmim : a.im - b.im = m * (2 * π) := by
    rw [hm]
    simp
  have hpi := Real.pi_pos
  have hm0 : m = 0 := by
    rw [hmim, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * π)] at him
    have h1 : |(m : ℝ)| < 1 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have h2 : |m| < 1 := by exact_mod_cast h1
    rw [abs_lt] at h2
    omega
  rw [hm, hm0]
  simp

/-- Two logarithms of the same number whose imaginary parts differ by an amount in `(0, 4π)` differ by `2πi`. -/
theorem eq_add_two_pi_I_of_exp_eq {a b : ℂ} (h : Complex.exp a = Complex.exp b) (h1 : 0 < a.im - b.im)
    (h2 : a.im - b.im < 4 * π) : a = b + 2 * π * Complex.I := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hmim : a.im - b.im = m * (2 * π) := by
    rw [hm]
    simp
  have hpi := Real.pi_pos
  have hm1 : m = 1 := by
    rw [hmim] at h1 h2
    have h3 : (0 : ℝ) < m := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have h4 : (m : ℝ) < 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have h3' : 0 < m := by exact_mod_cast h3
    have h4' : m < 2 := by exact_mod_cast h4
    omega
  rw [hm, hm1]
  simp

/-- `log R + iΘ` is a logarithm of `R e^{iΘ}` (`R > 0`). -/
theorem exp_log_add_mul_I {R : ℝ} (hR : 0 < R) (Θ : ℝ) :
    Complex.exp ((Real.log R : ℂ) + (Θ : ℂ) * Complex.I) =
      (R : ℂ) * Complex.exp ((Θ : ℂ) * Complex.I) := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hR]

/-! ### The auxiliary spiral of Lemma R -/

/-- The spiral `t ↦ ((1-t)|Pp| + t|Pm|) exp (i ((1-t) arg Pp + t (arg Pm + 2π)))` from `Pp` to `Pm`, the long way
round the unit circle (TF3 §8 step 1, with the two radial segments and the arc merged into one path). -/
def auxSpiral (Pp Pm : ℂ) (t : ℝ) : ℂ :=
  (((1 - t) * ‖Pp‖ + t * ‖Pm‖ : ℝ) : ℂ) *
    Complex.exp ((((1 - t) * Complex.arg Pp + t * (Complex.arg Pm + 2 * π) : ℝ) : ℂ) * Complex.I)

theorem continuous_auxSpiral (Pp Pm : ℂ) : Continuous (auxSpiral Pp Pm) := by
  unfold auxSpiral
  fun_prop

theorem auxSpiral_zero (Pp Pm : ℂ) : auxSpiral Pp Pm 0 = Pp := by
  simp only [auxSpiral, sub_zero, one_mul, zero_mul, add_zero]
  exact Complex.norm_mul_exp_arg_mul_I Pp

theorem auxSpiral_one (Pp Pm : ℂ) : auxSpiral Pp Pm 1 = Pm := by
  simp only [auxSpiral, sub_self, zero_mul, zero_add, one_mul]
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have h2pi : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * π : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [h2pi, mul_one]
  exact Complex.norm_mul_exp_arg_mul_I Pm

theorem norm_auxSpiral (Pp Pm : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖auxSpiral Pp Pm t‖ = (1 - t) * ‖Pp‖ + t * ‖Pm‖ := by
  rw [auxSpiral, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (mul_nonneg (by linarith [ht.2]) (norm_nonneg _))
      (mul_nonneg ht.1 (norm_nonneg _)))]

/-- The image of `[0,1]` under the spiral is connected. -/
theorem isConnected_auxSpiral_image (Pp Pm : ℂ) : IsConnected (auxSpiral Pp Pm '' Icc 0 1) :=
  (isConnected_Icc zero_le_one).image _ (continuous_auxSpiral Pp Pm).continuousOn

/-- If `cos φ > 0` and `φ ∈ [a, 2π - a]` with `0 ≤ a ≤ π`, then `|sin φ| ≥ sin a`. -/
theorem sin_le_abs_sin_of_cos_pos {a φ : ℝ} (ha0 : 0 ≤ a) (haπ : a ≤ π) (h1 : a ≤ φ)
    (h2 : φ ≤ 2 * π - a) (hcos : 0 < Real.cos φ) : Real.sin a ≤ |Real.sin φ| := by
  have hcle : Real.cos φ ≤ Real.cos a := by
    rcases le_total φ π with hφ | hφ
    · exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 hφ h1
    · have h' : Real.cos φ = Real.cos (2 * π - φ) := by rw [Real.cos_two_pi_sub]
      rw [h']
      exact Real.cos_le_cos_of_nonneg_of_le_pi ha0 (by linarith) (by linarith)
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0 haπ
  have hsq : Real.sin a ^ 2 ≤ Real.sin φ ^ 2 := by
    have e1 := Real.sin_sq_add_cos_sq a
    have e2 := Real.sin_sq_add_cos_sq φ
    have h3 : Real.cos φ ^ 2 ≤ Real.cos a ^ 2 := by
      have := mul_le_mul hcle hcle hcos.le (hcos.le.trans hcle)
      nlinarith
    linarith
  have h := sq_le_sq.1 hsq
  rwa [abs_of_nonneg hsa] at h

/-- **The points near the spiral** (TF3 §8 steps 1–2, with Details (c)'s margins). Let `0.983 ≤ |P±| ≤ 1.017`,
`arg Pp ≥ 1/50` and `arg Pm ≤ -1/50`. A point `w` within `1/1000` of the spiral lies in the annulus
`0.98 < |·| < 1.02`, not in the radial region `{re > 22/25, |im| < 1/60}`, and not on the ray `[0, ∞)`. -/
theorem auxSpiral_near {Pp Pm : ℂ} (hp1 : 983 / 1000 ≤ ‖Pp‖) (hp2 : ‖Pp‖ ≤ 1017 / 1000)
    (hm1 : 983 / 1000 ≤ ‖Pm‖) (hm2 : ‖Pm‖ ≤ 1017 / 1000)
    (hargp : 1 / 50 ≤ Complex.arg Pp) (hargm : Complex.arg Pm ≤ -(1 / 50))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {w : ℂ} (hw : ‖w - auxSpiral Pp Pm t‖ ≤ 1 / 1000) :
    (49 / 50 < ‖w‖ ∧ ‖w‖ < 51 / 50) ∧ ¬ (22 / 25 < w.re ∧ |w.im| < 1 / 60) ∧
      -w ∈ Complex.slitPlane := by
  obtain ⟨ht0, ht1⟩ := ht
  set ρ : ℝ := (1 - t) * ‖Pp‖ + t * ‖Pm‖ with hρ
  set φ : ℝ := (1 - t) * Complex.arg Pp + t * (Complex.arg Pm + 2 * π) with hφ
  have hc : auxSpiral Pp Pm t = (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := rfl
  have hρ1 : 983 / 1000 ≤ ρ := by
    have h1 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left hm1 ht0
    linarith
  have hρ2 : ρ ≤ 1017 / 1000 := by
    have h1 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left hm2 ht0
    linarith
  have hpi := Real.pi_gt_three
  have hφ1 : 1 / 50 ≤ φ := by
    have h1 := mul_le_mul_of_nonneg_left hargp (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left
      (show 1 / 50 ≤ Complex.arg Pm + 2 * π by linarith [Complex.neg_pi_lt_arg Pm]) ht0
    linarith
  have hφ2 : φ ≤ 2 * π - 1 / 50 := by
    have h1 := mul_le_mul_of_nonneg_left
      (show Complex.arg Pp ≤ 2 * π - 1 / 50 by linarith [Complex.arg_le_pi Pp])
      (show 0 ≤ 1 - t by linarith)
    have h2 := mul_le_mul_of_nonneg_left (show Complex.arg Pm + 2 * π ≤ 2 * π - 1 / 50 by linarith) ht0
    linarith
  set c := auxSpiral Pp Pm t with hcdef
  have hcnorm : ‖c‖ = ρ := by
    rw [hc, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hcre : c.re = ρ * Real.cos φ := by
    rw [hc, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hcim : c.im = ρ * Real.sin φ := by
    rw [hc, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hre : |w.re - c.re| ≤ 1 / 1000 := by
    have := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re] at this
    linarith
  have him : |w.im - c.im| ≤ 1 / 1000 := by
    have := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_im] at this
    linarith
  have hnorm : 49 / 50 < ‖w‖ ∧ ‖w‖ < 51 / 50 := by
    have h1 := norm_sub_norm_le c w
    have h2 := norm_sub_norm_le w c
    rw [norm_sub_rev] at h1
    constructor <;> linarith
  have hrad : ¬ (22 / 25 < w.re ∧ |w.im| < 1 / 60) := by
    rintro ⟨hwre, hwim⟩
    have hcre_pos : 0 < c.re := by
      have := (abs_le.1 hre).2
      linarith
    have hcos : 0 < Real.cos φ := by
      rw [hcre] at hcre_pos
      exact pos_of_mul_pos_right hcre_pos (by linarith)
    have hsin := sin_le_abs_sin_of_cos_pos (a := 1 / 50) (by norm_num) (by linarith) hφ1 hφ2 hcos
    have hsin0 : (1 : ℝ) / 50 - (1 / 50) ^ 3 / 6 < Real.sin (1 / 50) :=
      Real.sin_gt_sub_cube (by norm_num)
    have hcim_abs : 19 / 1000 < |c.im| := by
      rw [hcim, abs_mul, abs_of_pos (show 0 < ρ by linarith)]
      have := mul_le_mul hρ1 hsin (by linarith) (by linarith)
      nlinarith
    have h1 := abs_sub_abs_le_abs_sub c.im w.im
    rw [abs_sub_comm] at h1
    linarith
  refine ⟨hnorm, hrad, ?_⟩
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨hre0, him0⟩ := hcon
  rw [Complex.neg_re] at hre0
  rw [Complex.neg_im, neg_eq_zero] at him0
  have hwreal : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him0])
  have hwn : ‖w‖ = w.re := by
    rw [hwreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    simp
  exact hrad ⟨by linarith, by rw [him0, abs_zero]; norm_num⟩

/-- The winding of Lemma R's auxiliary loop (TF3 §8 step 3): principal angles along the final block from `Pm` to
`Pp`, the branch `arg (-·) + π` along the spiral walk back from `Pp` to `Pm`; the total turn is `2π`. -/
theorem arg_sub_add_arg_neg_sub {Pp Pm : ℂ} (hp : 0 < Pp.im) (hm : Pm.im < 0) :
    (Complex.arg Pp - Complex.arg Pm) + (Complex.arg (-Pm) - Complex.arg (-Pp)) = 2 * π := by
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hm, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hp]
  ring

/-- A point with nonnegative real part and `im ≥ |·|/50` has argument at least `1/50`. -/
theorem le_arg_of_im_ge {w : ℂ} (hw : w ≠ 0) (hre : 0 ≤ w.re) (him : ‖w‖ / 50 ≤ w.im) :
    1 / 50 ≤ Complex.arg w := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [Complex.arg_of_re_nonneg hre]
  have hsin : Real.sin (1 / 50) ≤ 1 / 50 := Real.sin_le (by norm_num)
  have hq : Real.sin (1 / 50) ≤ w.im / ‖w‖ := by
    rw [le_div_iff₀ hn]
    nlinarith
  have := Real.arcsin_le_arcsin hq
  rwa [Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])] at this

/-- A point with nonnegative real part and `im ≤ -|·|/50` has argument at most `-1/50`. -/
theorem arg_le_of_im_le {w : ℂ} (hw : w ≠ 0) (hre : 0 ≤ w.re) (him : w.im ≤ -(‖w‖ / 50)) :
    Complex.arg w ≤ -(1 / 50) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [Complex.arg_of_re_nonneg hre]
  have hsin : Real.sin (1 / 50) ≤ 1 / 50 := Real.sin_le (by norm_num)
  have hq : w.im / ‖w‖ ≤ Real.sin (-(1 / 50)) := by
    rw [Real.sin_neg, div_le_iff₀ hn]
    nlinarith
  have := Real.arcsin_le_arcsin hq
  rwa [Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])] at this

end MatedCRTHarmonic.RouteM
