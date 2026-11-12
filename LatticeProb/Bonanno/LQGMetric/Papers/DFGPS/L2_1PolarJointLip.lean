/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarJointLip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyLip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Joint Lipschitz bounds for the heat-kernel truncation differences in `(s, z)`

Towards the joint (in `(ε, z)`) existence and continuity of `g*_ε(z)` (node `Lem2_1HeatJoint`,
see `L2_1PolarCont.lean`): the route of `Field/HeatMollifyKolm`/`HeatMollifyUnif` (Kolmogorov +
Borel–Cantelli + Weierstrass M-test), with the parameter `z` replaced by `(s, z)`. This file
supplies the deterministic input: for `s, s' ∈ [a, b] ⊂ (0, ∞)`, `‖z‖, ‖z'‖ ≤ r`,
`|D_n(s,z)(w) − D_n(s',z')(w)| ≤ L e^{−n} (|s − s'| + ‖z − z'‖)` where
`D_n(s,z) = p_s(z,·)(χ_{n+1} − χ_n)` (`abs_heatDiff_sub_sz_le`). Own elementary estimate (mean
value theorem in `s`, Gaussian tail), as for the `z`-Lipschitz bound of `HeatMollifyLip`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

/-- the `s`-Lipschitz constant on `[a, b]`, `‖z‖ ≤ r` -/
def heatLipS (a b r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((a ^ 2)⁻¹ + (a ^ 3)⁻¹) * Real.exp (2 * b) * Real.exp r

lemma heatLipS_nonneg {a : ℝ} (ha : 0 < a) (b r : ℝ) : 0 ≤ heatLipS a b r := by
  unfold heatLipS; positivity

lemma heatKernel_eq_inv_mul (x : ℝ) (z w : ℂ) :
    heatKernel x z w = (2 * Real.pi)⁻¹ * (x⁻¹ * Real.exp (-(‖z - w‖ ^ 2 / 2) * x⁻¹)) := by
  unfold heatKernel
  rw [mul_inv, mul_assoc]
  congr 3
  ring

/-- **`s`-Lipschitz bound** of the heat kernel away from `z`. -/
lemma abs_heatKernel_sub_s_le {a b r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) {s s' : ℝ}
    (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) (z w : ℂ) (hz : ‖z‖ ≤ r) (n : ℕ)
    (hw : (n : ℝ) + 1 ≤ ‖w‖) :
    |heatKernel s z w - heatKernel s' z w| ≤
      heatLipS a b r * Real.exp (-(n : ℝ)) * |s - s'| := by
  set t := ‖z - w‖
  set T := t ^ 2 / 2
  have hT : 0 ≤ T := by positivity
  have ht : (n : ℝ) + 1 - r ≤ t := by
    have := norm_sub_norm_le w z; rw [norm_sub_rev] at this; simp only [t]; linarith
  set f : ℝ → ℝ := fun x => (2 * Real.pi)⁻¹ * (x⁻¹ * Real.exp (-T * x⁻¹))
  set f' : ℝ → ℝ := fun x => (2 * Real.pi)⁻¹ * (-(x ^ 2)⁻¹ * Real.exp (-T * x⁻¹) +
    x⁻¹ * (Real.exp (-T * x⁻¹) * (-T * -(x ^ 2)⁻¹)))
  have hder : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x := by
    intro x hx
    have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
    have h1 := hasDerivAt_inv hx0
    have h2 := ((hasDerivAt_inv hx0).const_mul (-T)).exp
    exact ((h1.mul h2).const_mul _).hasDerivWithinAt
  set C := heatLipS a b r * Real.exp (-(n : ℝ))
  have hbound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ C := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    set E := Real.exp (-T * x⁻¹)
    have hE0 : 0 < E := Real.exp_pos _
    have he : f' x = (2 * Real.pi)⁻¹ * (-(x ^ 2)⁻¹ * E + (x ^ 3)⁻¹ * T * E) := by
      simp only [f', E]; field_simp
    have hx2 : (x ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hx.1 2)
    have hx3 : (x ^ 3)⁻¹ ≤ (a ^ 3)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hx.1 3)
    have hb0 : 0 < b := hx0.trans_le hx.2
    -- `E ≤ e^{−T/b}`
    have hEb : E ≤ Real.exp (-(t ^ 2 / (2 * b))) := by
      refine Real.exp_le_exp.2 ?_
      have : T / b ≤ T * x⁻¹ := by
        rw [← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hT hx0 hx.2
      have e : t ^ 2 / (2 * b) = T / b := by simp only [T]; field_simp
      rw [e]; linarith
    have hq : 1 + T ≤ Real.exp t := by
      have := Real.quadratic_le_exp_of_nonneg (norm_nonneg (z - w))
      simp only [T, t] at this ⊢; linarith [norm_nonneg (z - w)]
    have hg : Real.exp (-(t ^ 2 / (2 * b))) ≤ Real.exp (2 * b - 2 * t) := by
      apply Real.exp_le_exp.2
      rw [neg_le, neg_sub, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (t - 2 * b)]
    have hkey : (1 + T) * E ≤ Real.exp (2 * b) * Real.exp r * Real.exp (-(n : ℝ)) := by
      calc (1 + T) * E ≤ Real.exp t * Real.exp (2 * b - 2 * t) :=
            mul_le_mul hq (hEb.trans hg) hE0.le (Real.exp_pos _).le
        _ = Real.exp (2 * b - t) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (2 * b + r + -(n : ℝ)) := Real.exp_le_exp.2 (by linarith)
        _ = _ := by rw [Real.exp_add, Real.exp_add]
    rw [he, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have habs : |-(x ^ 2)⁻¹ * E + (x ^ 3)⁻¹ * T * E| ≤ ((a ^ 2)⁻¹ + (a ^ 3)⁻¹) * ((1 + T) * E) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_neg, abs_of_pos (by positivity), abs_of_pos hE0,
        abs_of_nonneg (by positivity)]
      have h1 : (x ^ 2)⁻¹ * E ≤ (a ^ 2)⁻¹ * E := mul_le_mul_of_nonneg_right hx2 hE0.le
      have h2 : (x ^ 3)⁻¹ * T * E ≤ (a ^ 3)⁻¹ * T * E := by gcongr
      have h3 : 0 ≤ (a ^ 3)⁻¹ * E := by positivity
      have h4 : 0 ≤ (a ^ 2)⁻¹ * T * E := by positivity
      nlinarith
    calc (2 * Real.pi)⁻¹ * |-(x ^ 2)⁻¹ * E + (x ^ 3)⁻¹ * T * E|
        ≤ (2 * Real.pi)⁻¹ * (((a ^ 2)⁻¹ + (a ^ 3)⁻¹) *
            (Real.exp (2 * b) * Real.exp r * Real.exp (-(n : ℝ)))) := by
          gcongr
          exact habs.trans (mul_le_mul_of_nonneg_left hkey (by positivity))
      _ = C := by simp only [C, heatLipS]; ring
  have hmvt := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound hs' hs
  have hf : ∀ x, heatKernel x z w = f x := fun x => by
    rw [heatKernel_eq_inv_mul]
  rw [hf, hf, ← Real.norm_eq_abs, ← Real.norm_eq_abs (s - s')]
  exact hmvt

/-- `heatLipConst` is uniformly bounded for `s ∈ [a, b]` -/
def heatLipZ (a b r : ℝ) : ℝ :=
  (2 * Real.pi * a)⁻¹ * (2 * a)⁻¹ * Real.exp (2 * b) * (2 * (1 + r)) * Real.exp r

lemma heatLipConst_le {a b r s : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hs : s ∈ Icc a b) :
    heatLipConst s r ≤ heatLipZ a b r := by
  unfold heatLipConst heatLipZ
  have hs0 : 0 < s := ha.trans_le hs.1
  have h1 : (2 * Real.pi * s)⁻¹ ≤ (2 * Real.pi * a)⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos, hs.1])
  have h2 : (2 * s)⁻¹ ≤ (2 * a)⁻¹ := inv_anti₀ (by positivity) (by linarith [hs.1])
  have h3 : Real.exp (2 * s) ≤ Real.exp (2 * b) := Real.exp_le_exp.2 (by linarith [hs.2])
  gcongr

/-- **Joint Lipschitz bound** of the truncation differences in `(s, z)`. -/
lemma abs_heatDiff_sub_sz_le {a b r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) {s s' : ℝ}
    (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) (z z' : ℂ) (hz : ‖z‖ ≤ r) (hz' : ‖z'‖ ≤ r) (n : ℕ)
    (w : ℂ) : |heatDiff s z n w - heatDiff s' z' n w| ≤
      (heatLipZ a b r + heatLipS a b r) * Real.exp (-(n : ℝ)) * (|s - s'| + ‖z - z'‖) := by
  have hs0 : 0 < s := ha.trans_le hs.1
  have hLZ : 0 ≤ heatLipZ a b r := (heatLipConst_nonneg s r hs0 hr).trans (heatLipConst_le ha hr hs)
  have hLS := heatLipS_nonneg ha b r
  have h1 : |heatDiff s z n w - heatDiff s z' n w| ≤
      heatLipZ a b r * Real.exp (-(n : ℝ)) * ‖z - z'‖ :=
    (abs_heatDiff_sub_le s hs0 r hr z z' hz hz' n w).trans (by
      gcongr; exact heatLipConst_le ha hr hs)
  have h2 : |heatDiff s z' n w - heatDiff s' z' n w| ≤
      heatLipS a b r * Real.exp (-(n : ℝ)) * |s - s'| := by
    by_cases hw : ‖w‖ ≤ (n : ℝ) + 1
    · have e1 : heatDiff s z' n w = 0 := heatTrunc_succ_sub_eq_zero s z' n w hw
      have e2 : heatDiff s' z' n w = 0 := heatTrunc_succ_sub_eq_zero s' z' n w hw
      rw [e1, e2, sub_zero, abs_zero]; positivity
    push Not at hw
    rw [heatDiff_apply, heatDiff_apply, ← sub_mul, abs_mul]
    have hc : |(cutoff (n + 1) : ℂ → ℝ) w - (cutoff n : ℂ → ℝ) w| ≤ 1 := by
      have := (cutoff (n + 1)).nonneg (x := w); have := (cutoff (n + 1)).le_one (x := w)
      have := (cutoff n).nonneg (x := w); have := (cutoff n).le_one (x := w)
      rw [abs_le]; constructor <;> linarith
    exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans
      (abs_heatKernel_sub_s_le ha hr hs hs' z' w hz' n hw.le)
  calc |heatDiff s z n w - heatDiff s' z' n w|
      ≤ |heatDiff s z n w - heatDiff s z' n w| + |heatDiff s z' n w - heatDiff s' z' n w| :=
        abs_sub_le _ _ _
    _ ≤ heatLipZ a b r * Real.exp (-(n : ℝ)) * ‖z - z'‖ +
        heatLipS a b r * Real.exp (-(n : ℝ)) * |s - s'| := add_le_add h1 h2
    _ ≤ _ := by
        have hA : 0 ≤ heatLipZ a b r * Real.exp (-(n : ℝ)) * |s - s'| := by positivity
        have hB : 0 ≤ heatLipS a b r * Real.exp (-(n : ℝ)) * ‖z - z'‖ := by positivity
        nlinarith [hA, hB]

end LQGMetric.DFGPS
