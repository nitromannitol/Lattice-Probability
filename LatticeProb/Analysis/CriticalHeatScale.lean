import LatticeProb.Analysis.QuenchedCutoffEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Critical heat scale

Continuity, normalization, and growth bounds for the critical heat scale.
-/

open Set

namespace LatticeProb.Analysis.QuenchedCutoffEnergy

private lemma log_pos {r : ℝ} (hr : 0 < r) : 0 < Real.log (2 + r) :=
  Real.log_pos (by linarith)

private lemma scale_pos {r : ℝ} (hr : 0 < r) : 0 < scale r := by
  unfold scale
  exact div_pos (mul_pos (sq_pos_of_pos hr) (Real.log_pos (by norm_num))) (log_pos hr)

private lemma scale_one_private : scale 1 = 1 := by
  unfold scale
  norm_num [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3))]

private lemma log_mul_le {r R : ℝ} (hr : 0 < r) (h : r ≤ R) :
    r * Real.log (2 + R) ≤ R * Real.log (2 + r) := by
  have ha : 0 < 2 + r := by linarith
  have hb : 0 < 2 + R := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos ha
  have hl' : r ≤ (2 + r) * Real.log (2 + r) := by
    have := mul_le_mul_of_nonneg_left hl ha.le
    field_simp at this
    nlinarith
  have hd := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hd
  have hd' : (2 + r) * (Real.log (2 + R) - Real.log (2 + r)) ≤ R - r := by
    have := mul_le_mul_of_nonneg_left hd ha.le
    field_simp at this
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hd' hr.le
  have hm' := mul_le_mul_of_nonneg_left hl' (sub_nonneg.mpr h)
  nlinarith

private lemma scale_ratio_bounds_private {r R : ℝ} (hr : 0 < r) (h : r ≤ R) :
    R / r ≤ scale R / scale r ∧ scale R / scale r ≤ (R / r) ^ 2 := by
  have hR : 0 < R := lt_of_lt_of_le hr h
  have hlr := log_pos hr
  have hlR := log_pos hR
  have hc : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmono : Real.log (2 + r) ≤ Real.log (2 + R) :=
    Real.log_le_log (by linarith) (by linarith)
  have hcross := log_mul_le hr h
  constructor <;> unfold scale <;> field_simp <;> nlinarith [sq_nonneg (R-r)]

private lemma strictMonoOn_scale : StrictMonoOn scale (Ioi 0) := by
  intro r hr R hR hlt
  have hratio := (scale_ratio_bounds_private hr hlt.le).1
  have hs := scale_pos hr
  have : 1 < R / r := (one_lt_div hr).2 hlt
  have : 1 < scale R / scale r := lt_of_lt_of_le this hratio
  exact (one_lt_div hs).1 this

private lemma twice_le_log_mul {x : ℝ} (hx : 0 < x) :
    2 * x ≤ (2 + x) * Real.log (2 + x) := by
  have h := Real.le_log_one_add_of_nonneg (show 0 ≤ 1 + x by linarith)
  have hden : 0 < (1 + x) + 2 := by linarith
  have h' : 2 * (1 + x) ≤ ((1 + x) + 2) * Real.log (2 + x) := by
    have := (div_le_iff₀ hden).mp (by simpa only [show 1 + (1 + x) = 2 + x by ring] using h)
    nlinarith
  have hl : 0 ≤ Real.log (2 + x) := (Real.log_pos (by linarith)).le
  have hm := mul_le_mul_of_nonneg_left h' (show 0 ≤ 2 + x by linarith)
  have hp := mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hl
  nlinarith

private lemma log_div_sqrt_antitone :
    AntitoneOn (fun x : ℝ => Real.log (2 + x) / Real.sqrt x) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact ((continuousAt_const.add continuousAt_id).log (by change (2 : ℝ) + x ≠ 0; linarith [show 0 < x from hx])).div
      Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr hx).ne' |>.continuousWithinAt
  · rw [interior_Ioi]
    intro x hx
    exact (((hasDerivAt_const x (2 : ℝ)).add (hasDerivAt_id x)).log (by change (2 : ℝ) + x ≠ 0; linarith [show 0 < x from hx])).div
      (Real.hasDerivAt_sqrt hx.ne') (Real.sqrt_pos.mpr hx).ne' |>.differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    have hd := (((hasDerivAt_const x (2 : ℝ)).add (hasDerivAt_id x)).log (by change (2 : ℝ) + x ≠ 0; linarith [show 0 < x from hx])).div
      (Real.hasDerivAt_sqrt hx.ne') (Real.sqrt_pos.mpr hx).ne'
    simp only [Pi.add_apply, id_eq, zero_add] at hd
    change deriv ((fun y => Real.log (2 + y)) / fun y => Real.sqrt y) x ≤ 0
    rw [hd.deriv]
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have he : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
    have hl := twice_le_log_mul hx
    have hp : 0 < 2 + x := by linarith [show 0 < x from hx]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    apply (sub_nonpos.mpr _)
    have hdiv : Real.sqrt x / (2 + x) ≤ Real.log (2 + x) / (2 * Real.sqrt x) := by
      apply (div_le_div_iff₀ hp (by positivity : 0 < 2 * Real.sqrt x)).mpr
      nlinarith
    simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- The normalized logarithmic critical scale grows at least as the three-halves power. -/
theorem sharp_ratio_lower {r R : ℝ} (hr : 0 < r) (h : r ≤ R) :
    (R / r) ^ (3 / 2 : ℝ) ≤
      scale R / scale r := by
  have hR : 0 < R := lt_of_lt_of_le hr h
  have hlr : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
  have hlR : 0 < Real.log (2 + R) := Real.log_pos (by linarith)
  have hc : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsrr : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr.le
  have hsRR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR.le
  have hm := log_div_sqrt_antitone hr hR h
  have hm' := (div_le_div_iff₀ hsR hsr).mp hm
  have hp : (R / r) ^ (3 / 2 : ℝ) = (R / r) * Real.sqrt (R / r) := by
    have he : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [he, Real.rpow_add (div_pos hR hr), Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold scale
  rw [hp, Real.sqrt_div hR.le]
  field_simp
  have hm'' := mul_le_mul_of_nonneg_right hm' (le_of_lt (mul_pos hsr hsR))
  calc
    r * Real.sqrt R * Real.log (2 + R) =
        Real.log (2 + R) * Real.sqrt r * (Real.sqrt r * Real.sqrt R) := by
      calc
        _ = (Real.sqrt r) ^ 2 * Real.sqrt R * Real.log (2 + R) := by rw [hsrr]
        _ = _ := by ring
    _ ≤ Real.log (2 + r) * Real.sqrt R * (Real.sqrt r * Real.sqrt R) := hm''
    _ = R * Real.sqrt r * Real.log (2 + r) := by
      calc
        _ = (Real.sqrt R) ^ 2 * Real.sqrt r * Real.log (2 + r) := by ring
        _ = _ := by rw [hsRR]


/-- The scale is continuous on nonnegative radii. -/
theorem continuousOn_scale_nonneg : ContinuousOn scale (Ici 0) := by
  intro r hr
  change 0 ≤ r at hr
  apply ContinuousAt.continuousWithinAt
  unfold scale
  exact ((continuousAt_id.pow 2).mul continuousAt_const).div
    ((continuousAt_const.add continuousAt_id).log (by change (2 : ℝ) + r ≠ 0; linarith))
    (Real.log_pos (by linarith)).ne'

@[simp] theorem scale_zero : scale 0 = 0 := by simp [scale]

@[simp] theorem scale_one : scale 1 = 1 := scale_one_private

/-- The scale is strictly increasing on nonnegative radii. -/
theorem strictMonoOn_scale_nonneg : StrictMonoOn scale (Ici 0) := by
  intro r hr R hR hlt
  change 0 ≤ r at hr
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · rw [scale_zero]
    exact scale_pos (by linarith)
  · exact strictMonoOn_scale (show r ∈ Ioi 0 from hrpos)
      (show R ∈ Ioi 0 from lt_trans hrpos hlt) hlt

/-- The exact lower and upper power bounds for positive radii. -/
theorem scale_ratio_bounds {r R : ℝ} (hr : 0 < r) (h : r ≤ R) :
    (R / r) ^ (3 / 2 : ℝ) ≤ scale R / scale r ∧
      scale R / scale r ≤ (R / r) ^ 2 :=
  ⟨sharp_ratio_lower hr h, (scale_ratio_bounds_private hr h).2⟩

end LatticeProb.Analysis.QuenchedCutoffEnergy
