import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Short paths in round annuli

A set of the form `D = {w ∈ ℂ : |w - c| ∈ I}`, with `I ⊆ (0, ∞)` an interval (an open or closed round annulus, a
punctured disc, the complement of a disc), has *bounded convexity* with constant `1 + 2π`: any two points `z, w ∈ D`
are joined by a continuous path `p : [0, 1] → D` from `z` to `w` whose length (total variation) is at most
`(1 + 2π) |z - w|`.

The path interpolates the modulus `|· - c|` linearly and the argument linearly along the shorter arc:
`p(t) = c + ((1 - t) |z - c| + t |w - c|) / |z - c| · (z - c) · exp(i t θ)` with `θ = arg((w - c) / (z - c))`.
The length bound rests on the chord estimate `min(|z|, |w|) · |arg(w / z)| ≤ π |z - w|` for nonzero `z, w`.

## Main results

* `LatticeProb.min_norm_mul_abs_arg_div_le`: the chord estimate.
* `LatticeProb.dist_polarPath_le`: the polar interpolation path is `(1 + 2π) |z - w|`-Lipschitz on `[0, 1]`.
* `LatticeProb.exists_path_eVariationOn_le_of_dist_mem`: bounded convexity of `{w : |w - c| ∈ I}`.
* `LatticeProb.exists_path_eVariationOn_le_annulus`: the open annulus `{s < |w - c| < r}`, `0 ≤ s`.
-/

open Complex Set

namespace LatticeProb

/-- **Chord estimate for the argument**: for `q ≠ 0`, `min(1, |q|) · |arg q| ≤ π |1 - q|`. -/
theorem min_one_norm_mul_abs_arg_le {q : ℂ} (hq : q ≠ 0) :
    min 1 ‖q‖ * |arg q| ≤ Real.pi * ‖1 - q‖ := by
  have hθ : |arg q| ≤ Real.pi := abs_arg_le_pi q
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hmin1 : min 1 ‖q‖ ≤ 1 := min_le_left _ _
  have hminq : min 1 ‖q‖ ≤ ‖q‖ := min_le_right _ _
  have hre : q.re = ‖q‖ * Real.cos (arg q) := by
    rw [cos_arg hq]
    field_simp
  have him : q.im = ‖q‖ * Real.sin (arg q) := by
    rw [sin_arg]
    field_simp
  by_cases hc : Real.cos (arg q) ≤ 0
  · -- `|1 - q| ≥ re (1 - q) = 1 - |q| cos θ ≥ 1`
    have h1 : 1 ≤ ‖1 - q‖ := by
      have h := Complex.re_le_norm (1 - q)
      rw [Complex.sub_re, Complex.one_re, hre] at h
      nlinarith [norm_nonneg q]
    calc min 1 ‖q‖ * |arg q| ≤ 1 * Real.pi := mul_le_mul hmin1 hθ (abs_nonneg _) zero_le_one
      _ ≤ Real.pi * ‖1 - q‖ := by nlinarith [Real.pi_pos]
  · -- `|θ| ≤ π/2`, so Jordan's inequality gives `|sin θ| ≥ (2/π)|θ|`
    push Not at hc
    have hθ2 : |arg q| ≤ Real.pi / 2 := by
      by_contra hlt
      push Not at hlt
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hlt.le (by linarith [Real.pi_pos])
      rw [Real.cos_abs] at this
      linarith
    have hsin : 2 / Real.pi * |arg q| ≤ |Real.sin (arg q)| := by
      refine (Real.mul_le_sin (abs_nonneg _) hθ2).trans ?_
      rcases abs_choice (arg q) with h | h
      · rw [h]
        exact le_abs_self _
      · rw [h, Real.sin_neg]
        exact neg_le_abs _
    have him' : ‖q‖ * |Real.sin (arg q)| ≤ ‖1 - q‖ := by
      have h := Complex.abs_im_le_norm (1 - q)
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, him, abs_mul, abs_norm] at h
      exact h
    have hpi : 0 < Real.pi := Real.pi_pos
    calc min 1 ‖q‖ * |arg q| ≤ ‖q‖ * |arg q| := mul_le_mul_of_nonneg_right hminq (abs_nonneg _)
      _ = Real.pi / 2 * (‖q‖ * (2 / Real.pi * |arg q|)) := by field_simp
      _ ≤ Real.pi / 2 * (‖q‖ * |Real.sin (arg q)|) := by gcongr
      _ ≤ Real.pi / 2 * ‖1 - q‖ := by gcongr
      _ ≤ Real.pi * ‖1 - q‖ := by nlinarith [norm_nonneg (1 - q)]

/-- **Chord estimate**: for nonzero `z, w`, `min(|z|, |w|) · |arg(w / z)| ≤ π |z - w|`. -/
theorem min_norm_mul_abs_arg_div_le {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    min ‖z‖ ‖w‖ * |arg (w / z)| ≤ Real.pi * ‖z - w‖ := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h := min_one_norm_mul_abs_arg_le (div_ne_zero hw hz)
  have hmin : min ‖z‖ ‖w‖ = ‖z‖ * min 1 ‖w / z‖ := by
    rw [mul_min_of_nonneg _ _ hz0.le, norm_div, mul_one, mul_div_cancel₀ _ hz0.ne']
  have hsub : ‖z - w‖ = ‖z‖ * ‖1 - w / z‖ := by
    rw [← norm_mul, mul_sub, mul_one, mul_div_cancel₀ _ hz]
  rw [hmin, hsub, mul_assoc]
  calc ‖z‖ * (min 1 ‖w / z‖ * |arg (w / z)|) ≤ ‖z‖ * (Real.pi * ‖1 - w / z‖) :=
        mul_le_mul_of_nonneg_left h hz0.le
    _ = Real.pi * (‖z‖ * ‖1 - w / z‖) := by ring

/-- The **polar interpolation path** around `c` from `z` to `w`: the modulus `|· - c|` is interpolated linearly and
the argument linearly along the shorter arc, `p(t) = c + ((1 - t)|z - c| + t|w - c|)/|z - c| · (z - c) · exp(itθ)`
with `θ = arg((w - c)/(z - c))`. -/
noncomputable def polarPath (c z w : ℂ) (t : ℝ) : ℂ :=
  c + (((1 - t) * ‖z - c‖ + t * ‖w - c‖) / ‖z - c‖ : ℝ) * (z - c) *
    exp ((t * arg ((w - c) / (z - c)) : ℝ) * I)

theorem polarPath_zero {c z : ℂ} (hz : z ≠ c) (w : ℂ) : polarPath c z w 0 = z := by
  have hz0 : ‖z - c‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
  simp [polarPath, hz0]

theorem polarPath_one {c z w : ℂ} (hz : z ≠ c) : polarPath c z w 1 = w := by
  have hzc : z - c ≠ 0 := sub_ne_zero.2 hz
  have key := norm_mul_exp_arg_mul_I ((w - c) / (z - c))
  rw [norm_div] at key
  simp only [polarPath, one_mul, sub_self, zero_mul, zero_add]
  calc c + ((‖w - c‖ / ‖z - c‖ : ℝ) : ℂ) * (z - c) * exp (↑(arg ((w - c) / (z - c))) * I)
      = c + (z - c) * (((‖w - c‖ / ‖z - c‖ : ℝ) : ℂ) * exp (↑(arg ((w - c) / (z - c))) * I)) := by ring
    _ = w := by rw [key, mul_div_cancel₀ _ hzc]; ring

/-- The modulus of the polar interpolation path is the linear interpolation of the moduli. -/
theorem norm_polarPath_sub {c z : ℂ} (hz : z ≠ c) (w : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖polarPath c z w t - c‖ = (1 - t) * ‖z - c‖ + t * ‖w - c‖ := by
  have hz0 : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have ha : 0 ≤ (1 - t) * ‖z - c‖ + t * ‖w - c‖ := by
    have := ht.1; have := ht.2; positivity
  simp only [polarPath, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_norm, abs_of_nonneg ha]
  field_simp

/-- **Lipschitz bound for the polar interpolation path**: for `z, w ≠ c` and `t, t' ∈ [0, 1]`,
`|p(t) - p(t')| ≤ (1 + 2π) |z - w| |t - t'|`. -/
theorem dist_polarPath_le {c z w : ℂ} (hz : z ≠ c) (hw : w ≠ c) {t t' : ℝ} (ht' : t' ∈ Icc (0 : ℝ) 1) :
    dist (polarPath c z w t) (polarPath c z w t') ≤ (1 + 2 * Real.pi) * dist z w * dist t t' := by
  set z' := z - c with hz'
  set w' := w - c with hw'
  have hz'0 : z' ≠ 0 := sub_ne_zero.2 hz
  have hw'0 : w' ≠ 0 := sub_ne_zero.2 hw
  have hzn : 0 < ‖z'‖ := norm_pos_iff.2 hz'0
  set θ := arg (w' / z') with hθ
  set a : ℝ → ℝ := fun s => (1 - s) * ‖z'‖ + s * ‖w'‖ with ha
  set E : ℝ → ℂ := fun s => exp ((s * θ : ℝ) * I) with hE
  have hEn : ∀ s, ‖E s‖ = 1 := fun s => norm_exp_ofReal_mul_I _
  have hEd : ‖E t - E t'‖ ≤ |t - t'| * |θ| := by
    have hsplit : E t - E t' = E t' * (exp (I * ((t - t') * θ : ℝ)) - 1) := by
      simp only [hE, mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [hsplit, norm_mul, hEn, one_mul]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
    rw [Real.norm_eq_abs, abs_mul]
  have hdiff : polarPath c z w t - polarPath c z w t' =
      ((a t - a t') / ‖z'‖ : ℝ) * z' * E t + (a t' / ‖z'‖ : ℝ) * z' * (E t - E t') := by
    simp only [polarPath, ← hz', ← hw', ← hθ, ha, hE]
    push_cast
    ring
  have hat : |a t - a t'| = |t - t'| * |‖w'‖ - ‖z'‖| := by
    rw [← abs_mul]
    congr 1
    simp only [ha]
    ring
  have hat'0 : 0 ≤ a t' := by
    have := ht'.1; have := ht'.2; simp only [ha]; positivity
  have hat'max : a t' ≤ max ‖z'‖ ‖w'‖ := by
    have := ht'.1; have := ht'.2
    simp only [ha]
    nlinarith [le_max_left ‖z'‖ ‖w'‖, le_max_right ‖z'‖ ‖w'‖]
  -- the speed bound
  have hd : ‖z' - w'‖ = dist z w := by
    rw [dist_eq_norm, hz', hw', sub_sub_sub_cancel_right]
  have hrad : |‖w'‖ - ‖z'‖| ≤ ‖z' - w'‖ := by
    exact (abs_norm_sub_norm_le w' z').trans (norm_sub_rev w' z').le
  have hchord := min_norm_mul_abs_arg_div_le hz'0 hw'0
  have hθpi : |θ| ≤ Real.pi := abs_arg_le_pi _
  have hmax : max ‖z'‖ ‖w'‖ ≤ min ‖z'‖ ‖w'‖ + |‖w'‖ - ‖z'‖| := by
    rcases le_total ‖z'‖ ‖w'‖ with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]; linarith
    · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; linarith
  have hspeed : |‖w'‖ - ‖z'‖| + max ‖z'‖ ‖w'‖ * |θ| ≤ (1 + 2 * Real.pi) * ‖z' - w'‖ := by
    have h1 : max ‖z'‖ ‖w'‖ * |θ| ≤ min ‖z'‖ ‖w'‖ * |θ| + |‖w'‖ - ‖z'‖| * |θ| := by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right hmax (abs_nonneg _)
    have h2 : |‖w'‖ - ‖z'‖| * |θ| ≤ ‖z' - w'‖ * Real.pi :=
      mul_le_mul hrad hθpi (abs_nonneg _) (norm_nonneg _)
    nlinarith [hchord]
  rw [dist_eq_norm, hdiff, Real.dist_eq, ← hd]
  calc ‖((a t - a t') / ‖z'‖ : ℝ) * z' * E t + (a t' / ‖z'‖ : ℝ) * z' * (E t - E t')‖
      ≤ ‖((a t - a t') / ‖z'‖ : ℝ) * z' * E t‖ + ‖(a t' / ‖z'‖ : ℝ) * z' * (E t - E t')‖ := norm_add_le _ _
    _ = |a t - a t'| + a t' * ‖E t - E t'‖ := by
        simp only [norm_mul, hEn, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_nonneg hat'0]
        field_simp
    _ ≤ |t - t'| * |‖w'‖ - ‖z'‖| + max ‖z'‖ ‖w'‖ * (|t - t'| * |θ|) := by
        rw [hat]
        gcongr
    _ = |t - t'| * (|‖w'‖ - ‖z'‖| + max ‖z'‖ ‖w'‖ * |θ|) := by ring
    _ ≤ |t - t'| * ((1 + 2 * Real.pi) * ‖z' - w'‖) := by gcongr
    _ = (1 + 2 * Real.pi) * ‖z' - w'‖ * |t - t'| := by ring

/-- **Bounded convexity of round annuli.** Let `I ⊆ (0, ∞)` be order-connected (an interval) and
`D = {w : |w - c| ∈ I}`. Any two points `z, w ∈ D` are joined by a continuous path `p : [0, 1] → D` from `z` to `w`
of length (total variation on `[0, 1]`) at most `(1 + 2π) |z - w|`. -/
theorem exists_path_eVariationOn_le_of_dist_mem (c : ℂ) {I : Set ℝ} (hI : I.OrdConnected)
    (hI0 : ∀ ρ ∈ I, 0 < ρ) {z w : ℂ} (hz : dist z c ∈ I) (hw : dist w c ∈ I) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = z ∧ p 1 = w ∧
      MapsTo p (Icc 0 1) {v | dist v c ∈ I} ∧
      eVariationOn p (Icc 0 1) ≤ ENNReal.ofReal ((1 + 2 * Real.pi) * dist z w) := by
  have hzc : z ≠ c := fun h => (hI0 _ hz).ne' (by rw [h, dist_self])
  have hwc : w ≠ c := fun h => (hI0 _ hw).ne' (by rw [h, dist_self])
  set K : NNReal := Real.toNNReal ((1 + 2 * Real.pi) * dist z w) with hK
  have hK0 : 0 ≤ (1 + 2 * Real.pi) * dist z w := by
    have := Real.pi_pos; positivity
  have hlip : LipschitzOnWith K (polarPath c z w) (Icc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun t _ t' ht' => ?_
    rw [hK, Real.coe_toNNReal _ hK0]
    exact dist_polarPath_le hzc hwc ht'
  refine ⟨polarPath c z w, hlip.continuousOn, polarPath_zero hzc w, polarPath_one hzc, fun t ht => ?_, ?_⟩
  · show dist (polarPath c z w t) c ∈ I
    rw [dist_eq_norm, norm_polarPath_sub hzc w ht, ← dist_eq_norm, ← dist_eq_norm]
    exact hI.convex hz hw (by linarith [ht.2]) ht.1 (by ring)
  · have h1 := hlip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1) (mapsTo_id _)
    have h2 : eVariationOn (id : ℝ → ℝ) (Icc 0 1) ≤ ENNReal.ofReal (1 - 0) := by
      have := (MonotoneOn.eVariationOn_eq (f := (id : ℝ → ℝ)) (s := Icc (0 : ℝ) 1) monotoneOn_id
        (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)).le
      rwa [inter_self] at this
    rw [sub_zero, ENNReal.ofReal_one] at h2
    calc eVariationOn (polarPath c z w) (Icc 0 1) = eVariationOn (polarPath c z w ∘ id) (Icc 0 1) := rfl
      _ ≤ K * eVariationOn id (Icc 0 1) := h1
      _ ≤ K * 1 := by gcongr
      _ = ENNReal.ofReal ((1 + 2 * Real.pi) * dist z w) := by rw [mul_one]; rfl

/-- **Bounded convexity of an open round annulus** `{v : s < |v - c| < r}` with `0 ≤ s`, with constant `1 + 2π`. -/
theorem exists_path_eVariationOn_le_annulus (c : ℂ) {s r : ℝ} (hs : 0 ≤ s) {z w : ℂ}
    (hz : z ∈ {v : ℂ | s < dist v c ∧ dist v c < r}) (hw : w ∈ {v : ℂ | s < dist v c ∧ dist v c < r}) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = z ∧ p 1 = w ∧
      MapsTo p (Icc 0 1) {v : ℂ | s < dist v c ∧ dist v c < r} ∧
      eVariationOn p (Icc 0 1) ≤ ENNReal.ofReal ((1 + 2 * Real.pi) * dist z w) :=
  exists_path_eVariationOn_le_of_dist_mem c (I := Ioo s r) ordConnected_Ioo
    (fun _ hρ => hs.trans_lt hρ.1) hz hw

end LatticeProb
