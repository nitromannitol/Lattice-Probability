/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.LogAnnulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma33

/-!
# The logarithmic harmonic function of an annulus

Source: GMS [18] proof of Lemma 3.4 ([18]: `g_s(z) = log(ρ/|z|)/log(ρ/s)` on `B_ρ(0) \ B_s(0)`,
"a direct calculation shows that the Euclidean Dirichlet energy of `g_s` on `A_s` is `2π/log(ρ/s)`") and
Step 1 of Lemma 3.8.

`logRad z a b w = (log|w − z| − log a)/log(b/a)` is `0` on `∂B_a(z)`, `1` on `∂B_b(z)` (`a, b > 0`, `a ≠ b`,
either order) and harmonic off `z`. With `L = |log(b/a)|` and `c > 0`:

* `hasFDerivAt_logRad`, `norm_fderiv_logRad`: `|∇ logRad(w)| = 1/(L |w − z|)`;
* `norm_fderiv_logRad_sub_le`: `∇ logRad` is `1/(L c²)`-Lipschitz on `{|w − z| ≥ c}` (via inversion in the
  unit circle about `z`);
* `sqGrad_le_add`, `sqGrad_le`: `|∇ logRad|² ≤ 1/(L² c²)` and is one-sidedly `2/(L² c³)`-Lipschitz there;
* `eucEnergy_logRad`: `Energy(logRad; {r₁ < |w − z| < r₂}) = 2π log(r₂/r₁)/L²`, in particular `2π/L` on
  the annulus between the radii `a` and `b` (`eucEnergy_logRad_annulus`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.GMS3

/-- The derivative of `w ↦ log|w − z|`: `⟨w − z, ·⟩ / |w − z|²`. -/
def logDistDeriv (z w : ℂ) : StrongDual ℝ ℂ := (‖w - z‖ ^ 2)⁻¹ • innerSL ℝ (w - z)

theorem hasFDerivAt_logDist {z w : ℂ} (hw : w ≠ z) :
    HasFDerivAt (fun u : ℂ => Real.log ‖u - z‖) (logDistDeriv z w) w := by
  have h1 := (hasStrictFDerivAt_norm_sq (w - z)).hasFDerivAt.comp w
    ((hasFDerivAt_id w).sub_const z)
  have hsq : HasFDerivAt (fun u : ℂ => ‖u - z‖ ^ 2) (2 • innerSL ℝ (w - z)) w := by
    refine h1.congr_fderiv ?_
    ext v
    simp
  have hne : ‖w - z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
  have hlog := (hsq.log hne).const_mul (1 / 2 : ℝ)
  refine (hlog.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  · ext v
    simp only [logDistDeriv, smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  · simp only
    rw [Real.log_pow]
    ring

theorem norm_logDistDeriv {z w : ℂ} (hw : w ≠ z) : ‖logDistDeriv z w‖ = ‖w - z‖⁻¹ := by
  unfold logDistDeriv
  have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  rw [norm_smul, innerSL_apply_norm, norm_inv, norm_pow, Real.norm_eq_abs, abs_norm]
  field_simp

/-- `|∇ log|· − z|(u) − ∇ log|· − z|(v)| = |u − v| / (|u − z| |v − z|)` (inversion about `z`). -/
theorem norm_logDistDeriv_sub {z u v : ℂ} (hu : u ≠ z) (hv : v ≠ z) :
    ‖logDistDeriv z u - logDistDeriv z v‖ = ‖u - v‖ / (‖u - z‖ * ‖v - z‖) := by
  have hinv := EuclideanGeometry.dist_inversion_inversion hu hv 1
  rw [EuclideanGeometry.inversion_def] at hinv
  simp only [vsub_eq_sub, vadd_eq_add, one_pow, dist_eq_norm] at hinv
  have hrepr : logDistDeriv z u - logDistDeriv z v =
      innerSL ℝ ((1 / ‖u - z‖) ^ 2 • (u - z) - (1 / ‖v - z‖) ^ 2 • (v - z)) := by
    ext x
    simp only [logDistDeriv, sub_apply, smul_apply,
      innerSL_apply_apply, inner_sub_left, real_inner_smul_left, smul_eq_mul, one_div, inv_pow]
  rw [hrepr, innerSL_apply_norm]
  have : (1 / ‖u - z‖) ^ 2 • (u - z) - (1 / ‖v - z‖) ^ 2 • (v - z) =
      ((1 / ‖u - z‖) ^ 2 • (u - z) + z) - ((1 / ‖v - z‖) ^ 2 • (v - z) + z) := by abel
  rw [this, hinv]
  field_simp

/-- The harmonic interpolation `(log|w − z| − log a)/log(b/a)`: `0` on `∂B_a(z)`, `1` on `∂B_b(z)`. -/
def logRad (z : ℂ) (a b : ℝ) (w : ℂ) : ℝ := (Real.log ‖w - z‖ - Real.log a) / Real.log (b / a)

theorem hasFDerivAt_logRad {z w : ℂ} (hw : w ≠ z) (a b : ℝ) :
    HasFDerivAt (logRad z a b) ((Real.log (b / a))⁻¹ • logDistDeriv z w) w := by
  have h := ((hasFDerivAt_logDist hw).sub_const (Real.log a)).const_mul (Real.log (b / a))⁻¹
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  unfold logRad
  rw [div_eq_inv_mul]

theorem fderiv_logRad {z w : ℂ} (hw : w ≠ z) (a b : ℝ) :
    fderiv ℝ (logRad z a b) w = (Real.log (b / a))⁻¹ • logDistDeriv z w :=
  (hasFDerivAt_logRad hw a b).fderiv

theorem norm_fderiv_logRad {z w : ℂ} (hw : w ≠ z) (a b : ℝ) :
    ‖fderiv ℝ (logRad z a b) w‖ = (|Real.log (b / a)| * ‖w - z‖)⁻¹ := by
  rw [fderiv_logRad hw, norm_smul, norm_logDistDeriv hw, norm_inv, Real.norm_eq_abs, mul_inv]

theorem logRad_of_norm_eq_left {z w : ℂ} {a b : ℝ} (hw : ‖w - z‖ = a) : logRad z a b w = 0 := by
  unfold logRad
  rw [hw, sub_self, zero_div]

theorem logRad_of_norm_eq_right {z w : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hw : ‖w - z‖ = b) : logRad z a b w = 1 := by
  unfold logRad
  rw [hw, ← Real.log_div hb.ne' ha.ne']
  refine div_self ?_
  rw [Real.log_ne_zero]
  refine ⟨(div_pos hb ha).ne', ?_, ?_⟩
  · intro h
    rw [div_eq_one_iff_eq ha.ne'] at h
    exact hab h.symm
  · intro h
    have : 0 < b / a := div_pos hb ha
    linarith

theorem differentiableOn_logRad (z : ℂ) (a b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    DifferentiableOn ℝ (logRad z a b) {w | c < ‖w - z‖} := fun w hw => by
  have hw' : w ≠ z := by
    intro h
    simp only [Set.mem_ofPred_eq, h, sub_self, norm_zero] at hw
    linarith
  exact (hasFDerivAt_logRad hw' a b).differentiableAt.differentiableWithinAt

theorem isOpen_norm_sub_gt (z : ℂ) (c : ℝ) : IsOpen {w : ℂ | c < ‖w - z‖} :=
  isOpen_lt continuous_const (continuous_id.sub continuous_const).norm

/-- `∇ logRad` is `1/(L c²)`-Lipschitz on `{|w − z| ≥ c}`. -/
theorem norm_fderiv_logRad_sub_le {z : ℂ} {a b c : ℝ} (hc : 0 < c) {u v : ℂ}
    (hu : c ≤ ‖u - z‖) (hv : c ≤ ‖v - z‖) :
    ‖fderiv ℝ (logRad z a b) u - fderiv ℝ (logRad z a b) v‖ ≤
      (|Real.log (b / a)| * c ^ 2)⁻¹ * ‖u - v‖ := by
  have hu' : u ≠ z := fun h => by rw [h, sub_self, norm_zero] at hu; linarith
  have hv' : v ≠ z := fun h => by rw [h, sub_self, norm_zero] at hv; linarith
  rw [fderiv_logRad hu', fderiv_logRad hv', ← smul_sub, norm_smul, norm_logDistDeriv_sub hu' hv',
    norm_inv, Real.norm_eq_abs]
  have hden : c ^ 2 ≤ ‖u - z‖ * ‖v - z‖ := by rw [sq]; exact mul_le_mul hu hv hc.le (by linarith)
  calc |Real.log (b / a)|⁻¹ * (‖u - v‖ / (‖u - z‖ * ‖v - z‖))
      ≤ |Real.log (b / a)|⁻¹ * (‖u - v‖ / c ^ 2) := by gcongr
    _ = (|Real.log (b / a)| * c ^ 2)⁻¹ * ‖u - v‖ := by rw [mul_inv]; ring

/-- `|∇ logRad(w)|² = 1/(L² |w − z|²)`. -/
theorem sqGrad_logRad {z w : ℂ} (hw : w ≠ z) (a b : ℝ) :
    ‖fderiv ℝ (logRad z a b) w‖ ^ 2 = ((Real.log (b / a)) ^ 2 * ‖w - z‖ ^ 2)⁻¹ := by
  rw [norm_fderiv_logRad hw, inv_pow, mul_pow, sq_abs]

theorem sqGrad_le {z : ℂ} {a b c : ℝ} (hc : 0 < c) {w : ℂ} (hw : c ≤ ‖w - z‖) :
    ‖fderiv ℝ (logRad z a b) w‖ ^ 2 ≤ ((Real.log (b / a)) ^ 2 * c ^ 2)⁻¹ := by
  have hw' : w ≠ z := fun h => by rw [h, sub_self, norm_zero] at hw; linarith
  rw [sqGrad_logRad hw']
  by_cases hL : Real.log (b / a) = 0
  · simp [hL]
  have hL2 : 0 < (Real.log (b / a)) ^ 2 := by positivity
  gcongr

/-- `|∇ logRad|²` is one-sidedly `2/(L² c³)`-Lipschitz on `{|w − z| ≥ c}`. -/
theorem sqGrad_le_add {z : ℂ} {a b c : ℝ} (hc : 0 < c) {u v : ℂ} (hu : c ≤ ‖u - z‖)
    (hv : c ≤ ‖v - z‖) :
    ‖fderiv ℝ (logRad z a b) u‖ ^ 2 ≤ ‖fderiv ℝ (logRad z a b) v‖ ^ 2 +
      2 * ((Real.log (b / a)) ^ 2 * c ^ 3)⁻¹ * dist u v := by
  have hu' : u ≠ z := fun h => by rw [h, sub_self, norm_zero] at hu; linarith
  have hv' : v ≠ z := fun h => by rw [h, sub_self, norm_zero] at hv; linarith
  rw [sqGrad_logRad hu', sqGrad_logRad hv']
  by_cases hL : Real.log (b / a) = 0
  · simp [hL]
  set L2 := (Real.log (b / a)) ^ 2 with hL2def
  have hL2 : 0 < L2 := by positivity
  set p := ‖u - z‖
  set q := ‖v - z‖
  have hp : 0 < p := by linarith
  have hq : 0 < q := by linarith
  have hdist : |q - p| ≤ dist u v := by
    have := abs_norm_sub_norm_le (v - z) (u - z)
    rw [sub_sub_sub_cancel_right] at this
    rw [dist_eq_norm, norm_sub_rev]
    exact this
  -- `1/p² − 1/q² = (q − p)(q + p)/(p² q²) ≤ |q − p| (1/(p q²) + 1/(p² q)) ≤ 2|q − p|/c³`
  have key : (p ^ 2)⁻¹ - (q ^ 2)⁻¹ ≤ 2 * (c ^ 3)⁻¹ * dist u v := by
    have h1 : (p ^ 2)⁻¹ - (q ^ 2)⁻¹ = (q - p) * (q + p) / (p ^ 2 * q ^ 2) := by
      field_simp
      ring
    rw [h1]
    have h2 : (q - p) * (q + p) / (p ^ 2 * q ^ 2) ≤ |q - p| * ((q + p) / (p ^ 2 * q ^ 2)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h3 : (q + p) / (p ^ 2 * q ^ 2) ≤ 2 * (c ^ 3)⁻¹ := by
      have e : (q + p) / (p ^ 2 * q ^ 2) = 1 / (p ^ 2 * q) + 1 / (p * q ^ 2) := by
        field_simp
      rw [e, two_mul]
      have hc3 : c ^ 3 ≤ p ^ 2 * q := by
        calc c ^ 3 = c ^ 2 * c := by ring
          _ ≤ p ^ 2 * q := mul_le_mul (pow_le_pow_left₀ hc.le hu 2) hv hc.le (by positivity)
      have hc3' : c ^ 3 ≤ p * q ^ 2 := by
        calc c ^ 3 = c * c ^ 2 := by ring
          _ ≤ p * q ^ 2 := mul_le_mul hu (pow_le_pow_left₀ hc.le hv 2) (by positivity) hp.le
      have h3a : 1 / (p ^ 2 * q) ≤ (c ^ 3)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (by positivity) hc3
      have h3b : 1 / (p * q ^ 2) ≤ (c ^ 3)⁻¹ := by
        rw [one_div]; exact inv_anti₀ (by positivity) hc3'
      linarith
    calc (q - p) * (q + p) / (p ^ 2 * q ^ 2) ≤ |q - p| * ((q + p) / (p ^ 2 * q ^ 2)) := h2
      _ ≤ dist u v * (2 * (c ^ 3)⁻¹) := mul_le_mul hdist h3 (by positivity) dist_nonneg
      _ = 2 * (c ^ 3)⁻¹ * dist u v := by ring
  have hmul : (L2 * p ^ 2)⁻¹ - (L2 * q ^ 2)⁻¹ = L2⁻¹ * ((p ^ 2)⁻¹ - (q ^ 2)⁻¹) := by
    rw [mul_inv, mul_inv]; ring
  have : (L2 * p ^ 2)⁻¹ - (L2 * q ^ 2)⁻¹ ≤ 2 * (L2 * c ^ 3)⁻¹ * dist u v := by
    rw [hmul, mul_inv]
    calc L2⁻¹ * ((p ^ 2)⁻¹ - (q ^ 2)⁻¹) ≤ L2⁻¹ * (2 * (c ^ 3)⁻¹ * dist u v) :=
          mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hL2.le)
      _ = _ := by ring
  linarith

/-! ### The Dirichlet energy of `logRad` on an annulus -/

/-- The radial lower integral over `ℂ` in polar coordinates. -/
theorem lintegral_radial (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ w : ℂ, φ ‖w‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * φ r := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • φ ‖Complex.polarCoord.symm p‖ =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal p.1 * φ p.1 := by
    rw [polarCoord_target]
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul]
  rw [hcongr, Measure.volume_eq_prod, setLIntegral_prod]
  · simp only [setLIntegral_const, Real.volume_Ioo]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    congr 2
    ring
  · exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hφ.comp measurable_fst)).aemeasurable

theorem eucEnergy_logRad {z : ℂ} {a b r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂) :
    eucEnergy (logRad z a b) {w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} =
      ENNReal.ofReal (2 * π * Real.log (r₂ / r₁) / (Real.log (b / a)) ^ 2) := by
  set L2 := (Real.log (b / a)) ^ 2 with hL2
  let φ : ℝ → ℝ≥0∞ := (Ioo r₁ r₂).indicator fun r => ENNReal.ofReal ((L2 * r ^ 2)⁻¹)
  have hφ : Measurable φ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator measurableSet_Ioo
  have hnm : Measurable fun w : ℂ => ‖w - z‖ := (continuous_id.sub continuous_const).norm.measurable
  have hset : MeasurableSet {w : ℂ | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} :=
    (measurableSet_lt measurable_const hnm).inter (measurableSet_lt hnm measurable_const)
  have h1 : eucEnergy (logRad z a b) {w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} =
      ∫⁻ w : ℂ, φ ‖w - z‖ := by
    unfold eucEnergy
    rw [← lintegral_indicator hset]
    congr 1
    funext w
    by_cases hw : w ∈ {w : ℂ | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂}
    · have hw' : w ≠ z := fun h => by
        simp only [Set.mem_ofPred_eq, h, sub_self, norm_zero] at hw; linarith [hw.1]
      simp only [φ]
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem (show ‖w - z‖ ∈ Ioo r₁ r₂ from hw),
        sqGrad_logRad hw']
    · simp only [φ]
      rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (show ‖w - z‖ ∉ Ioo r₁ r₂ from hw)]
  rw [h1, lintegral_sub_right_eq_self (fun w => φ ‖w‖) z, lintegral_radial φ hφ]
  have h2 : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * φ r =
      ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal (L2⁻¹ * r⁻¹) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext r
    by_cases hr' : r ∈ Ioo r₁ r₂
    · have hr0 : 0 < r := hr₁.trans hr'.1
      simp only [φ]
      rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr0), Set.indicator_of_mem hr',
        Set.indicator_of_mem hr', ← ENNReal.ofReal_mul hr0.le]
      congr 1
      rw [mul_inv]
      field_simp
    · rw [Set.indicator_of_notMem hr' (f := fun r => ENNReal.ofReal (L2⁻¹ * r⁻¹))]
      by_cases hr0 : r ∈ Ioi (0 : ℝ)
      · simp only [φ]
        rw [Set.indicator_of_mem hr0, Set.indicator_of_notMem hr', mul_zero]
      · rw [Set.indicator_of_notMem hr0]
  have h3 : ∫⁻ r in Ioo r₁ r₂, ENNReal.ofReal (L2⁻¹ * r⁻¹) =
      ENNReal.ofReal (L2⁻¹ * Real.log (r₂ / r₁)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
        intervalIntegral.integral_const_mul,
        integral_inv_of_pos hr₁ (hr₁.trans_le hr)]
    · refine (ContinuousOn.integrableOn_Icc (f := fun r : ℝ => L2⁻¹ * r⁻¹) ?_).mono_set
        Ioo_subset_Icc_self
      exact continuousOn_const.mul (continuousOn_inv₀.mono fun r hr' => (hr₁.trans_le hr'.1).ne')
    · refine (ae_restrict_mem measurableSet_Ioo).mono fun r hr' => ?_
      have : 0 < r := hr₁.trans hr'.1
      positivity
  rw [h2, h3, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_eq_inv_mul]
  ring

/-- **The Euclidean Dirichlet energy of `logRad` on the annulus between radii `a` and `b` is
`2π / |log(b/a)|`**. -/
theorem eucEnergy_logRad_annulus {z : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₂) :
    eucEnergy (logRad z r₁ r₂) {w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} =
      ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) ∧
    eucEnergy (logRad z r₂ r₁) {w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} =
      ENNReal.ofReal (2 * π / Real.log (r₂ / r₁)) := by
  have hlog : 0 < Real.log (r₂ / r₁) := Real.log_pos ((one_lt_div hr₁).mpr hr)
  refine ⟨?_, ?_⟩
  · rw [eucEnergy_logRad hr₁ hr.le]
    congr 1
    field_simp
  · rw [eucEnergy_logRad hr₁ hr.le]
    congr 1
    rw [show r₁ / r₂ = (r₂ / r₁)⁻¹ by rw [inv_div], Real.log_inv, neg_sq]
    field_simp

end MatedCRTHarmonic.GMS3
