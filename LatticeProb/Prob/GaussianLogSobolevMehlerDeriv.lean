/-
# Derivatives of the Mehler interpolation of an exponential tilt

For `g : E → ℝ` with continuous gradient `g'` bounded by `K`, the Mehler interpolation
`LatticeProb.GaussLSI.mehler g α u = ∫ v, exp (g (sin α • u + cos α • v)) ∂γ` is differentiable in
the angle and along lines in the base point, by differentiation under the integral sign:

* `hasDerivAt_mehler_angle`: `∂_α mehler g α u = mehlerAngleDeriv g g' α u
  = ∫ v, exp (g w) ⟪g' w, cos α • u - sin α • v⟫ ∂γ`, where `w = sin α • u + cos α • v`;
* `hasDerivAt_mehler_line`: the derivative of `s ↦ mehler g α (u + s • e)` is
  `⟪mehlerGrad g g' α (u + s • e), e⟫`, where
  `mehlerGrad g g' α u = sin α • ∫ v, exp (g w) • g' w ∂γ`;
* `norm_mehlerGrad_le`: `‖mehlerGrad g g' α u‖ ≤ K |sin α| mehler g α u`;
* `continuous_mehler`, `continuous_mehlerGrad`: continuity in the base point.
-/
import LatticeProb.Prob.GaussianLogSobolevMehler

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped RealInnerProductSpace NNReal

namespace LatticeProb.GaussLSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The angle derivative of the Mehler interpolation. -/
def mehlerAngleDeriv (g : E → ℝ) (g' : E → E) (α : ℝ) (u : E) : ℝ :=
  ∫ v, Real.exp (g (Real.sin α • u + Real.cos α • v)) *
    ⟪g' (Real.sin α • u + Real.cos α • v), Real.cos α • u - Real.sin α • v⟫ ∂(stdGaussian E)

/-- The gradient of the Mehler interpolation in the base point. -/
def mehlerGrad (g : E → ℝ) (g' : E → E) (α : ℝ) (u : E) : E :=
  Real.sin α • ∫ v, Real.exp (g (Real.sin α • u + Real.cos α • v)) •
    g' (Real.sin α • u + Real.cos α • v) ∂(stdGaussian E)

variable {g : E → ℝ} {g' : E → E} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The chain rule for `exp ∘ g` along a differentiable path. -/
theorem hasDerivAt_exp_comp (hgd : ∀ x, HasGradientAt g (g' x) x) {c : ℝ → E} {c' : E}
    {t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s => Real.exp (g (c s))) (Real.exp (g (c t)) * ⟪g' (c t), c'⟫) t := by
  have h := (hgd (c t)).hasFDerivAt.comp_hasDerivAt t hc
  simp only [InnerProductSpace.toDual_apply_apply] at h
  exact h.exp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The integrand of the derivatives is bounded by `K ‖y‖ e^{g w}`. -/
theorem abs_exp_mul_inner_le (hg'b : ∀ x, ‖g' x‖ ≤ K) (w y : E) :
    |Real.exp (g w) * ⟪g' w, y⟫| ≤ Real.exp (g w) * (K * ‖y‖) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (hg'b w) (norm_nonneg _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The angle velocity `cos α • u - sin α • v` has norm at most `‖u‖ + ‖v‖`. -/
theorem norm_cos_smul_sub_sin_smul_le (α : ℝ) (u v : E) :
    ‖Real.cos α • u - Real.sin α • v‖ ≤ ‖u‖ + ‖v‖ := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one α)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The integrand of the angle derivative is bounded by `A e^{(K + 1) ‖v‖}`. -/
theorem abs_mehlerAngleIntegrand_le (hg : LipschitzWith K g) (hg'b : ∀ x, ‖g' x‖ ≤ K)
    (β : ℝ) (u v : E) :
    |Real.exp (g (Real.sin β • u + Real.cos β • v)) *
      ⟪g' (Real.sin β • u + Real.cos β • v), Real.cos β • u - Real.sin β • v⟫|
      ≤ Real.exp (g 0) * Real.exp (K * ‖u‖) * K * (‖u‖ + 1) *
        Real.exp (((K : ℝ) + 1) * ‖v‖) := by
  set A := Real.exp (g 0) * Real.exp (K * ‖u‖)
  have hA0 : 0 ≤ A := by positivity
  refine (abs_exp_mul_inner_le hg'b _ _).trans ?_
  have h1 := exp_rot_le hg β u v
  have h2 := norm_cos_smul_sub_sin_smul_le β u v
  have h3 := Kahane.norm_mul_exp_le 1 K zero_le_one v
  have h4 : Real.exp (K * ‖v‖) ≤ Real.exp (((K : ℝ) + 1) * ‖v‖) :=
    Real.exp_le_exp.mpr (by nlinarith [norm_nonneg v])
  have hK := K.coe_nonneg
  calc Real.exp (g (Real.sin β • u + Real.cos β • v)) * (K * ‖Real.cos β • u - Real.sin β • v‖)
      ≤ (A * Real.exp (K * ‖v‖)) * (K * (‖u‖ + ‖v‖)) := by gcongr
    _ = A * K * (‖u‖ * Real.exp (K * ‖v‖) + ‖v‖ * (1 * Real.exp (K * ‖v‖))) := by ring
    _ ≤ A * K * (‖u‖ * Real.exp (((K : ℝ) + 1) * ‖v‖) +
          1 * Real.exp (((K : ℝ) + 1) * ‖v‖)) := by gcongr
    _ = A * K * (‖u‖ + 1) * Real.exp (((K : ℝ) + 1) * ‖v‖) := by ring

/-- **The angle derivative of the Mehler interpolation**, by differentiation under the integral. -/
theorem hasDerivAt_mehler_angle (hg : LipschitzWith K g) (hgd : ∀ x, HasGradientAt g (g' x) x)
    (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ) (u : E) :
    HasDerivAt (fun β => mehler g β u) (mehlerAngleDeriv g g' α u) α := by
  have hgc := hg.continuous
  have hpath : ∀ (β : ℝ) (v : E), HasDerivAt (fun s => Real.sin s • u + Real.cos s • v)
      (Real.cos β • u - Real.sin β • v) β := by
    intro β v
    have := ((Real.hasDerivAt_sin β).smul_const u).add ((Real.hasDerivAt_cos β).smul_const v)
    rw [sub_eq_add_neg, ← neg_smul]
    exact this
  set A := Real.exp (g 0) * Real.exp (K * ‖u‖)
  have hA0 : 0 ≤ A := by positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := α) (s := Set.univ)
    (F := fun β v => Real.exp (g (Real.sin β • u + Real.cos β • v)))
    (F' := fun β v => Real.exp (g (Real.sin β • u + Real.cos β • v)) *
      ⟪g' (Real.sin β • u + Real.cos β • v), Real.cos β • u - Real.sin β • v⟫)
    (bound := fun v => A * K * (‖u‖ + 1) * Real.exp (((K : ℝ) + 1) * ‖v‖)) univ_mem
    (Eventually.of_forall fun β => by fun_prop) (integrable_mehlerIntegrand hg α u)
    (by fun_prop) (ae_of_all _ fun v β _ => ?_)
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) ((K : ℝ) + 1)).const_mul _)
    (ae_of_all _ fun v β _ => hasDerivAt_exp_comp hgd (hpath β v))).2
  rw [Real.norm_eq_abs]
  exact abs_mehlerAngleIntegrand_le hg hg'b β u v

/-- The vector integrand of `mehlerGrad` is integrable. -/
theorem integrable_mehlerGradIntegrand (hg : LipschitzWith K g) (hg'c : Continuous g')
    (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ) (u : E) :
    Integrable (fun v => Real.exp (g (Real.sin α • u + Real.cos α • v)) •
      g' (Real.sin α • u + Real.cos α • v)) (stdGaussian E) := by
  have hgc := hg.continuous
  refine ((integrable_mehlerIntegrand hg α u).const_mul K).mono' (by fun_prop)
    (ae_of_all _ fun v => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hg'b _) (Real.exp_pos _).le

/-- **The gradient bound** `‖∇ mehler‖ ≤ K |sin α| mehler`. -/
theorem norm_mehlerGrad_le (hg : LipschitzWith K g) (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ)
    (u : E) : ‖mehlerGrad g g' α u‖ ≤ K * |Real.sin α| * mehler g α u := by
  rw [mehlerGrad, norm_smul, Real.norm_eq_abs, mul_comm (K : ℝ), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [mehler, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_mehlerIntegrand hg α u).const_mul _)
    (ae_of_all _ fun v => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hg'b _) (Real.exp_pos _).le

/-- **The derivative of the Mehler interpolation along a line** in the base point. -/
theorem hasDerivAt_mehler_line (hg : LipschitzWith K g) (hgd : ∀ x, HasGradientAt g (g' x) x)
    (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ) (u e : E) (t : ℝ) :
    HasDerivAt (fun s => mehler g α (u + s • e)) ⟪mehlerGrad g g' α (u + t • e), e⟫ t := by
  have hgc := hg.continuous
  have hpath : ∀ (s : ℝ) (v : E), HasDerivAt
      (fun r => Real.sin α • (u + r • e) + Real.cos α • v) (Real.sin α • e) s := by
    intro s v
    have h1 : HasDerivAt (fun r : ℝ => u + r • e) e s := by
      simpa using ((hasDerivAt_id' s).smul_const e).const_add u
    simpa using (h1.const_smul (Real.sin α)).add_const (Real.cos α • v)
  set A := Real.exp (g 0) * Real.exp (K * (‖u‖ + (|t| + 1) * ‖e‖))
  have hA0 : 0 ≤ A := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian E)
    (F := fun s v => Real.exp (g (Real.sin α • (u + s • e) + Real.cos α • v)))
    (F' := fun s v => Real.exp (g (Real.sin α • (u + s • e) + Real.cos α • v)) *
      ⟪g' (Real.sin α • (u + s • e) + Real.cos α • v), Real.sin α • e⟫) (x₀ := t)
    (s := Metric.ball t 1) (bound := fun v => A * (K * ‖e‖) * Real.exp (K * ‖v‖))
    (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s => by fun_prop) (integrable_mehlerIntegrand hg α (u + t • e))
    (by fun_prop) (ae_of_all _ fun v s hs => ?_)
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).const_mul _)
    (ae_of_all _ fun v s _ => hasDerivAt_exp_comp hgd (hpath s v))
  · refine key.2.congr_deriv ?_
    have hI := integrable_mehlerGradIntegrand hg hg'c hg'b α (u + t • e)
    rw [mehlerGrad, real_inner_smul_left, real_inner_comm e, ← integral_inner hI,
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [inner_smul_right]
    rw [real_inner_comm e]
    ring
  · rw [Real.norm_eq_abs]
    refine (abs_exp_mul_inner_le hg'b _ _).trans ?_
    have hs' : |s| ≤ |t| + 1 := by
      have := abs_sub_abs_le_abs_sub s t
      rw [Metric.mem_ball, Real.dist_eq] at hs
      linarith
    have hnorm : ‖u + s • e‖ ≤ ‖u‖ + (|t| + 1) * ‖e‖ := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
    have h1 := exp_rot_le hg α (u + s • e) v
    have h2 : Real.exp (K * ‖u + s • e‖) ≤ Real.exp (K * (‖u‖ + (|t| + 1) * ‖e‖)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)
    have h3 : ‖Real.sin α • e‖ ≤ ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one α)
    have hK := K.coe_nonneg
    calc Real.exp (g (Real.sin α • (u + s • e) + Real.cos α • v)) * (K * ‖Real.sin α • e‖)
        ≤ (Real.exp (g 0) * Real.exp (K * ‖u + s • e‖) * Real.exp (K * ‖v‖)) * (K * ‖e‖) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h3 hK) (by positivity) (by positivity)
      _ ≤ (A * Real.exp (K * ‖v‖)) * (K * ‖e‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (Real.exp_pos _).le) (by positivity)
      _ = A * (K * ‖e‖) * Real.exp (K * ‖v‖) := by ring

/-- The Mehler interpolation is continuous in the base point. -/
theorem continuous_mehler (hg : LipschitzWith K g) (α : ℝ) :
    Continuous (mehler g α) := by
  have hgc := hg.continuous
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  refine continuousAt_of_dominated (bound := fun v => Real.exp (g 0) *
      Real.exp (K * (‖u₀‖ + 1)) * Real.exp (K * ‖v‖))
    (Eventually.of_forall fun u => by fun_prop) ?_
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).const_mul _)
    (ae_of_all _ fun v => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
  refine ae_of_all _ fun v => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (exp_rot_le hg α u v).trans ?_
  have : ‖u‖ ≤ ‖u₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' u u₀
    rw [Metric.mem_ball, dist_eq_norm] at hu
    linarith
  gcongr

/-- The integral in `mehlerGrad` is continuous in the base point. -/
theorem continuous_mehlerGrad (hg : LipschitzWith K g) (hg'c : Continuous g')
    (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ) :
    Continuous (mehlerGrad g g' α) := by
  have hgc := hg.continuous
  refine Continuous.const_smul (continuous_iff_continuousAt.2 fun u₀ => ?_) _
  refine continuousAt_of_dominated (bound := fun v => K * (Real.exp (g 0) *
      Real.exp (K * (‖u₀‖ + 1)) * Real.exp (K * ‖v‖)))
    (Eventually.of_forall fun u => by fun_prop) ?_
    (((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).const_mul _).const_mul _)
    (ae_of_all _ fun v => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
  refine ae_of_all _ fun v => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  have : ‖u‖ ≤ ‖u₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' u u₀
    rw [Metric.mem_ball, dist_eq_norm] at hu
    linarith
  have h := exp_rot_le hg α u v
  have h' : Real.exp (K * ‖u‖) ≤ Real.exp (K * (‖u₀‖ + 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left this K.coe_nonneg)
  refine mul_le_mul (hg'b _) (h.trans ?_) (Real.exp_pos _).le K.coe_nonneg
  gcongr

end LatticeProb.GaussLSI
