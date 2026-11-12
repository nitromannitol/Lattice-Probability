/-
# The Gaussian logarithmic Sobolev inequality for exponential tilts

Let `γ = stdGaussian E` and let `g : E → ℝ` have a continuous gradient `g'` with `‖g'‖ ≤ K`.
Then for `f = exp ∘ g`,

  `∫ f log f dγ ≤ (∫ f dγ) log (∫ f dγ) + (K² / 2) ∫ f dγ`

(`integral_mul_log_le_of_gradient`). This is the Gaussian logarithmic Sobolev inequality
(Gross 1975) for densities whose logarithm is `K`-Lipschitz, with the sharp constant.

The proof is the semigroup argument of Bakry and Émery, written along the Mehler interpolation
`LatticeProb.GaussLSI.mehler g α` (the Ornstein–Uhlenbeck semigroup at time `t` with
`sin α = e^{-t}`). The entropy functional `Φ(α) = ∫ mehler g α log (mehler g α) dγ` is
differentiable (`hasDerivAt_mehlerEntropy`). Rotating `γ ⊗ γ` and applying Gaussian integration by
parts (`LatticeProb.Kahane.integral_inner_mul_stdGaussian_of_le`) writes its derivative as
`cos α ∫∫ ⟪∇ log mehler g α (sin α • w + cos α • z), ∇ f (w)⟫`, and the bounds
`‖∇ log mehler g α‖ ≤ K sin α` and `‖∇ f‖ ≤ K f` give `Φ'(α) ≤ K² sin α cos α ∫ f dγ` on
`[0, π / 2]` (`mehlerEntropy_deriv_le`). Integrating from `α = 0` (where `mehler` is the constant
`∫ f dγ`) to `α = π / 2` (where it is `f`) gives the inequality.
-/
import LatticeProb.Prob.GaussianLogSobolevMehlerDeriv

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped RealInnerProductSpace NNReal

namespace LatticeProb.GaussLSI

open GaussConc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The entropy functional along the Mehler interpolation. -/
def mehlerEntropy (g : E → ℝ) (α : ℝ) : ℝ :=
  ∫ u, mehler g α u * Real.log (mehler g α u) ∂(stdGaussian E)

variable {g : E → ℝ} {g' : E → E} {K : ℝ≥0}

/-- The constant bounding `|log mehler g α u| - K ‖u‖`, uniformly in the angle. -/
def logBound (g : E → ℝ) (K : ℝ≥0) : ℝ :=
  |g 0| + |Real.log (∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E))|
    + |Real.log (∫ v, Real.exp (-(K * ‖v‖)) ∂(stdGaussian E))|

omit [BorelSpace E] in
theorem logBound_nonneg : 0 ≤ logBound (E := E) g K := by
  unfold logBound; positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Mehler integrand is bounded below by a product of exponentials of the norms. -/
theorem exp_rot_ge (hg : LipschitzWith K g) (α : ℝ) (u v : E) :
    Real.exp (g 0) * Real.exp (-(K * ‖u‖)) * Real.exp (-(K * ‖v‖))
      ≤ Real.exp (g (Real.sin α • u + Real.cos α • v)) := by
  refine le_trans ?_ (exp_ge_of_lipschitz hg _)
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left (norm_sin_smul_add_cos_smul_le α u v) K.coe_nonneg
  linarith

/-- **Uniform logarithmic growth**: `|log mehler g α u| ≤ logBound g K + K ‖u‖`. -/
theorem abs_log_mehler_le (hg : LipschitzWith K g) (α : ℝ) (u : E) :
    |Real.log (mehler g α u)| ≤ logBound g K + K * ‖u‖ := by
  have hM := Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K
  have hm := Kahane.integrable_exp_mul_norm_stdGaussian (E := E) (-K)
  have hM0 : 0 < ∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E) := integral_exp_pos hM
  have hm0 : 0 < ∫ v, Real.exp (-(K * ‖v‖)) ∂(stdGaussian E) := by
    simpa [neg_mul] using integral_exp_pos hm
  have hup : mehler g α u ≤
      Real.exp (g 0) * Real.exp (K * ‖u‖) * ∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E) := by
    rw [mehler, ← integral_const_mul]
    exact integral_mono (integrable_mehlerIntegrand hg α u) (hM.const_mul _)
      fun v => exp_rot_le hg α u v
  have hlow : Real.exp (g 0) * Real.exp (-(K * ‖u‖)) *
      ∫ v, Real.exp (-(K * ‖v‖)) ∂(stdGaussian E) ≤ mehler g α u := by
    rw [mehler, ← integral_const_mul]
    refine integral_mono ((by simpa [neg_mul] using hm : Integrable (fun v =>
      Real.exp (-(K * ‖v‖))) (stdGaussian E)).const_mul _) (integrable_mehlerIntegrand hg α u)
      fun v => exp_rot_ge hg α u v
  have hpos := mehler_pos hg α u
  have h1 := Real.log_le_log hpos hup
  have h2 := Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (by positivity) hM0.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_exp] at h1
  rw [Real.log_mul (by positivity) hm0.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_exp] at h2
  unfold logBound
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (g 0), neg_abs_le (g 0),
    le_abs_self (Real.log (∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E))),
    neg_abs_le (Real.log (∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E))),
    le_abs_self (Real.log (∫ v, Real.exp (-(K * ‖v‖)) ∂(stdGaussian E))),
    neg_abs_le (Real.log (∫ v, Real.exp (-(K * ‖v‖)) ∂(stdGaussian E))),
    mul_nonneg K.coe_nonneg (norm_nonneg u)]

/-- The upper bound `mehler g α u ≤ e^{g 0} e^{K ‖u‖} ∫ e^{K ‖v‖} dγ`, uniformly in the angle. -/
theorem mehler_le_uniform (hg : LipschitzWith K g) (α : ℝ) (u : E) :
    mehler g α u ≤
      Real.exp (g 0) * Real.exp (K * ‖u‖) * ∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E) := by
  rw [mehler, ← integral_const_mul]
  exact integral_mono (integrable_mehlerIntegrand hg α u)
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) K).const_mul _)
    fun v => exp_rot_le hg α u v

/-- The angle derivative is bounded by `A(u) ∫ e^{(K + 1) ‖v‖} dγ`, uniformly in the angle. -/
theorem abs_mehlerAngleDeriv_le (hg : LipschitzWith K g) (hg'b : ∀ x, ‖g' x‖ ≤ K) (β : ℝ)
    (u : E) :
    |mehlerAngleDeriv g g' β u| ≤ Real.exp (g 0) * Real.exp (K * ‖u‖) * K * (‖u‖ + 1) *
      ∫ v, Real.exp (((K : ℝ) + 1) * ‖v‖) ∂(stdGaussian E) := by
  rw [mehlerAngleDeriv, ← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) _).const_mul _)
    (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs]; exact abs_mehlerAngleIntegrand_le hg hg'b β u v)

/-- The angle derivative is strongly measurable in the base point. -/
theorem stronglyMeasurable_mehlerAngleDeriv (hg : LipschitzWith K g) (hg'c : Continuous g')
    (β : ℝ) : StronglyMeasurable (mehlerAngleDeriv g g' β) := by
  have hgc := hg.continuous
  have hc : Continuous fun p : E × E => Real.exp (g (Real.sin β • p.1 + Real.cos β • p.2)) *
      ⟪g' (Real.sin β • p.1 + Real.cos β • p.2), Real.cos β • p.1 - Real.sin β • p.2⟫ := by
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

/-- **The derivative of the entropy functional** along the Mehler interpolation. -/
theorem hasDerivAt_mehlerEntropy (hg : LipschitzWith K g) (hgd : ∀ x, HasGradientAt g (g' x) x)
    (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K) (α : ℝ) :
    HasDerivAt (mehlerEntropy g)
      (∫ u, (Real.log (mehler g α u) + 1) * mehlerAngleDeriv g g' α u ∂(stdGaussian E)) α := by
  have hL := logBound_nonneg (E := E) (g := g) (K := K)
  have hK := K.coe_nonneg
  set M₁ := ∫ v, Real.exp (((K : ℝ) + 1) * ‖v‖) ∂(stdGaussian E)
  have hM₁ : 0 ≤ M₁ := integral_nonneg fun _ => (Real.exp_pos _).le
  set M := ∫ v, Real.exp (K * ‖v‖) ∂(stdGaussian E)
  have hM : 0 ≤ M := integral_nonneg fun _ => (Real.exp_pos _).le
  have hlogc : ∀ β, Continuous fun u => Real.log (mehler g β u) := fun β =>
    (continuous_mehler hg β).log fun u => (mehler_pos hg β u).ne'
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := α) (s := univ)
    (F := fun β u => mehler g β u * Real.log (mehler g β u))
    (F' := fun β u => (Real.log (mehler g β u) + 1) * mehlerAngleDeriv g g' β u)
    (bound := fun u => Real.exp (g 0) * K * M₁ * (logBound g K + 1 + K) *
      Real.exp (((K : ℝ) + 2) * ‖u‖)) univ_mem
    (Eventually.of_forall fun β => ((continuous_mehler hg β).mul (hlogc β)).aestronglyMeasurable)
    ?_ (((hlogc α).add continuous_const).aestronglyMeasurable.mul
      (stronglyMeasurable_mehlerAngleDeriv hg hg'c α).aestronglyMeasurable)
    (ae_of_all _ fun u β _ => ?_)
    ((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) ((K : ℝ) + 2)).const_mul _)
    (ae_of_all _ fun u β _ => by
      have h := (Real.hasDerivAt_mul_log (mehler_pos hg β u).ne').comp β
        (hasDerivAt_mehler_angle hg hgd hg'c hg'b β u)
      exact h)).2
  · refine Kahane.integrable_of_le_exp (A := Real.exp (g 0) * M * (logBound g K + K))
      (B := (K : ℝ) + 1) ((continuous_mehler hg α).mul (hlogc α)).aestronglyMeasurable
      fun u => ?_
    have h1 := mehler_le_uniform hg α u
    have h2 := abs_log_mehler_le hg α u
    have h3 : logBound g K + K * ‖u‖ ≤ (logBound g K + K) * Real.exp ‖u‖ := by
      nlinarith [Real.add_one_le_exp ‖u‖, norm_nonneg u]
    rw [abs_mul, abs_of_pos (mehler_pos hg α u),
      show ((K : ℝ) + 1) * ‖u‖ = K * ‖u‖ + ‖u‖ by ring, Real.exp_add]
    calc mehler g α u * |Real.log (mehler g α u)|
        ≤ (Real.exp (g 0) * Real.exp (K * ‖u‖) * M) * ((logBound g K + K) * Real.exp ‖u‖) :=
          mul_le_mul h1 (h2.trans h3) (abs_nonneg _) (by positivity)
      _ = Real.exp (g 0) * M * (logBound g K + K) * (Real.exp (K * ‖u‖) * Real.exp ‖u‖) := by
          ring
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.log (mehler g β u) + 1| ≤ logBound g K + 1 + K * ‖u‖ := by
      have := abs_log_mehler_le hg β u
      have := abs_add_le (Real.log (mehler g β u)) 1
      rw [abs_one] at this
      linarith
    have h2 : logBound g K + 1 + K * ‖u‖ ≤ (logBound g K + 1 + K) * Real.exp ‖u‖ := by
      nlinarith [Real.add_one_le_exp ‖u‖, norm_nonneg u]
    have h3 := abs_mehlerAngleDeriv_le hg hg'b β u
    have h4 : ‖u‖ + 1 ≤ Real.exp ‖u‖ := by linarith [Real.add_one_le_exp ‖u‖]
    have h5 : Real.exp (g 0) * Real.exp (K * ‖u‖) * K * (‖u‖ + 1) * M₁
        ≤ Real.exp (g 0) * Real.exp (K * ‖u‖) * K * Real.exp ‖u‖ * M₁ := by gcongr
    rw [show ((K : ℝ) + 2) * ‖u‖ = K * ‖u‖ + ‖u‖ + ‖u‖ by ring, Real.exp_add, Real.exp_add]
    calc |Real.log (mehler g β u) + 1| * |mehlerAngleDeriv g g' β u|
        ≤ ((logBound g K + 1 + K) * Real.exp ‖u‖) *
          (Real.exp (g 0) * Real.exp (K * ‖u‖) * K * Real.exp ‖u‖ * M₁) :=
          mul_le_mul (h1.trans h2) (h3.trans h5) (abs_nonneg _)
            (mul_nonneg (by linarith) (Real.exp_pos _).le)
      _ = Real.exp (g 0) * K * M₁ * (logBound g K + 1 + K) *
          (Real.exp (K * ‖u‖) * Real.exp ‖u‖ * Real.exp ‖u‖) := by ring

/-- The scaled logarithmic gradient `(c / mehler g α u) • mehlerGrad g g' α u` has norm at most
`|c| K |sin α|`. -/
theorem norm_smul_mehlerGrad_le (hg : LipschitzWith K g) (hg'b : ∀ x, ‖g' x‖ ≤ K) (α c : ℝ)
    (u : E) :
    ‖(c * (mehler g α u)⁻¹) • mehlerGrad g g' α u‖ ≤ |c| * (K * |Real.sin α|) := by
  have hp := mehler_pos hg α u
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hp, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [inv_mul_le_iff₀ hp, mul_comm (mehler g α u)]
  exact norm_mehlerGrad_le hg hg'b α u

/-- **Gaussian integration by parts in the rotated variable.** For fixed `w`, with
`G z = log mehler g α (sin α • w + cos α • z) + 1`,
`∫ ⟪a, z⟫ G z dγ(z) = ∫ ⟪cos α ∇ log mehler g α (sin α • w + cos α • z), a⟫ dγ(z)`. -/
theorem integral_inner_mul_logMehler (hg : LipschitzWith K g)
    (hgd : ∀ x, HasGradientAt g (g' x) x) (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K)
    (α : ℝ) (w a : E) :
    ∫ z, ⟪a, z⟫ * (Real.log (mehler g α (Real.sin α • w + Real.cos α • z)) + 1) ∂(stdGaussian E)
      = ∫ z, ⟪(Real.cos α * (mehler g α (Real.sin α • w + Real.cos α • z))⁻¹) •
          mehlerGrad g g' α (Real.sin α • w + Real.cos α • z), a⟫ ∂(stdGaussian E) := by
  have hL := logBound_nonneg (E := E) (g := g) (K := K)
  have hK := K.coe_nonneg
  have hpt : Continuous fun z : E => Real.sin α • w + Real.cos α • z := by fun_prop
  have hP := continuous_mehler hg α
  refine Kahane.integral_inner_mul_stdGaussian_of_le (A := logBound g K + 1 + K * ‖w‖ + K)
    (B := 1) (fun x e t => ?_) ?_ ?_ (fun z => ?_) (fun z => ?_) a
  · have hrw : ∀ s : ℝ, Real.sin α • w + Real.cos α • (x + s • e)
        = (Real.sin α • w + Real.cos α • x) + s • (Real.cos α • e) := by
      intro s; rw [smul_add, smul_comm (Real.cos α) s e]; abel
    simp only [hrw]
    have h := ((hasDerivAt_mehler_line hg hgd hg'c hg'b α (Real.sin α • w + Real.cos α • x)
      (Real.cos α • e) t).log (mehler_pos hg α _).ne').add_const 1
    refine h.congr_deriv ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  · exact ((hP.comp hpt).log fun z => (mehler_pos hg α _).ne').add continuous_const
  · exact (continuous_const.mul ((hP.comp hpt).inv₀ fun z => (mehler_pos hg α _).ne')).smul
      ((continuous_mehlerGrad hg hg'c hg'b α).comp hpt)
  · have h1 := abs_log_mehler_le hg α (Real.sin α • w + Real.cos α • z)
    have h2 := norm_sin_smul_add_cos_smul_le α w z
    have h3 := abs_add_le (Real.log (mehler g α (Real.sin α • w + Real.cos α • z))) 1
    rw [abs_one] at h3
    have h4 := mul_le_mul_of_nonneg_left h2 hK
    have hA : 0 ≤ logBound g K + 1 + K * ‖w‖ := by
      have := mul_nonneg hK (norm_nonneg w); linarith
    have h5 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp ‖z‖) (add_nonneg hA hK)
    have h6 := mul_nonneg hA (norm_nonneg z)
    rw [one_mul]
    nlinarith
  · have h1 := norm_smul_mehlerGrad_le hg hg'b α (Real.cos α) (Real.sin α • w + Real.cos α • z)
    have h2 : |Real.cos α| * (K * |Real.sin α|) ≤ K := by
      have := mul_le_mul (Real.abs_cos_le_one α) (mul_le_of_le_one_right hK
        (Real.abs_sin_le_one α)) (by positivity) zero_le_one
      linarith
    have hA : 0 ≤ logBound g K + 1 + K * ‖w‖ := by
      have := mul_nonneg hK (norm_nonneg w); linarith
    rw [one_mul]
    calc _ ≤ (K : ℝ) := h1.trans h2
      _ ≤ logBound g K + 1 + K * ‖w‖ + K := by linarith
      _ ≤ (logBound g K + 1 + K * ‖w‖ + K) * Real.exp ‖z‖ :=
        le_mul_of_one_le_right (by linarith) (Real.one_le_exp (norm_nonneg z))

/-- **The derivative bound.** On `[0, π / 2]`, `Φ'(α) ≤ K² sin α cos α ∫ exp ∘ g dγ`. -/
theorem mehlerEntropy_deriv_le (hg : LipschitzWith K g) (hgd : ∀ x, HasGradientAt g (g' x) x)
    (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π / 2) :
    ∫ u, (Real.log (mehler g α u) + 1) * mehlerAngleDeriv g g' α u ∂(stdGaussian E)
      ≤ K ^ 2 * Real.sin α * Real.cos α * ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  have hgc := hg.continuous
  have hK := K.coe_nonneg
  have hL := logBound_nonneg (E := E) (g := g) (K := K)
  have hs : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα1⟩
  have hrot := measurePreserving_rotPair (E := E) α
  have hlogc : Continuous fun u => Real.log (mehler g α u) :=
    (continuous_mehler hg α).log fun u => (mehler_pos hg α u).ne'
  set H : E × E → ℝ := fun q => (Real.log (mehler g α (rotPair α q).1) + 1) *
    (Real.exp (g q.1) * ⟪g' q.1, q.2⟫) with hHdef
  have hHc : Continuous H :=
    ((hlogc.comp (continuous_rotPair (E := E) α).fst).add continuous_const).mul
      ((Real.continuous_exp.comp (hgc.comp continuous_fst)).mul
        ((hg'c.comp continuous_fst).inner continuous_snd))
  have hHint : Integrable H ((stdGaussian E).prod (stdGaussian E)) := by
    refine (((Kahane.integrable_exp_mul_norm_stdGaussian (E := E) ((K : ℝ) + 1)).mul_prod
      (Kahane.integrable_exp_mul_norm_stdGaussian (E := E) 2)).const_mul
      ((logBound g K + 1 + K) * (Real.exp (g 0) * K))).mono' hHc.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    obtain ⟨q₁, q₂⟩ := q
    have h1 : |Real.log (mehler g α (rotPair α (q₁, q₂)).1) + 1|
        ≤ logBound g K + 1 + K * ‖(rotPair α (q₁, q₂)).1‖ := by
      have := abs_log_mehler_le hg α (rotPair α (q₁, q₂)).1
      have := abs_add_le (Real.log (mehler g α (rotPair α (q₁, q₂)).1)) 1
      rw [abs_one] at this
      linarith
    have h2 : ‖(rotPair α (q₁, q₂)).1‖ ≤ ‖q₁‖ + ‖q₂‖ := norm_sin_smul_add_cos_smul_le α q₁ q₂
    have h3 : logBound g K + 1 + K * ‖(rotPair α (q₁, q₂)).1‖
        ≤ (logBound g K + 1 + K) * (Real.exp ‖q₁‖ * Real.exp ‖q₂‖) := by
      rw [← Real.exp_add]
      have he := Real.add_one_le_exp (‖q₁‖ + ‖q₂‖)
      have h5 := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ logBound g K + 1 + K)
      have h6 := mul_le_mul_of_nonneg_left h2 hK
      have h7 := mul_nonneg (by linarith : 0 ≤ logBound g K + 1) (add_nonneg (norm_nonneg q₁)
        (norm_nonneg q₂))
      nlinarith
    have h4 := abs_exp_mul_inner_le (g := g) hg'b q₁ q₂
    have h5 := exp_le_of_lipschitz hg q₁
    have h6 : ‖q₂‖ ≤ Real.exp ‖q₂‖ := by linarith [Real.add_one_le_exp ‖q₂‖]
    rw [Real.norm_eq_abs, hHdef, abs_mul]
    calc |Real.log (mehler g α (rotPair α (q₁, q₂)).1) + 1| *
          |Real.exp (g q₁) * ⟪g' q₁, q₂⟫|
        ≤ ((logBound g K + 1 + K) * (Real.exp ‖q₁‖ * Real.exp ‖q₂‖)) *
          ((Real.exp (g 0) * Real.exp (K * ‖q₁‖)) * (K * Real.exp ‖q₂‖)) := by
          refine mul_le_mul (h1.trans h3) (h4.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul h5 (mul_le_mul_of_nonneg_left h6 hK) (by positivity) (by positivity)
      _ = (logBound g K + 1 + K) * (Real.exp (g 0) * K) *
          (Real.exp (((K : ℝ) + 1) * ‖q₁‖) * Real.exp (2 * ‖q₂‖)) := by
          rw [show ((K : ℝ) + 1) * ‖q₁‖ = K * ‖q₁‖ + ‖q₁‖ by ring,
            show (2 : ℝ) * ‖q₂‖ = ‖q₂‖ + ‖q₂‖ by ring, Real.exp_add, Real.exp_add]
          ring
  have hstep1 : ∫ u, (Real.log (mehler g α u) + 1) * mehlerAngleDeriv g g' α u ∂(stdGaussian E)
      = ∫ q, H q ∂((stdGaussian E).prod (stdGaussian E)) := by
    have hint1 : Integrable (fun p => H (rotPair α p)) ((stdGaussian E).prod (stdGaussian E)) :=
      (hrot.integrable_comp hHc.aestronglyMeasurable).2 hHint
    have hmap : ∫ q, H q ∂((stdGaussian E).prod (stdGaussian E))
        = ∫ p, H (rotPair α p) ∂((stdGaussian E).prod (stdGaussian E)) := by
      conv_lhs => rw [← hrot.map_eq]
      exact integral_map hrot.measurable.aemeasurable hHc.aestronglyMeasurable
    rw [hmap, integral_prod _ hint1]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hHdef, rotPair_rotPair]
    rw [mehlerAngleDeriv, ← integral_const_mul]
    rfl
  rw [hstep1, integral_prod _ hHint, ← integral_const_mul]
  refine integral_mono hHint.integral_prod_left
    ((Kahane.integrable_of_le_exp (f := fun x => Real.exp (g x)) (A := Real.exp (g 0)) (B := K)
      (by fun_prop) fun x => by
        rw [abs_of_pos (Real.exp_pos _)]; exact exp_le_of_lipschitz hg x).const_mul _)
    fun w => ?_
  have hH : ∀ z, H (w, z) = ⟪Real.exp (g w) • g' w, z⟫ *
      (Real.log (mehler g α (Real.sin α • w + Real.cos α • z)) + 1) := by
    intro z
    simp only [hHdef, rotPair, real_inner_smul_left]
    ring
  simp only [hH]
  rw [integral_inner_mul_logMehler hg hgd hg'c hg'b α w]
  have hz : ∀ z, ‖⟪(Real.cos α * (mehler g α (Real.sin α • w + Real.cos α • z))⁻¹) •
      mehlerGrad g g' α (Real.sin α • w + Real.cos α • z), Real.exp (g w) • g' w⟫‖
      ≤ K ^ 2 * Real.sin α * Real.cos α * Real.exp (g w) := by
    intro z
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 := norm_smul_mehlerGrad_le hg hg'b α (Real.cos α) (Real.sin α • w + Real.cos α • z)
    rw [abs_of_nonneg hc, abs_of_nonneg hs] at h1
    have h2 : ‖Real.exp (g w) • g' w‖ ≤ Real.exp (g w) * K := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hg'b w) (Real.exp_pos _).le
    calc _ ≤ (Real.cos α * (K * Real.sin α)) * (Real.exp (g w) * K) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = K ^ 2 * Real.sin α * Real.cos α * Real.exp (g w) := by ring
  have hb := norm_integral_le_of_norm_le_const (μ := stdGaussian E) (ae_of_all _ hz)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at hb
  exact (le_abs_self _).trans hb

/-- **The Gaussian logarithmic Sobolev inequality for exponential tilts.** If `g` has a continuous
gradient bounded by `K`, then `f = exp ∘ g` satisfies
`∫ f log f dγ ≤ (∫ f dγ) log (∫ f dγ) + (K² / 2) ∫ f dγ`. -/
theorem integral_mul_log_le_of_gradient (hg : LipschitzWith K g)
    (hgd : ∀ x, HasGradientAt g (g' x) x) (hg'c : Continuous g') (hg'b : ∀ x, ‖g' x‖ ≤ K) :
    ∫ x, Real.exp (g x) * Real.log (Real.exp (g x)) ∂(stdGaussian E)
      ≤ (∫ x, Real.exp (g x) ∂(stdGaussian E)) * Real.log (∫ x, Real.exp (g x) ∂(stdGaussian E))
        + (K : ℝ) ^ 2 / 2 * ∫ x, Real.exp (g x) ∂(stdGaussian E) := by
  set Z := ∫ x, Real.exp (g x) ∂(stdGaussian E)
  set Ψ : ℝ → ℝ := fun β => mehlerEntropy g β - (K : ℝ) ^ 2 / 2 * Z * Real.sin β ^ 2
  have hΨ : ∀ β, HasDerivAt Ψ
      ((∫ u, (Real.log (mehler g β u) + 1) * mehlerAngleDeriv g g' β u ∂(stdGaussian E))
        - (K : ℝ) ^ 2 / 2 * Z * (2 * Real.sin β * Real.cos β)) β := by
    intro β
    have h := ((Real.hasDerivAt_sin β).pow 2).const_mul ((K : ℝ) ^ 2 / 2 * Z)
    refine (hasDerivAt_mehlerEntropy hg hgd hg'c hg'b β).sub (h.congr_deriv ?_)
    push_cast
    ring
  have hanti : AntitoneOn Ψ (Icc 0 (π / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun β _ => (hΨ β).continuousAt.continuousWithinAt)
      (fun β _ => (hΨ β).differentiableAt.differentiableWithinAt) fun β hβ => ?_
    rw [interior_Icc] at hβ
    rw [(hΨ β).deriv]
    have := mehlerEntropy_deriv_le hg hgd hg'c hg'b hβ.1.le hβ.2.le
    linarith
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  have h := hanti ⟨le_rfl, hπ⟩ ⟨hπ, le_rfl⟩ hπ
  simp only [Ψ, mehlerEntropy, Real.sin_pi_div_two, Real.sin_zero, mehler_pi_div_two,
    mehler_zero] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

end LatticeProb.GaussLSI
