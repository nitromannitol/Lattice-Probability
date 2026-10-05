import Mathlib
import LatticeProb.Prob.MehlerSmoothing
import LatticeProb.Prob.GaussDensity

/-!
# Mehler interpolation in dimension `d` (Raic (2.3)-(2.5))

For `E = EuclideanSpace ℝ (Fin d)` and `γ = stdGaussian E` put
`mehlerI a f w = ∫ f (cos a • w + sin a • z) dγ(z)` and
`mehlerIS g w = Δ g w - ⟨∇g w, w⟩` (Laplacian as the sum of the second line derivatives along the
standard basis).

* `mehlerI_hasFDerivAt`, `mehlerI_fderiv_apply`: `∇ U_a g = cos a · U_a ∇g` for `g ∈ C¹_b`.
* `mehlerI_laplacian`: `Δ U_a f = cos² a · U_a Δf` for `f ∈ C²_b`.
* `mehlerI_stein` (Gaussian integration by parts in `ℝ^d`, via the density of `γ`),
  `mehlerI_stein_laplacian`: `E ⟨∇f(cos a w + sin a Z), Z⟩ = sin a · E Δf(cos a w + sin a Z)`.
* `mehlerI_hasDerivAt` (**heat equation**): `∂_a U_a f(w) = tan a · S (U_a f)(w)`, `0 < a < π/2`.
* `mehlerI_interpolation` (**interpolation identity**): for a probability space `(Ω, P)` and a
  measurable `W` with `E‖W‖ < ∞`,
  `E f(W) - γ f = - ∫_0^{π/2} tan a · E[(S U_a f)(W)] da`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

noncomputable section

/-- The Mehler interpolation `U_a f (w) = E f (cos a • w + sin a • Z)`, `Z ~ N(0, I_d)`. -/
def mehlerI {d : ℕ} (a : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, f (Real.cos a • w + Real.sin a • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The Stein operator `S g (w) = Δ g (w) - ⟨∇g (w), w⟩`; the Laplacian is the sum of the
second directional derivatives along the standard basis. -/
def mehlerIS {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ k : Fin d, iteratedDeriv 2
      (fun t : ℝ => g (w + t • EuclideanSpace.single k (1 : ℝ))) 0) - fderiv ℝ g w w

/-- The class `C²_b`: twice continuously differentiable, `f`, `Df`, `D²f` bounded. -/
def mehlerIClassC2b {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ (∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) ∧
    (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)

/-- The class `C¹_b`: continuously differentiable, `g` and `Dg` bounded. -/
def mehlerIClassC1b {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧ (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C)

/-- The directional derivative `D_e g (x) = Dg(x) e`. -/
def mehlerIDir {d : ℕ} (e : EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ g x e

theorem mehlerI_integrable_norm (d : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))).norm

/-- The Fréchet derivative in the base point of the Mehler interpolation of a `C¹_b` function. -/
theorem mehlerI_hasFDerivAt {d : ℕ} (a : ℝ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) (w : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (mehlerI a g)
      (∫ z, Real.cos a • fderiv ℝ g (Real.cos a • w + Real.sin a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) w := by
  obtain ⟨hg1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hg
  have hcg : Continuous g := hg1.continuous
  have hcd : Continuous (fderiv ℝ g) := hg1.continuous_fderiv one_ne_zero
  have hlin : Continuous fun z : EuclideanSpace ℝ (Fin d) => Real.cos a • w + Real.sin a • z := by
    fun_prop
  have hm : Continuous fun z : EuclideanSpace ℝ (Fin d) =>
      Real.cos a • fderiv ℝ g (Real.cos a • w + Real.sin a • z) :=
    (hcd.comp hlin).const_smul (Real.cos a)
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun w' z => g (Real.cos a • w' + Real.sin a • z))
    (F' := fun w' z => Real.cos a • fderiv ℝ g (Real.cos a • w' + Real.sin a • z))
    (x₀ := w) (s := Set.univ) (bound := fun _ => |Real.cos a| * C1) Filter.univ_mem
    (Filter.Eventually.of_forall fun w' =>
      (hcg.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hcg.comp (by fun_prop)).aestronglyMeasurable C0
      (ae_of_all _ fun z => by simpa using h0 _))
    hm.aestronglyMeasurable
    (ae_of_all _ fun z w' _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (h1 _) (abs_nonneg _))
    (integrable_const _)
    (ae_of_all _ fun z w' _ => by
      have h2 : HasFDerivAt (fun w'' : EuclideanSpace ℝ (Fin d) =>
          Real.cos a • w'' + Real.sin a • z)
          (Real.cos a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) w' := by
        simpa using ((hasFDerivAt_id w').const_smul (Real.cos a)).add_const (Real.sin a • z)
      have h3 := ((hg1.differentiable one_ne_zero) _).hasFDerivAt.comp w' h2
      refine h3.congr_fderiv ?_
      ext v
      simp)
  exact this

/-- A bounded continuous function composed with an affine map of the Gaussian is integrable. -/
theorem mehlerI_integrable_comp {d : ℕ} {G : Type*} [NormedAddCommGroup G]
    {h : EuclideanSpace ℝ (Fin d) → G} (hc : Continuous h) (C : ℝ) (hb : ∀ x, ‖h x‖ ≤ C)
    (p : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => h (p + t • z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  Integrable.of_bound (hc.comp (by fun_prop)).aestronglyMeasurable C
    (ae_of_all _ fun z => hb _)

theorem mehlerI_continuous {d : ℕ} (a : ℝ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) : Continuous (mehlerI a g) :=
  continuous_iff_continuousAt.2 fun w => (mehlerI_hasFDerivAt a hg w).continuousAt

theorem mehlerI_differentiable {d : ℕ} (a : ℝ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) : Differentiable ℝ (mehlerI a g) :=
  fun w => (mehlerI_hasFDerivAt a hg w).differentiableAt

theorem mehlerI_fderiv_apply {d : ℕ} (a : ℝ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) (w v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (mehlerI a g) w v = Real.cos a * mehlerI a (mehlerIDir v g) w := by
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.cos a • fderiv ℝ g (Real.cos a • w + Real.sin a • z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hg1, _, ⟨C1, h1⟩⟩ := hg
    have := (mehlerI_integrable_comp (hg1.continuous_fderiv one_ne_zero) C1 h1
      (Real.cos a • w) (Real.sin a)).smul (Real.cos a)
    exact this
  rw [(mehlerI_hasFDerivAt a hg w).fderiv, ContinuousLinearMap.integral_apply hint v]
  simp only [smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  rfl

/-- The line derivative of the Mehler interpolation of a `C¹_b` function. -/
theorem mehlerI_hasDerivAt_line {d : ℕ} (a : ℝ) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) (w e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mehlerI a g (w + s • e))
      (Real.cos a * mehlerI a (mehlerIDir e g) (w + t • e)) t := by
  have h1 : HasDerivAt (fun s : ℝ => w + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add w
  have h2 := (mehlerI_hasFDerivAt a hg (w + t • e)).comp_hasDerivAt t h1
  rw [← mehlerI_fderiv_apply a hg (w + t • e) e]
  exact h2.congr_deriv (by rw [← (mehlerI_hasFDerivAt a hg (w + t • e)).fderiv]) 

theorem mehlerIClassC2b.c1b {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) : mehlerIClassC1b f :=
  ⟨hf.1.of_le (by norm_num), hf.2.1, hf.2.2.1⟩

/-- The second derivative applied to two vectors. -/
theorem mehlerI_fderiv_dir {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ 2 f)
    (x v e : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (mehlerIDir e f) x v = iteratedFDeriv ℝ 2 f x ![v, e] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have h1 : HasFDerivAt (fun y => fderiv ℝ f y e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hd.hasFDerivAt
  show fderiv ℝ (fun y => fderiv ℝ f y e) x v = _
  rw [h1.fderiv, iteratedFDeriv_two_apply]
  simp

theorem mehlerIClassC2b.dir_c1b {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (e : EuclideanSpace ℝ (Fin d)) :
    mehlerIClassC1b (mehlerIDir e f) := by
  obtain ⟨hf2, _, ⟨C1, h1⟩, ⟨C2, h2⟩⟩ := hf
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (h2 0)
  refine ⟨?_, ⟨C1 * ‖e‖, fun x => ?_⟩, ⟨C2 * ‖e‖, fun x => ?_⟩⟩
  · exact (hf2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  · calc |mehlerIDir e f x| = ‖fderiv ℝ f x e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ f x‖ * ‖e‖ := (fderiv ℝ f x).le_opNorm e
      _ ≤ C1 * ‖e‖ := mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC2 (norm_nonneg _)) fun v => ?_
    rw [mehlerI_fderiv_dir hf2, Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 f x ![v, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ∏ i, ‖(![v, e] : Fin 2 → _) i‖ :=
          (iteratedFDeriv ℝ 2 f x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 f x‖ * (‖v‖ * ‖e‖) := by simp [Fin.prod_univ_two]
      _ ≤ C2 * (‖v‖ * ‖e‖) := mul_le_mul_of_nonneg_right (h2 x) (by positivity)
      _ = C2 * ‖e‖ * ‖v‖ := by ring

/-- Second line derivative of the Mehler interpolation of a `C²_b` function. -/
theorem mehlerI_iteratedDeriv_two_line {d : ℕ} (a : ℝ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (w e : EuclideanSpace ℝ (Fin d)) :
    iteratedDeriv 2 (fun t : ℝ => mehlerI a f (w + t • e)) 0
      = Real.cos a ^ 2 * mehlerI a (mehlerIDir e (mehlerIDir e f)) w := by
  have h1 : deriv (fun t : ℝ => mehlerI a f (w + t • e))
      = fun t => Real.cos a * mehlerI a (mehlerIDir e f) (w + t • e) :=
    funext fun t => (mehlerI_hasDerivAt_line a hf.c1b w e t).deriv
  have h2 := (mehlerI_hasDerivAt_line a (hf.dir_c1b e) w e 0).const_mul (Real.cos a)
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2.deriv]
  simp
  ring

open scoped ENNReal NNReal

/-- The real density of the standard Gaussian on `ℝ^d`. -/
def mehlerIRho (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((Real.sqrt (2 * Real.pi))⁻¹) ^ d * Real.exp (-(‖y‖ ^ 2 / 2))

theorem mehlerIRho_pos (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) : 0 < mehlerIRho d y := by
  unfold mehlerIRho; positivity

theorem mehlerIRho_continuous (d : ℕ) : Continuous (mehlerIRho d) := by
  unfold mehlerIRho; fun_prop

theorem mehlerI_prod_gaussianPDF (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    ∏ i, gaussianPDF 0 1 (y i) = ENNReal.ofReal (mehlerIRho d y) := by
  have h1 : ∀ i, gaussianPDF 0 1 (y i) = ENNReal.ofReal (mehlerPhi (y i)) := fun i => by
    rw [gaussianPDF, mehlerPhi_eq]
  simp_rw [h1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (mehlerPhi_pos _).le)]
  congr 1
  simp only [mehlerPhi, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Real.exp_sum, mehlerIRho]
  congr 3
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_neg_distrib, ← Finset.sum_div]
  simp

theorem mehlerI_stdGaussian_eq_withDensity_real (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
      = (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
          fun y => ENNReal.ofReal (mehlerIRho d y) := by
  rw [stdGaussian_euclidean_eq_withDensity (Fin d)]
  congr 1
  funext y
  exact mehlerI_prod_gaussianPDF d y

theorem mehlerI_measurable_ofReal_rho (d : ℕ) :
    Measurable fun y : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (mehlerIRho d y) :=
  ENNReal.measurable_ofReal.comp (mehlerIRho_continuous d).measurable

/-- A Gaussian integral as a Lebesgue integral against the density. -/
theorem mehlerI_integral_density {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : EuclideanSpace ℝ (Fin d) → G) :
    ∫ z, g z ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ x, mehlerIRho d x • g x := by
  rw [mehlerI_stdGaussian_eq_withDensity_real,
    integral_withDensity_eq_integral_toReal_smul (mehlerI_measurable_ofReal_rho d)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (mehlerIRho_pos d x).le]

theorem mehlerI_integrable_density {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    Integrable (fun x => mehlerIRho d x * g x) volume
      ↔ Integrable g (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [mehlerI_stdGaussian_eq_withDensity_real,
    integrable_withDensity_iff_integrable_smul' (mehlerI_measurable_ofReal_rho d)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (mehlerIRho_pos d x).le, smul_eq_mul]

theorem mehlerIRho_hasFDerivAt (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (mehlerIRho d) (-(mehlerIRho d x) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := ((h1.const_mul (-(1 / 2) : ℝ)).exp).const_mul (((Real.sqrt (2 * Real.pi))⁻¹) ^ d)
  have h3 : mehlerIRho d = fun y : EuclideanSpace ℝ (Fin d) =>
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ d * Real.exp (-(1 / 2) * ‖y‖ ^ 2) := by
    funext y
    simp only [mehlerIRho]
    congr 2
    ring
  rw [h3]
  refine h2.congr_fderiv ?_
  ext v
  simp
  ring

theorem mehlerI_integrable_inner {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => inner ℝ z v)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  ((mehlerI_integrable_norm d).mul_const ‖v‖).mono'
    (continuous_id.inner continuous_const).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using abs_real_inner_le_norm z v)

/-- **Gaussian integration by parts** (Stein's identity) in `ℝ^d`:
`E ⟨Z, v⟩ h(Z) = E ⟨∇h(Z), v⟩` for `h ∈ C¹_b`. -/
theorem mehlerI_stein {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : mehlerIClassC1b h)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ z, inner ℝ z v * h z ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ z, fderiv ℝ h z v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨hh1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hh
  have hcont : Continuous h := hh1.continuous
  have hcd : Continuous (fderiv ℝ h) := hh1.continuous_fderiv one_ne_zero
  have hdv : Continuous fun x => fderiv ℝ h x v := hcd.clm_apply continuous_const
  have hgh : Integrable h (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    Integrable.of_bound hcont.aestronglyMeasurable C0
      (ae_of_all _ fun z => by simpa using h0 z)
  have hgdh : Integrable (fun z => fderiv ℝ h z v) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    Integrable.of_bound hdv.aestronglyMeasurable (C1 * ‖v‖)
      (ae_of_all _ fun z => by
        calc ‖fderiv ℝ h z v‖ ≤ ‖fderiv ℝ h z‖ * ‖v‖ := (fderiv ℝ h z).le_opNorm v
          _ ≤ C1 * ‖v‖ := mul_le_mul_of_nonneg_right (h1 z) (norm_nonneg _))
  have hgih : Integrable (fun z => inner ℝ z v * h z)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (mehlerI_integrable_inner v).mul_bdd hcont.aestronglyMeasurable (c := C0)
      (ae_of_all _ fun z => by simpa using h0 z)
  have hrho : ∀ x, fderiv ℝ (mehlerIRho d) x v = -(mehlerIRho d x * inner ℝ x v) := fun x => by
    rw [(mehlerIRho_hasFDerivAt d x).fderiv]
    simp [innerSL_apply_apply]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (f := mehlerIRho d) (g := h) (v := v)
    (by
      have : (fun x => fderiv ℝ (mehlerIRho d) x v * h x)
          = fun x => -(mehlerIRho d x * (inner ℝ x v * h x)) :=
        funext fun x => by rw [hrho]; ring
      rw [this]
      exact ((mehlerI_integrable_density _).2 hgih).neg)
    ((mehlerI_integrable_density _).2 hgdh)
    ((mehlerI_integrable_density _).2 hgh)
    (fun x _ => (mehlerIRho_hasFDerivAt d x).differentiableAt)
    (fun x _ => hh1.differentiable one_ne_zero x)
  rw [mehlerI_integral_density, mehlerI_integral_density]
  simp only [smul_eq_mul]
  rw [key]
  simp_rw [hrho]
  rw [← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

/-! ### Calculus facts on `C¹_b` -/

theorem mehlerIClassC1b.comp_affine {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) (p : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mehlerIClassC1b (fun z => g (p + t • z)) ∧
      ∀ z v, fderiv ℝ (fun z => g (p + t • z)) z v = t * fderiv ℝ g (p + t • z) v := by
  obtain ⟨hg1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hg
  have hder : ∀ z, HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => g (p + t • z))
      ((fderiv ℝ g (p + t • z)).comp (t • ContinuousLinearMap.id ℝ _)) z := fun z => by
    have h2 : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin d) => p + t • z')
        (t • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) z := by
      simpa using ((hasFDerivAt_id z).const_smul t).const_add p
    exact ((hg1.differentiable one_ne_zero) _).hasFDerivAt.comp z h2
  have hform : ∀ z v, fderiv ℝ (fun z => g (p + t • z)) z v = t * fderiv ℝ g (p + t • z) v :=
    fun z v => by rw [(hder z).fderiv]; simp
  refine ⟨⟨hg1.comp (by fun_prop), ⟨C0, fun x => h0 _⟩, ⟨|t| * C1, fun z => ?_⟩⟩, hform⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg t)
    ((norm_nonneg _).trans (h1 0))) fun v => ?_
  rw [hform, norm_mul, Real.norm_eq_abs]
  calc |t| * ‖fderiv ℝ g (p + t • z) v‖ ≤ |t| * (‖fderiv ℝ g (p + t • z)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ g (p + t • z)).le_opNorm v) (abs_nonneg t)
    _ ≤ |t| * (C1 * ‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
          (abs_nonneg t)
    _ = |t| * C1 * ‖v‖ := by ring

theorem mehlerIClassC1b.dir_cont_bdd {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : mehlerIClassC1b g) (e : EuclideanSpace ℝ (Fin d)) :
    Continuous (mehlerIDir e g) ∧ ∃ C, ∀ x, |mehlerIDir e g x| ≤ C := by
  obtain ⟨hg1, _, ⟨C1, h1⟩⟩ := hg
  refine ⟨(hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const,
    ⟨C1 * ‖e‖, fun x => ?_⟩⟩
  calc |mehlerIDir e g x| = ‖fderiv ℝ g x e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ g x‖ * ‖e‖ := (fderiv ℝ g x).le_opNorm e
    _ ≤ C1 * ‖e‖ := mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg _)

/-- A continuous linear form is the sum of its values on the standard basis, weighted by the
coordinates. -/
theorem mehlerI_apply_eq_sum {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    L z = ∑ k : Fin d, inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
      L (EuclideanSpace.single k (1 : ℝ)) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply, real_inner_comm]

/-! ### The angle derivative -/

theorem mehlerI_angle_vec_norm_le {d : ℕ} (a : ℝ) (w z : EuclideanSpace ℝ (Fin d)) :
    ‖-(Real.sin a) • w + Real.cos a • z‖ ≤ ‖w‖ + ‖z‖ := by
  calc ‖-(Real.sin a) • w + Real.cos a • z‖
      ≤ ‖-(Real.sin a) • w‖ + ‖Real.cos a • z‖ := norm_add_le _ _
    _ = |Real.sin a| * ‖w‖ + |Real.cos a| * ‖z‖ := by
      rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * ‖w‖ + 1 * ‖z‖ := by
      gcongr
      · exact Real.abs_sin_le_one a
      · exact Real.abs_cos_le_one a
    _ = ‖w‖ + ‖z‖ := by ring

theorem mehlerI_angle_integrand_norm_le {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C1 : ℝ}
    (hC1 : 0 ≤ C1) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) (a : ℝ) (w z : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)‖
      ≤ C1 * (‖w‖ + ‖z‖) :=
  calc _ ≤ ‖fderiv ℝ f (Real.cos a • w + Real.sin a • z)‖ *
        ‖-(Real.sin a) • w + Real.cos a • z‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C1 * (‖w‖ + ‖z‖) :=
      mul_le_mul (h1 _) (mehlerI_angle_vec_norm_le a w z) (norm_nonneg _) hC1

/-- Differentiation in the angle under the Gaussian integral, for `f ∈ C¹_b`. -/
theorem mehlerI_hasDerivAt_angle {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC1b f) (w : EuclideanSpace ℝ (Fin d)) (a : ℝ) :
    HasDerivAt (fun a' : ℝ => mehlerI a' f w)
      (∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z)
        (-(Real.sin a) • w + Real.cos a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) a := by
  obtain ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hf
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hcf : Continuous f := hf1.continuous
  have hcd : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  have hlin : ∀ a' : ℝ, Continuous fun z : EuclideanSpace ℝ (Fin d) =>
      Real.cos a' • w + Real.sin a' • z := fun a' => by fun_prop
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin d) => C1 * (‖w‖ + ‖z‖))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ((integrable_const ‖w‖).add (mehlerI_integrable_norm d)).const_mul C1
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun a' z => f (Real.cos a' • w + Real.sin a' • z))
    (F' := fun a' z => fderiv ℝ f (Real.cos a' • w + Real.sin a' • z)
      (-(Real.sin a') • w + Real.cos a' • z)) (x₀ := a)
    (s := Set.univ) (bound := fun z => C1 * (‖w‖ + ‖z‖)) Filter.univ_mem
    (Filter.Eventually.of_forall fun a' => (hcf.comp (hlin a')).aestronglyMeasurable)
    (Integrable.of_bound (hcf.comp (hlin a)).aestronglyMeasurable C0
      (ae_of_all _ fun z => by simpa using h0 _))
    (((hcd.comp (hlin a)).clm_apply (by fun_prop)).aestronglyMeasurable)
    (ae_of_all _ fun z a' _ => by
      exact mehlerI_angle_integrand_norm_le hC1 h1 a' w z)
    hint
    (ae_of_all _ fun z a' _ => by
      have h2 : HasDerivAt (fun a'' : ℝ => Real.cos a'' • w + Real.sin a'' • z)
          (-(Real.sin a') • w + Real.cos a' • z) a' := by
        have := ((Real.hasDerivAt_cos a').smul_const w).add ((Real.hasDerivAt_sin a').smul_const z)
        exact this
      exact ((hf1.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt a' h2)
  exact this.2

/-! ### The Laplacian and the commutation formulas -/

/-- The Laplacian: the sum of the second directional derivatives along the standard basis. -/
def mehlerILap {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ k : Fin d, mehlerIDir (EuclideanSpace.single k (1 : ℝ))
    (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f) x

theorem mehlerI_integrable_of_cont_bdd {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hb : ∃ C, ∀ x, |h x| ≤ C) (p : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => h (p + t • z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨C, hC⟩ := hb
  exact mehlerI_integrable_comp hc C (fun x => by simpa using hC x) p t

/-- Gaussian integration by parts, in the form used for the angle derivative:
`E ⟨∇f(cos a • w + sin a • Z), Z⟩ = sin a · E Δf(cos a • w + sin a • Z)`. -/
theorem mehlerI_stein_laplacian {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = Real.sin a * ∫ z, mehlerILap f (Real.cos a • w + Real.sin a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hI : ∀ k : Fin d, Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
        mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f (Real.cos a • w + Real.sin a • z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun k => by
    obtain ⟨hc, ⟨C, hC⟩⟩ := hf.c1b.dir_cont_bdd (EuclideanSpace.single k (1 : ℝ))
    exact (mehlerI_integrable_inner _).mul_bdd (c := C)
      (hc.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun z => by simpa using hC _)
  have hII : ∀ k : Fin d, Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      mehlerIDir (EuclideanSpace.single k (1 : ℝ))
        (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f) (Real.cos a • w + Real.sin a • z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun k =>
    mehlerI_integrable_of_cont_bdd
      ((hf.dir_c1b (EuclideanSpace.single k (1 : ℝ))).dir_cont_bdd _).1
      ((hf.dir_c1b (EuclideanSpace.single k (1 : ℝ))).dir_cont_bdd _).2 _ _
  have hterm : ∀ k : Fin d, ∫ z, inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
        mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = Real.sin a * ∫ z, mehlerIDir (EuclideanSpace.single k (1 : ℝ))
          (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f) (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := fun k => by
    obtain ⟨hc, hl⟩ := (hf.dir_c1b (EuclideanSpace.single k (1 : ℝ))).comp_affine
      (Real.cos a • w) (Real.sin a)
    rw [mehlerI_stein hc (EuclideanSpace.single k (1 : ℝ))]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [hl]
    rfl
  calc ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ z, ∑ k : Fin d, inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
        mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_congr_ae (ae_of_all _ fun z => mehlerI_apply_eq_sum _ z)
    _ = ∑ k : Fin d, ∫ z, inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
        mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := integral_finsetSum _ fun k _ => hI k
    _ = ∑ k : Fin d, Real.sin a * ∫ z, mehlerIDir (EuclideanSpace.single k (1 : ℝ))
          (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) f) (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := Finset.sum_congr rfl fun k _ => hterm k
    _ = Real.sin a * ∫ z, mehlerILap f (Real.cos a • w + Real.sin a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← integral_finsetSum _ fun k _ => hII k]
        rfl

/-- The derivative in the angle, in terms of the gradient and the Laplacian of `f`. -/
theorem mehlerI_angle_integral_eq {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -(Real.sin a) * ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) w
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        + Real.cos a * (Real.sin a * ∫ z, mehlerILap f (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  obtain ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hf.c1b
  have hcd : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  have hlin : Continuous fun z : EuclideanSpace ℝ (Fin d) => Real.cos a • w + Real.sin a • z := by
    fun_prop
  have hint1 : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ f (Real.cos a • w + Real.sin a • z) w)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    mehlerI_integrable_of_cont_bdd (hf.c1b.dir_cont_bdd w).1 (hf.c1b.dir_cont_bdd w).2 _ _
  have hint2 : Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ f (Real.cos a • w + Real.sin a • z) z)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ((mehlerI_integrable_norm d).const_mul C1).mono'
      ((hcd.comp hlin).clm_apply continuous_id).aestronglyMeasurable
      (ae_of_all _ fun z => by
        calc ‖fderiv ℝ f (Real.cos a • w + Real.sin a • z) z‖
            ≤ ‖fderiv ℝ f (Real.cos a • w + Real.sin a • z)‖ * ‖z‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ C1 * ‖z‖ := mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
  calc ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ z, (-(Real.sin a) * fderiv ℝ f (Real.cos a • w + Real.sin a • z) w
          + Real.cos a * fderiv ℝ f (Real.cos a • w + Real.sin a • z) z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_congr_ae (ae_of_all _ fun z => by
          simp only [map_add, map_smul, smul_eq_mul])
    _ = -(Real.sin a) * ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) w
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        + Real.cos a * ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) z
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = _ := by rw [mehlerI_stein_laplacian hf a w]

theorem mehlerI_laplacian {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ∑ k : Fin d, iteratedDeriv 2
        (fun t : ℝ => mehlerI a f (w + t • EuclideanSpace.single k (1 : ℝ))) 0
      = Real.cos a ^ 2 * mehlerI a (mehlerILap f) w := by
  simp_rw [mehlerI_iteratedDeriv_two_line a hf w]
  rw [← Finset.mul_sum]
  congr 1
  unfold mehlerI mehlerILap
  rw [integral_finsetSum]
  intro k _
  exact mehlerI_integrable_of_cont_bdd
    ((hf.dir_c1b (EuclideanSpace.single k (1 : ℝ))).dir_cont_bdd _).1
    ((hf.dir_c1b (EuclideanSpace.single k (1 : ℝ))).dir_cont_bdd _).2 _ _

theorem mehlerIS_mehlerI {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    mehlerIS (mehlerI a f) w
      = Real.cos a ^ 2 * ∫ z, mehlerILap f (Real.cos a • w + Real.sin a • z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        - Real.cos a * ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) w
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  unfold mehlerIS
  rw [mehlerI_laplacian hf a w, mehlerI_fderiv_apply a hf.c1b w w]
  rfl

/-- The pointwise form of the heat equation:
`tan a · S (U_a f) (w) = ∫ ⟨∇f(cos a w + sin a z), -sin a w + cos a z⟩ dγ(z)`. -/
theorem mehlerI_tan_mehlerIS {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2)
    (w : EuclideanSpace ℝ (Fin d)) :
    Real.tan a * mehlerIS (mehlerI a f) w
      = ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hc : Real.cos a ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩).ne'
  rw [mehlerI_angle_integral_eq hf a w, mehlerIS_mehlerI hf a w, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **The heat equation** for the Mehler interpolation of a `C²_b` function:
`∂_a U_a f = tan a · S (U_a f)` for `0 < a < π/2`. -/
theorem mehlerI_hasDerivAt {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2)
    (w : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun a' : ℝ => mehlerI a' f w) (Real.tan a * mehlerIS (mehlerI a f) w) a := by
  rw [mehlerI_tan_mehlerIS hf ha0 ha1 w]
  exact mehlerI_hasDerivAt_angle hf.c1b w a

/-! ### The interpolation identity -/

/-- The angle derivative of the Mehler interpolation, as a function of the base point. -/
def mehlerIAng {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (a : ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

theorem mehlerIAng_norm_le {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C1 : ℝ}
    (hC1 : 0 ≤ C1) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    ‖mehlerIAng f a w‖
      ≤ C1 * (‖w‖ + ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin d) => C1 * (‖w‖ + ‖z‖))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    ((integrable_const ‖w‖).add (mehlerI_integrable_norm d)).const_mul C1
  calc ‖mehlerIAng f a w‖ ≤ ∫ z, C1 * (‖w‖ + ‖z‖) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        norm_integral_le_of_norm_le hint
          (ae_of_all _ fun z => mehlerI_angle_integrand_norm_le hC1 h1 a w z)
    _ = C1 * (‖w‖ + ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
        rw [integral_const_mul, integral_add (integrable_const _) (mehlerI_integrable_norm d),
          integral_const]
        simp

theorem mehlerIAng_stronglyMeasurable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC1b f) (a : ℝ) : StronglyMeasurable (mehlerIAng f a) := by
  have hcd : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv one_ne_zero
  have hcont : Continuous (Function.uncurry fun (w z : EuclideanSpace ℝ (Fin d)) =>
      fderiv ℝ f (Real.cos a • w + Real.sin a • z) (-(Real.sin a) • w + Real.cos a • z)) := by
    have h2 : Continuous fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        Real.cos a • p.1 + Real.sin a • p.2 := by fun_prop
    exact (hcd.comp h2).clm_apply (by fun_prop)
  exact hcont.stronglyMeasurable.integral_prod_right

theorem mehlerI_norm_le {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {C0 : ℝ}
    (h0 : ∀ x, |f x| ≤ C0) (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ‖mehlerI a f w‖ ≤ C0 := by
  have := norm_integral_le_of_norm_le (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (f := fun z => f (Real.cos a • w + Real.sin a • z))
    (integrable_const C0) (ae_of_all _ fun z => by simpa using h0 (Real.cos a • w + Real.sin a • z))
  unfold mehlerI
  simpa using this

/-- The derivative of `a ↦ E U_a f (W)` is `E` of the angle derivative, for every angle. -/
theorem mehlerI_integral_hasDerivAt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → EuclideanSpace ℝ (Fin d)) (hW : Measurable W)
    (hWint : Integrable (fun ω => ‖W ω‖) P) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC1b f) (a : ℝ) :
    HasDerivAt (fun a' : ℝ => ∫ ω, mehlerI a' f (W ω) ∂P)
      (∫ ω, mehlerIAng f a (W ω) ∂P) a := by
  obtain ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hf
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hf' : mehlerIClassC1b f := ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩
  have hbd : Integrable (fun ω => C1 * (‖W ω‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) P :=
    (hWint.add (integrable_const _)).const_mul C1
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := P)
    (F := fun a' ω => mehlerI a' f (W ω)) (F' := fun a' ω => mehlerIAng f a' (W ω))
    (x₀ := a) (s := Set.univ) (bound := fun ω => C1 * (‖W ω‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) Filter.univ_mem
    (Filter.Eventually.of_forall fun a' =>
      ((mehlerI_continuous a' hf').measurable.comp hW).aestronglyMeasurable)
    (Integrable.of_bound
      ((mehlerI_continuous a hf').measurable.comp hW).aestronglyMeasurable C0
      (ae_of_all _ fun ω => mehlerI_norm_le h0 a (W ω)))
    (((mehlerIAng_stronglyMeasurable hf' a).measurable.comp hW).aestronglyMeasurable)
    (ae_of_all _ fun ω a' _ => mehlerIAng_norm_le hC1 h1 a' (W ω))
    hbd
    (ae_of_all _ fun ω a' _ => mehlerI_hasDerivAt_angle hf' (W ω) a')
  exact this.2

/-- The derivative `a ↦ E[∂_a U_a f(W)]` is interval integrable on `[0, π/2]` (it is bounded
and measurable, being a derivative). -/
theorem mehlerI_integral_angle_intervalIntegrable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → EuclideanSpace ℝ (Fin d))
    (hW : Measurable W) (hWint : Integrable (fun ω => ‖W ω‖) P)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : mehlerIClassC1b f) :
    IntervalIntegrable (fun a : ℝ => ∫ ω, mehlerIAng f a (W ω) ∂P) volume 0 (Real.pi / 2) := by
  obtain ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hf
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hf' : mehlerIClassC1b f := ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩
  have hbd : Integrable (fun ω => C1 * (‖W ω‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) P :=
    (hWint.add (integrable_const _)).const_mul C1
  have hmeas : Measurable fun a : ℝ => ∫ ω, mehlerIAng f a (W ω) ∂P := by
    have : (fun a : ℝ => ∫ ω, mehlerIAng f a (W ω) ∂P)
        = deriv (fun a' : ℝ => ∫ ω, mehlerI a' f (W ω) ∂P) :=
      funext fun a => (mehlerI_integral_hasDerivAt P W hW hWint hf' a).deriv.symm
    rw [this]
    exact measurable_deriv _
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
  exact Measure.integrableOn_of_bounded (by simp) hmeas.aestronglyMeasurable
    (ae_of_all _ fun a => norm_integral_le_of_norm_le hbd
      (ae_of_all _ fun ω => mehlerIAng_norm_le hC1 h1 a (W ω)))

/-- The integrand of the interpolation identity is integrable on `(0, π/2)`; there is no
singularity at `π/2`, because `tan a · S U_a f (w) = ∂_a U_a f (w)` is bounded by
`C (‖w‖ + E‖Z‖)`. -/
theorem mehlerI_interpolation_integrableOn {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → EuclideanSpace ℝ (Fin d))
    (hW : Measurable W) (hWint : Integrable (fun ω => ‖W ω‖) P)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : mehlerIClassC2b f) :
    IntegrableOn (fun a : ℝ => Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le hpi).1
    (mehlerI_integral_angle_intervalIntegrable P W hW hWint hf.c1b)
  refine h.congr_fun (fun a ha => ?_) measurableSet_Ioo
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  exact (mehlerI_tan_mehlerIS hf ha.1 ha.2 (W ω)).symm

/-- **The interpolation identity** (Raic (2.5)):
`E f(W) - γ f = - ∫_0^{π/2} tan a · E[(S U_a f)(W)] da`. -/
theorem mehlerI_interpolation {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → EuclideanSpace ℝ (Fin d)) (hW : Measurable W)
    (hWint : Integrable (fun ω => ‖W ω‖) P) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) :
    ∫ ω, f (W ω) ∂P - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -∫ a in Set.Ioo 0 (Real.pi / 2),
          Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => mehlerI_integral_hasDerivAt P W hW hWint hf.c1b a)
    (mehlerI_integral_angle_intervalIntegrable P W hW hWint hf.c1b)
  have hΦ0 : ∫ ω, mehlerI 0 f (W ω) ∂P = ∫ ω, f (W ω) ∂P := by simp [mehlerI]
  have hΦ1 : ∫ ω, mehlerI (Real.pi / 2) f (W ω) ∂P
      = ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simp [mehlerI]
  have hIoo : ∫ a in Set.Ioo 0 (Real.pi / 2), ∫ ω, mehlerIAng f a (W ω) ∂P
      = ∫ a in Set.Ioo 0 (Real.pi / 2),
          Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P := by
    refine setIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (mehlerI_tan_mehlerIS hf ha.1 ha.2 (W ω)).symm
  rw [← hIoo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi, hftc, hΦ0,
    hΦ1]
  ring

/-! ### Bridges: the Stein operator through `iteratedFDeriv`, and the pointwise bound -/

theorem mehlerI_hasDerivAt_line_of_differentiable {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : Differentiable ℝ h) (x e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (x + s • e)) (fderiv ℝ h (x + t • e) e) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  exact (hh _).hasFDerivAt.comp_hasDerivAt t h1

/-- The second derivative along a line is the second Fréchet derivative on `(e, e)`. -/
theorem mehlerI_iteratedDeriv_two_line_eq {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ 2 g) (x e : EuclideanSpace ℝ (Fin d)) :
    iteratedDeriv 2 (fun t : ℝ => g (x + t • e)) 0 = iteratedFDeriv ℝ 2 g x ![e, e] := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hDd : Differentiable ℝ (mehlerIDir e g) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  have h1 : deriv (fun t : ℝ => g (x + t • e)) = fun t => mehlerIDir e g (x + t • e) :=
    funext fun t => (mehlerI_hasDerivAt_line_of_differentiable hgd x e t).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1,
    (mehlerI_hasDerivAt_line_of_differentiable hDd x e 0).deriv]
  simp only [zero_smul, add_zero]
  exact mehlerI_fderiv_dir hg x e e

/-- The Stein operator through `iteratedFDeriv`: `S g = ∑ₖ D²g(e_k, e_k) - ⟨∇g, w⟩`. -/
theorem mehlerIS_eq_iteratedFDeriv {d : ℕ} {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ 2 g) (w : EuclideanSpace ℝ (Fin d)) :
    mehlerIS g w = (∑ k : Fin d, iteratedFDeriv ℝ 2 g w
        ![EuclideanSpace.single k (1 : ℝ), EuclideanSpace.single k (1 : ℝ)])
      - fderiv ℝ g w w := by
  unfold mehlerIS
  congr 1
  exact Finset.sum_congr rfl fun k _ => mehlerI_iteratedDeriv_two_line_eq hg w _

/-- The Laplacian through `iteratedFDeriv`. -/
theorem mehlerILap_eq_iteratedFDeriv {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ 2 f) (x : EuclideanSpace ℝ (Fin d)) :
    mehlerILap f x = ∑ k : Fin d, iteratedFDeriv ℝ 2 f x
        ![EuclideanSpace.single k (1 : ℝ), EuclideanSpace.single k (1 : ℝ)] :=
  Finset.sum_congr rfl fun _ _ => mehlerI_fderiv_dir hf x _ _

/-- No singularity at `π/2`: `|tan a · S U_a f (w)| ≤ C₁ (‖w‖ + E‖Z‖)`, where `C₁` bounds
`‖Df‖`. -/
theorem mehlerI_tan_mehlerIS_norm_le {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : mehlerIClassC2b f) {C1 : ℝ} (hC1 : 0 ≤ C1) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (w : EuclideanSpace ℝ (Fin d)) :
    |Real.tan a * mehlerIS (mehlerI a f) w|
      ≤ C1 * (‖w‖ + ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  rw [mehlerI_tan_mehlerIS hf ha0 ha1 w, ← Real.norm_eq_abs]
  exact mehlerIAng_norm_le hC1 h1 a w

end

end LatticeProb
