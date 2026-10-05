import Mathlib
import LatticeProb.Prob.PittStatements
import LatticeProb.Prob.GaussDensity

/-!
# Pitt's Gaussian association theorem for a nondegenerate covariance (packet P25)

`pitt_nondeg k hsm : PittNondegStmt k` for `hsm : PittSmoothStmt k`: association of bounded Borel
coordinatewise nondecreasing functions under `multivariateGaussian 0 S`, `S` positive definite
with nonnegative entries, from the `C²_b` case by mollification.

* `pitt_multivariateGaussian_ac`: for `S` positive definite, `multivariateGaussian 0 S ≪ volume`.
* `pittMollify k n f = ψ_n ⋆ f`, `ψ_n` the normalised `ContDiffBump` of radii
  `1 / (2 (n + 1))`, `1 / (n + 1)`.  For `f` bounded Borel:
  `pittMollify_c2b` (`ψ_n ⋆ f` is `C²_b`, via `pitt_conv_iteratedFDeriv_bdd`: all derivatives of
  `ψ ⋆ f` are bounded when `ψ` is smooth with compact support),
  `pittMollify_abs_le` (`|ψ_n ⋆ f| ≤ M`), `pittMollify_mono` (`PittMono` is preserved),
  `pittMollify_ae_tendsto` (`ψ_n ⋆ f → f` Lebesgue-a.e., Lebesgue differentiation).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Convolution

namespace LatticeProb

/-- The standard Gaussian on `ℝ^k` is absolutely continuous w.r.t. Lebesgue measure. -/
theorem pitt_stdGaussian_ac (k : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin k)) ≪ (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
  rw [stdGaussian_euclidean_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- A unit of the algebra of continuous endomorphisms has nonzero determinant. -/
theorem pitt_det_ne_zero_of_isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (h : IsUnit A) : A.det ≠ 0 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : LinearMap.det ((↑u : E →L[ℝ] E) : E →ₗ[ℝ] E) *
      LinearMap.det ((↑u⁻¹ : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.det_comp]
    have : (((↑u : E →L[ℝ] E) : E →ₗ[ℝ] E) ∘ₗ ((↑u⁻¹ : E →L[ℝ] E) : E →ₗ[ℝ] E)) =
      LinearMap.id := by
      ext x
      simp [← mul_apply_eq_comp]
    rw [this, LinearMap.det_id]
  intro h0
  have : (↑u : E →L[ℝ] E).det = 0 := h0
  simp only [ContinuousLinearMap.det] at this
  rw [this, zero_mul] at h1
  exact zero_ne_one h1

/-- A nondegenerate centred Gaussian on `ℝ^k` is absolutely continuous w.r.t. Lebesgue
measure: it is the image of the standard Gaussian under the invertible `CFC.sqrt S`. -/
theorem pitt_multivariateGaussian_ac {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S ≪
      (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA
  have hS0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ S := hS.posSemidef.nonneg
  have hSu : IsUnit S := hS.isUnit
  have hsu : IsUnit (CFC.sqrt S) := (CFC.isUnit_sqrt_iff S hS0).2 hSu
  have hAu : IsUnit A := hsu.map _
  have hdet : A.det ≠ 0 := pitt_det_ne_zero_of_isUnit A hAu
  have hqmp := Measure.ContinuousLinearMap.quasiMeasurePreserving
    (volume : Measure (EuclideanSpace ℝ (Fin k))) A hdet
  have hmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin k) => (0 : EuclideanSpace ℝ (Fin k)) + A x) := by
    fun_prop
  have hfun : (fun x : EuclideanSpace ℝ (Fin k) => (0 : EuclideanSpace ℝ (Fin k)) + A x) = A := by
    funext x; simp
  unfold multivariateGaussian
  refine ((pitt_stdGaussian_ac k).map hmeas).trans ?_
  rw [hfun]
  exact hqmp.absolutelyContinuous


section Conv

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [FiniteDimensional ℝ G] {μ : Measure G} [μ.IsAddHaarMeasure]

omit [BorelSpace G] in
/-- A bounded measurable function is locally integrable for a Haar measure. -/
theorem pitt_locallyIntegrable_of_bounded {f : G → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : LocallyIntegrable f μ := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded (M := M) hK.measure_lt_top.ne
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by simpa using hM x)

/-- Bound on all iterated derivatives of `g ⋆ f` for `g` smooth with compact support and `f`
bounded and measurable. -/
theorem pitt_conv_iteratedFDeriv_bdd {f : G → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (r : ℕ) :
    ∀ (E₁ F : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F]
      [NormedSpace ℝ F] (L : E₁ →L[ℝ] ℝ →L[ℝ] F) (g : G → E₁), HasCompactSupport g →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ r (g ⋆[L, μ] f) x‖ ≤ C := by
  induction r with
  | zero =>
    intro E₁ F _ _ _ _ L g hcg hg
    have hgc : Continuous g := hg.continuous
    have hint : Integrable (fun t => ‖g t‖) μ :=
      (hgc.norm).integrable_of_hasCompactSupport hcg.norm
    refine ⟨∫ t, ‖L‖ * M * ‖g t‖ ∂μ, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero, convolution_def]
    refine norm_integral_le_of_norm_le (hint.const_mul (‖L‖ * M)) (Filter.Eventually.of_forall
      fun t => ?_)
    calc ‖L (g t) (f (x - t))‖ ≤ ‖L‖ * ‖g t‖ * ‖f (x - t)‖ := L.le_opNorm₂ _ _
      _ ≤ ‖L‖ * ‖g t‖ * M := by
        gcongr
        simpa using hM (x - t)
      _ = ‖L‖ * M * ‖g t‖ := by ring
  | succ r ih =>
    intro E₁ F _ _ _ _ L g hcg hg
    have hf' : LocallyIntegrable f μ := pitt_locallyIntegrable_of_bounded hf hM
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
    have hder : fderiv ℝ (g ⋆[L, μ] f) = (fderiv ℝ g ⋆[L.precompL G, μ] f) := by
      funext x
      exact (hcg.hasFDerivAt_convolution_left L hg1 hf' x).fderiv
    have hg' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) :=
      hg.fderiv_right (by exact_mod_cast le_rfl)
    obtain ⟨C, hC⟩ := ih (G →L[ℝ] E₁) (G →L[ℝ] F) (L.precompL G) (fderiv ℝ g)
      (hcg.fderiv ℝ) hg'
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hder]
    exact hC x

end Conv

section Mollifier

/-- The bump function of radii `1 / (2 (n + 1))` and `1 / (n + 1)`. -/
noncomputable def pittBump (k n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) hn]
    nlinarith

/-- The mollifying kernel: the normalised bump. -/
noncomputable def pittKernel (k n : ℕ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  (pittBump k n).normed volume

/-- The mollification `ψ_n ⋆ f`. -/
noncomputable def pittMollify (k n : ℕ) (f : EuclideanSpace ℝ (Fin k) → ℝ) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  (pittKernel k n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

variable {k : ℕ}

theorem pittKernel_contDiff (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pittKernel k n) :=
  (pittBump k n).contDiff_normed (n := ⊤)

theorem pittKernel_hasCompactSupport (n : ℕ) : HasCompactSupport (pittKernel k n) :=
  (pittBump k n).hasCompactSupport_normed

theorem pittKernel_nonneg (n : ℕ) (t : EuclideanSpace ℝ (Fin k)) : 0 ≤ pittKernel k n t :=
  (pittBump k n).nonneg_normed t

theorem pittKernel_integral (n : ℕ) : ∫ t, pittKernel k n t = 1 :=
  (pittBump k n).integral_normed

theorem pittKernel_integrable (n : ℕ) : Integrable (pittKernel k n) :=
  (pittKernel_contDiff n).continuous.integrable_of_hasCompactSupport
    (pittKernel_hasCompactSupport n)

theorem pittMollify_apply (n : ℕ) (f : EuclideanSpace ℝ (Fin k) → ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    pittMollify k n f x = ∫ t, pittKernel k n t * f (x - t) := by
  simp [pittMollify, convolution_def]

theorem pitt_integrable_kernel_mul (n : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun t => pittKernel k n t * f (x - t)) := by
  refine Integrable.mono' ((pittKernel_integrable n).mul_const M) ?_ ?_
  · exact ((pittKernel_contDiff n).continuous.aestronglyMeasurable).mul
      ((hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, Real.norm_of_nonneg (pittKernel_nonneg n t)]
    exact mul_le_mul_of_nonneg_left (by simpa using hM (x - t)) (pittKernel_nonneg n t)

/-- Mollification does not increase the sup-norm bound. -/
theorem pittMollify_abs_le (n : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ} {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (x : EuclideanSpace ℝ (Fin k)) :
    |pittMollify k n f x| ≤ M := by
  rw [pittMollify_apply, ← Real.norm_eq_abs]
  calc ‖∫ t, pittKernel k n t * f (x - t)‖ ≤ ∫ t, pittKernel k n t * M := by
        refine norm_integral_le_of_norm_le ((pittKernel_integrable n).mul_const M)
          (Filter.Eventually.of_forall fun t => ?_)
        rw [norm_mul, Real.norm_of_nonneg (pittKernel_nonneg n t)]
        exact mul_le_mul_of_nonneg_left (by simpa using hM (x - t)) (pittKernel_nonneg n t)
    _ = M := by rw [integral_mul_const, pittKernel_integral, one_mul]


/-- `ψ_n ⋆ f` is `C^∞` for `f` bounded Borel. -/
theorem pittMollify_contDiff (m : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pittMollify k m f) :=
  (pittKernel_hasCompactSupport m).contDiff_convolution_left (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤) (pittKernel_contDiff m)
    (pitt_locallyIntegrable_of_bounded hf hM)

theorem pittMollify_iteratedFDeriv_bdd (m r : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ r (pittMollify k m f) x‖ ≤ C :=
  pitt_conv_iteratedFDeriv_bdd hf hM r ℝ ℝ (ContinuousLinearMap.lsmul ℝ ℝ) (pittKernel k m)
    (pittKernel_hasCompactSupport m) (pittKernel_contDiff m)

/-- The mollification of a bounded Borel function lies in `C²_b`. -/
theorem pittMollify_c2b (m : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) : mehlerIClassC2b (pittMollify k m f) := by
  refine ⟨(pittMollify_contDiff m hf hM).of_le (WithTop.coe_le_coe.2 le_top),
    ⟨M, pittMollify_abs_le m hM⟩, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := pittMollify_iteratedFDeriv_bdd m 1 hf hM
    refine ⟨C, fun x => ?_⟩
    have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := pittMollify k m f) (x := x) (n := 0)
    rw [norm_iteratedFDeriv_zero] at h
    rw [h]
    exact hC x
  · exact pittMollify_iteratedFDeriv_bdd m 2 hf hM

/-- Mollification preserves coordinatewise monotonicity. -/
theorem pittMollify_mono (m : ℕ) {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) (hmono : PittMono f) : PittMono (pittMollify k m f) := by
  intro x y hxy
  rw [pittMollify_apply, pittMollify_apply]
  refine integral_mono (pitt_integrable_kernel_mul m hf hM x)
    (pitt_integrable_kernel_mul m hf hM y) fun t => ?_
  refine mul_le_mul_of_nonneg_left (hmono _ _ fun i => ?_) (pittKernel_nonneg m t)
  simpa using sub_le_sub_right (hxy i) (t i)

/-- Lebesgue differentiation: `ψ_n ⋆ f → f` Lebesgue-almost everywhere. -/
theorem pittMollify_ae_tendsto {f : EuclideanSpace ℝ (Fin k) → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin k))),
      Tendsto (fun m : ℕ => pittMollify k m f x) atTop (𝓝 (f x)) := by
  refine ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := pittBump k)
    (l := atTop) (K := 2) ?_ ?_ (pitt_locallyIntegrable_of_bounded hf hM)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · refine Filter.Eventually.of_forall fun i => ?_
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    show 1 / ((i : ℝ) + 1) ≤ 2 * (1 / (2 * ((i : ℝ) + 1)))
    rw [le_iff_eq_or_lt]
    left
    field_simp

end Mollifier

/-- **Pitt's association inequality for a nondegenerate covariance**, from the smooth case. -/
theorem pitt_nondeg (k : ℕ) (hsm : PittSmoothStmt k) : PittNondegStmt k := by
  intro S hS hnn f g hfm hgm hbf hbg hfmono hgmono
  obtain ⟨Mf, hMf⟩ := hbf
  obtain ⟨Mg, hMg⟩ := hbg
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S with hν
  have hac : ν ≪ (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
    pitt_multivariateGaussian_ac hS
  have hfae : ∀ᵐ x ∂ν, Tendsto (fun m : ℕ => pittMollify k m f x) atTop (𝓝 (f x)) :=
    (pittMollify_ae_tendsto hfm hMf).filter_mono hac.ae_le
  have hgae : ∀ᵐ x ∂ν, Tendsto (fun m : ℕ => pittMollify k m g x) atTop (𝓝 (g x)) :=
    (pittMollify_ae_tendsto hgm hMg).filter_mono hac.ae_le
  have hcf : ∀ m : ℕ, Continuous (pittMollify k m f) := fun m =>
    (pittMollify_contDiff m hfm hMf).continuous
  have hcg : ∀ m : ℕ, Continuous (pittMollify k m g) := fun m =>
    (pittMollify_contDiff m hgm hMg).continuous
  have h1 : Tendsto (fun m : ℕ => ∫ x, pittMollify k m f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mf)
      (fun m => (hcf m).aestronglyMeasurable) (integrable_const Mf) (fun m => ?_) hfae
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact pittMollify_abs_le m hMf x
  have h2 : Tendsto (fun m : ℕ => ∫ x, pittMollify k m g x ∂ν) atTop (𝓝 (∫ x, g x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mg)
      (fun m => (hcg m).aestronglyMeasurable) (integrable_const Mg) (fun m => ?_) hgae
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact pittMollify_abs_le m hMg x
  have h3 : Tendsto (fun m : ℕ => ∫ x, pittMollify k m f x * pittMollify k m g x ∂ν) atTop
      (𝓝 (∫ x, f x * g x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Mf * Mg)
      (fun m => ((hcf m).mul (hcg m)).aestronglyMeasurable) (integrable_const (Mf * Mg))
      (fun m => ?_) ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (pittMollify_abs_le m hMf x) (pittMollify_abs_le m hMg x)
        (abs_nonneg _) hMf0
    · filter_upwards [hfae, hgae] with x hx hy
      exact hx.mul hy
  refine le_of_tendsto_of_tendsto' (h1.mul h2) h3 fun m => ?_
  exact hsm S hS.posSemidef hnn (pittMollify k m f) (pittMollify k m g)
    (pittMollify_c2b m hfm hMf) (pittMollify_c2b m hgm hMg)
    (pittMollify_mono m hfm hMf hfmono) (pittMollify_mono m hgm hMg hgmono)


end LatticeProb
