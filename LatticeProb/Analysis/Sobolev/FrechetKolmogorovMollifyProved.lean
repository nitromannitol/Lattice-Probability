/-
# The mollification step and the Fréchet–Kolmogorov theorem

For a nonnegative continuous compactly supported `ρ` of total mass one, the Fourier multiplier
`1 - 𝓕ρ` satisfies `‖1 - 𝓕ρ(ξ)‖² ≤ ∫ ρ(y) ‖𝐞⟪-y, ξ⟫ - 1‖² dy`
(`norm_one_sub_fourier_sq_le`), so for integrable `f` the squared `H^s` distance from `f` to
`f ⋆ ρ` is at most the `ρ`-average of the translation errors `‖f(· - y) - f‖²_{H^s}`
(`sobolevNormSq_sub_convReal_le`).  A normalized bump supported in a small ball gives
`SobolevMollificationEstimate`.

If `f` has compact support but is not integrable, some point has no neighbourhood on which `f` is
integrable.  Near that point the convolution with a bump that is positive on its open support
vanishes, so `f - f ⋆ ρ` is not integrable and its Sobolev norm is zero
(`not_integrable_sub_convReal`).  Together these give `FrechetKolmogorovMollify`, and with the
mollified compactness `frechetKolmogorovMollifiedCompact_holds` the Fréchet–Kolmogorov theorem
`FrechetKolmogorovH`.
-/
import LatticeProb.Analysis.Sobolev.ConvolutionJetsIntegrable
import LatticeProb.Analysis.Sobolev.FrechetKolmogorovMollifyResidual
import LatticeProb.Analysis.Sobolev.TranslationBound

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology

namespace LatticeProb.Sobolev

variable {d : ℕ}

/-- The Fourier character, as a complex-valued function, is continuous. -/
theorem continuous_fourierChar_coe : Continuous (fun t : ℝ => ((𝐞 t : Circle) : ℂ)) := by
  exact continuous_subtype_val.comp Real.continuous_fourierChar

/-- Jensen's inequality for the square against a continuous compactly supported probability
density. -/
theorem sq_integral_mul_le_integral_mul_sq {ρ a : Space d → ℝ} (hρc : Continuous ρ)
    (hρcs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (ha : Continuous a) :
    (∫ y, ρ y * a y) ^ 2 ≤ ∫ y, ρ y * a y ^ 2 := by
  set m := ∫ y, ρ y * a y with hm
  have hi : ∀ g : Space d → ℝ, Continuous g → Integrable (fun y => ρ y * g y) := fun g hg =>
    (hρc.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.mul_right (f' := g) hρcs)
  have i1 : Integrable (fun y => ρ y * a y ^ 2) := hi (fun y => a y ^ 2) (ha.pow 2)
  have i2 : Integrable (fun y => 2 * m * (ρ y * a y)) := (hi a ha).const_mul (2 * m)
  have i3 : Integrable (fun y => m ^ 2 * ρ y) :=
    (hρc.integrable_of_hasCompactSupport hρcs).const_mul (m ^ 2)
  have h0 : 0 ≤ ∫ y, ρ y * (a y - m) ^ 2 :=
    integral_nonneg fun y => mul_nonneg (hρ0 y) (sq_nonneg _)
  have e1 : ∫ y, ρ y * (a y - m) ^ 2
      = ∫ y, ((ρ y * a y ^ 2 - 2 * m * (ρ y * a y)) + m ^ 2 * ρ y) := by
    congr 1
    funext y
    ring
  have e2 : ∫ y, ((ρ y * a y ^ 2 - 2 * m * (ρ y * a y)) + m ^ 2 * ρ y)
      = (∫ y, (ρ y * a y ^ 2 - 2 * m * (ρ y * a y))) + ∫ y, m ^ 2 * ρ y :=
    integral_add (i1.sub i2) i3
  have e3 : ∫ y, (ρ y * a y ^ 2 - 2 * m * (ρ y * a y))
      = (∫ y, ρ y * a y ^ 2) - ∫ y, 2 * m * (ρ y * a y) := integral_sub i1 i2
  have e4 : ∫ y, 2 * m * (ρ y * a y) = 2 * m * m := integral_const_mul _ _
  have e5 : ∫ y, m ^ 2 * ρ y = m ^ 2 * 1 := by rw [integral_const_mul, hρ1]
  rw [e1, e2, e3, e4, e5] at h0
  nlinarith

/-- The Fourier multiplier `1 - 𝓕ρ` of a continuous compactly supported probability density is
controlled by the `ρ`-average of the squared phase errors. -/
theorem norm_one_sub_fourier_sq_le {ρ : Space d → ℝ} (hρc : Continuous ρ)
    (hρcs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1) (ξ : Space d) :
    ‖1 - 𝓕 (fun x => (ρ x : ℂ)) ξ‖ ^ 2
      ≤ ∫ y, ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ ^ 2 := by
  have hE : Continuous (fun y : Space d => ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ)) :=
    continuous_fourierChar_coe.comp (continuous_neg.inner continuous_const)
  have hac : Continuous (fun y : Space d => ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖) :=
    (hE.sub continuous_const).norm
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  have hP : Integrable (fun y => (ρ y : ℂ)) := hρi.ofReal
  have hPe : Integrable (fun y => (ρ y : ℂ) * ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ)) :=
    ((Complex.continuous_ofReal.comp hρc).mul hE).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (hρcs.comp_left Complex.ofReal_zero))
  have hrep : 1 - 𝓕 (fun x => (ρ x : ℂ)) ξ
      = ∫ y, (ρ y : ℂ) * (1 - ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ)) := by
    have h1 : ∫ y, (ρ y : ℂ) * (1 - ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ))
        = (∫ y, (ρ y : ℂ)) - ∫ y, (ρ y : ℂ) * ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) := by
      rw [← integral_sub hP hPe]
      congr 1
      funext y
      ring
    have h2 : ∫ y, (ρ y : ℂ) = 1 := by
      rw [integral_complex_ofReal, hρ1]
      simp
    have h3 : ∫ y, (ρ y : ℂ) * ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ)
        = 𝓕 (fun x => (ρ x : ℂ)) ξ := by
      rw [Real.fourier_eq]
      congr 1
      funext y
      rw [Circle.smul_def, smul_eq_mul, inner_neg_left, mul_comm]
    rw [h1, h2, h3]
  have hnorm : ‖1 - 𝓕 (fun x => (ρ x : ℂ)) ξ‖
      ≤ ∫ y, ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ := by
    rw [hrep]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 y), norm_sub_rev]
  calc ‖1 - 𝓕 (fun x => (ρ x : ℂ)) ξ‖ ^ 2
      ≤ (∫ y, ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := sq_integral_mul_le_integral_mul_sq hρc hρcs hρ0 hρ1 hac

/-- **The mollification estimate.**  For integrable `f` and a continuous compactly supported
probability density `ρ`, if every translation error `‖f(· - y) - f‖²_{H^s}` with `ρ y ≠ 0` is at
most `η`, then `‖f - f ⋆ ρ‖²_{H^s} ≤ η`. -/
theorem sobolevNormSq_sub_convReal_le (s : ℝ) {f ρ : Space d → ℝ} (hf : Integrable f)
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) {η : ℝ}
    (htr : ∀ y, ρ y ≠ 0 →
      sobolevNormSq d s (fun x => f (x + -y) - f x) ≤ ENNReal.ofReal η) :
    sobolevNormSq d s (fun x => f x - convReal f ρ x) ≤ ENNReal.ofReal η := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  have hF1 : Integrable (fun x => (f x : ℂ)) := hf.ofReal
  have hconv : Integrable (convReal f ρ) :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hρi
  have hdiff : ∀ ξ, 𝓕 (fun x => ((f x - convReal f ρ x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (f x : ℂ)) ξ * (1 - 𝓕 (fun x => (ρ x : ℂ)) ξ) := by
    intro ξ
    have hconvC : Integrable (fun x => (convReal f ρ x : ℂ)) := hconv.ofReal
    have h := fourier_sub_lift hF1 hconvC
    have hc := fourier_lift_convReal hf hρi
    have e : (fun x => ((f x - convReal f ρ x : ℝ) : ℂ))
        = (fun x => (f x : ℂ)) - fun x => (convReal f ρ x : ℂ) := by
      funext x
      simp
    rw [e, h, Pi.sub_apply, hc, Pi.mul_apply]
    ring
  have htrans : ∀ y ξ, ‖𝓕 (fun x => ((f (x + -y) - f x : ℝ) : ℂ)) ξ‖
      = ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ := by
    intro y ξ
    have hF' : Integrable (fun x => (f (x + -y) : ℂ)) := hF1.comp_add_right (-y)
    have h := congrFun (fourier_translate_sub_lift (fun x => (f x : ℂ)) (-y) hF1 hF') ξ
    have e : (fun x => ((f (x + -y) - f x : ℝ) : ℂ)) = fun x => (f (x + -y) : ℂ) - (f x : ℂ) := by
      funext x
      simp
    rw [e, h, norm_smul]
  have hw0 : ∀ ξ : Space d, 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := fun ξ =>
    Real.rpow_nonneg (by positivity) s
  have hint : ∀ ξ : Space d,
      Integrable (fun y => ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ ^ 2) := by
    intro ξ
    have hE : Continuous (fun y : Space d => ((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ)) :=
      continuous_fourierChar_coe.comp (continuous_neg.inner continuous_const)
    exact (hρc.mul ((hE.sub continuous_const).norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right hρcs)
  set G : Space d → Space d → ℝ≥0∞ := fun ξ y => ENNReal.ofReal (ρ y) *
    ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 *
      ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ ^ 2) with hG
  have hpt : ∀ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
      ‖𝓕 (fun x => ((f x - convReal f ρ x : ℝ) : ℂ)) ξ‖ ^ 2) ≤ ∫⁻ y, G ξ y := by
    intro ξ
    have hc0 : 0 ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 :=
      mul_nonneg (hw0 ξ) (sq_nonneg _)
    have heq : ∫⁻ y, G ξ y = ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 *
          ∫ y, ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ ^ 2) := by
      have hnn : 0 ≤ᵐ[volume] fun y => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 *
            (ρ y * ‖((𝐞 (inner ℝ (-y) ξ) : Circle) : ℂ) - 1‖ ^ 2) :=
        Eventually.of_forall fun y => mul_nonneg hc0 (mul_nonneg (hρ0 y) (sq_nonneg _))
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hint ξ).const_mul _) hnn]
      refine lintegral_congr fun y => ?_
      simp only [G]
      rw [← ENNReal.ofReal_mul (hρ0 y)]
      congr 1
      ring
    rw [heq, hdiff, norm_mul]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left (norm_one_sub_fourier_sq_le hρc hρcs hρ0 hρ1 ξ) hc0
    calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * (‖𝓕 (fun x => (f x : ℂ)) ξ‖ *
          ‖1 - 𝓕 (fun x => (ρ x : ℂ)) ξ‖) ^ 2
        = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ^ 2 *
          ‖1 - 𝓕 (fun x => (ρ x : ℂ)) ξ‖ ^ 2 := by ring
      _ ≤ _ := h
  have hmeas : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    have hcF : Continuous (𝓕 (fun x => (f x : ℂ))) := continuous_fourier_lift hf
    have hW : Continuous (fun ξ : Space d => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s) :=
      Continuous.rpow_const (by fun_prop) (fun ξ => Or.inl (by positivity))
    have hE : Continuous (fun p : Space d × Space d =>
        ((𝐞 (inner ℝ (-p.2) p.1) : Circle) : ℂ)) :=
      continuous_fourierChar_coe.comp (continuous_snd.neg.inner continuous_fst)
    have hreal : Continuous (fun p : Space d × Space d =>
        (1 + (2 * Real.pi * ‖p.1‖) ^ 2) ^ s * ‖𝓕 (fun x => (f x : ℂ)) p.1‖ ^ 2 *
          ‖((𝐞 (inner ℝ (-p.2) p.1) : Circle) : ℂ) - 1‖ ^ 2) :=
      ((hW.comp continuous_fst).mul ((hcF.comp continuous_fst).norm.pow 2)).mul
        ((hE.sub continuous_const).norm.pow 2)
    exact ((ENNReal.measurable_ofReal.comp (hρc.measurable.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp hreal.measurable)).aemeasurable
  have hy : ∀ y, ∫⁻ ξ, G ξ y ≤ ENNReal.ofReal (ρ y) * ENNReal.ofReal η := by
    intro y
    have e : ∫⁻ ξ, G ξ y
        = ENNReal.ofReal (ρ y) * sobolevNormSq d s (fun x => f (x + -y) - f x) := by
      rw [sobolevNormSq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ξ => ?_
      simp only [G]
      rw [htrans y ξ]
      congr 2
      ring
    rw [e]
    by_cases hy0 : ρ y = 0
    · simp [hy0]
    · exact mul_le_mul_of_nonneg_left (htr y hy0) zero_le
  calc sobolevNormSq d s (fun x => f x - convReal f ρ x)
      = ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          ‖𝓕 (fun x => ((f x - convReal f ρ x : ℝ) : ℂ)) ξ‖ ^ 2) := rfl
    _ ≤ ∫⁻ ξ, ∫⁻ y, G ξ y := lintegral_mono hpt
    _ = ∫⁻ y, ∫⁻ ξ, G ξ y := lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ENNReal.ofReal η := lintegral_mono hy
    _ = ENNReal.ofReal η := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1,
          ENNReal.ofReal_one, one_mul]

/-- The Sobolev norm of a function that is not integrable is zero. -/
theorem sobolevNormSq_eq_zero_of_not_integrable (s : ℝ) {g : Space d → ℝ}
    (hg : ¬ Integrable g) : sobolevNormSq d s g = 0 := by
  have hgc : ¬ Integrable (fun x => (g x : ℂ)) := fun h => hg (by simpa using h.re)
  have h0 : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = 0 := by
    intro ξ
    refine integral_undef fun h => hgc ?_
    exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ ξ).1 h
  unfold sobolevNormSq
  simp [h0]

/-- **Non-integrable compactly supported functions.**  If `f` vanishes outside a compact set and
is not integrable, and `ρ` is continuous and positive on the open ball of radius `r`, then
`f - f ⋆ ρ` is not integrable. -/
theorem not_integrable_sub_convReal {K : Set (Space d)} (hK : IsCompact K)
    {f ρ : Space d → ℝ} (hfK : tsupport f ⊆ K) (hf : ¬ Integrable f) (hρc : Continuous ρ)
    {r : ℝ} (hr : 0 < r) (hρpos : ∀ y, ‖y‖ < r → 0 < ρ y) :
    ¬ Integrable (fun x => f x - convReal f ρ x) := by
  have hloc : ¬ LocallyIntegrable f volume := by
    intro hl
    apply hf
    exact (integrableOn_iff_integrable_of_support_subset
      ((subset_tsupport f).trans hfK)).1 (hl.integrableOn_isCompact hK)
  obtain ⟨p, hp⟩ : ∃ p, ¬ IntegrableAtFilter f (𝓝 p) volume := by
    by_contra h
    exact hloc fun x => Classical.byContradiction fun hx => h ⟨x, hx⟩
  have hzero : ∀ x ∈ Metric.ball p r, convReal f ρ x = 0 := by
    intro x hx
    have hxp : dist x p < r := hx
    have hnot : ¬ Integrable (fun t => f t * ρ (x - t)) := by
      intro hint
      apply hp
      set δ := (r - dist x p) / 2 with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      have hsub : ∀ t ∈ Metric.closedBall p δ, 0 < ρ (x - t) := by
        intro t ht
        apply hρpos
        rw [← dist_eq_norm]
        have h1 : dist t p ≤ δ := ht
        have h2 := dist_triangle x p t
        rw [dist_comm p t] at h2
        linarith
      obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_closedBall p δ).exists_isMinOn
        ⟨p, Metric.mem_closedBall_self hδpos.le⟩
        ((hρc.comp (continuous_const.sub continuous_id)).continuousOn)
      have hc : 0 < ρ (x - t₀) := hsub t₀ ht₀
      refine ⟨Metric.closedBall p δ, Metric.closedBall_mem_nhds p hδpos, ?_⟩
      have hmeas : AEStronglyMeasurable (fun t => f t * ρ (x - t) * (ρ (x - t))⁻¹)
          (volume.restrict (Metric.closedBall p δ)) :=
        (hint.aestronglyMeasurable.mul
          ((hρc.comp (continuous_const.sub continuous_id)).measurable.inv.aestronglyMeasurable)).restrict
      have heq : (fun t => f t * ρ (x - t) * (ρ (x - t))⁻¹)
          =ᵐ[volume.restrict (Metric.closedBall p δ)] f := by
        refine ae_restrict_of_forall_mem Metric.isClosed_closedBall.measurableSet fun t ht => ?_
        exact mul_inv_cancel_right₀ (hsub t ht).ne' (f t)
      refine Integrable.mono' ((hint.norm.const_mul (ρ (x - t₀))⁻¹).restrict)
        (hmeas.congr heq) ?_
      refine ae_restrict_of_forall_mem Metric.isClosed_closedBall.measurableSet fun t ht => ?_
      have hρt := hsub t ht
      have hle : ρ (x - t₀) ≤ ρ (x - t) := hmin ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hρt, inv_mul_eq_div,
        le_div_iff₀ hc]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    unfold convReal
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    exact integral_undef hnot
  intro hint
  apply hp
  refine ⟨Metric.ball p r, Metric.ball_mem_nhds p hr, ?_⟩
  refine hint.integrableOn.congr_fun (fun x hx => ?_) Metric.isOpen_ball.measurableSet
  simp [hzero x hx]

/-- A nonnegative smooth function of total mass one whose support is the open ball of radius
`r` about the origin. -/
theorem exists_nonneg_mollifier {r : ℝ} (hr : 0 < r) :
    ∃ ρ : Space d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ y, 0 ≤ ρ y) ∧
      ∫ y, ρ y = 1 ∧ Function.support ρ = Metric.ball 0 r := by
  let b : ContDiffBump (0 : Space d) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  exact ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, b.nonneg_normed,
    b.integral_normed, b.support_normed_eq⟩

/-- The mollification estimate holds. -/
theorem sobolevMollificationEstimate_holds : SobolevMollificationEstimate := by
  intro d s S hint htrans η hη
  obtain ⟨δ, hδ, hδtr⟩ := htrans η hη
  obtain ⟨ρ, hρsm, hρcs, hρ0, hρ1, hsupp⟩ := exists_nonneg_mollifier (d := d) (half_pos hδ)
  refine ⟨ρ, hρsm, hρcs, fun f hf => ?_⟩
  refine sobolevNormSq_sub_convReal_le s (hint f hf) hρsm.continuous hρcs hρ0 hρ1
    (fun y hy => ?_)
  have hy' : y ∈ Metric.ball (0 : Space d) (δ / 2) := hsupp ▸ hy
  rw [Metric.mem_ball, dist_zero_right] at hy'
  exact hδtr (-y) (by rw [norm_neg]; linarith) f hf

/-- **Mollification approximation.**  A family supported in a fixed compact set and uniformly
translation-continuous in `H^s` is approximated uniformly by convolution with one smooth
compactly supported function. -/
theorem frechetKolmogorovMollify_holds : FrechetKolmogorovMollify := by
  intro d K hK s S hsupp htrans η hη
  obtain ⟨δ, hδ, hδtr⟩ := htrans η hη
  obtain ⟨ρ, hρsm, hρcs, hρ0, hρ1, hρsupp⟩ := exists_nonneg_mollifier (d := d) (half_pos hδ)
  refine ⟨ρ, hρsm, hρcs, fun f hf => ?_⟩
  by_cases hfi : Integrable f
  · refine sobolevNormSq_sub_convReal_le s hfi hρsm.continuous hρcs hρ0 hρ1 (fun y hy => ?_)
    have hy' : y ∈ Metric.ball (0 : Space d) (δ / 2) := hρsupp ▸ hy
    rw [Metric.mem_ball, dist_zero_right] at hy'
    exact hδtr (-y) (by rw [norm_neg]; linarith) f hf
  · have hpos : ∀ y : Space d, ‖y‖ < δ / 2 → 0 < ρ y := by
      intro y hy
      have hy' : y ∈ Function.support ρ := by
        rw [hρsupp, Metric.mem_ball, dist_zero_right]
        exact hy
      exact lt_of_le_of_ne (hρ0 y) (Ne.symm hy')
    rw [sobolevNormSq_eq_zero_of_not_integrable s
      (not_integrable_sub_convReal hK (hsupp f hf) hfi hρsm.continuous (half_pos hδ) hpos)]
    exact zero_le

/-- **The Fréchet–Kolmogorov theorem in `H^s`.**  An integrable family supported in a fixed
compact set, bounded and uniformly translation-continuous in `H^s`, is totally bounded in `H^s`,
with centres in the family. -/
theorem frechetKolmogorovH_holds : FrechetKolmogorovH :=
  frechetKolmogorovH_of_mollify_and_compact frechetKolmogorovMollify_holds
    frechetKolmogorovMollifiedCompact_holds

end LatticeProb.Sobolev
