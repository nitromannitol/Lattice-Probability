import Mathlib
import LatticeProb.Prob.GaussianLogSobolevOU

/-!
# Mehler smoothing: derivative calculus and the Ornstein-Uhlenbeck heat equation (`d = 1`)

For `γ = gaussianReal 0 1` and `a : ℝ`,
`mehlerSmooth a f w = ∫ f (w cos a + z sin a) dγ(z)`.

* Phase A (`mehlerSmooth_iteratedDeriv`, `mehlerSmooth_contDiff`,
  `mehlerSmooth_iteratedDeriv_bound`): for a bounded Borel `f` and `0 < sin a`,
  `(U_a f)^{(r)}(w) = (cot a)^r ∫ f (w cos a + z sin a) He_r(z) dγ(z)`.  The proof is by the
  *shift* form of the kernel route: moving the base point `w` is a translation of the Gaussian
  profile `He_r φ`, so a single dominated-derivative lemma (`mehler_hasDerivAt_shift`) supplies
  the step `r → r + 1` (`mehlerH_hasDerivAt`).
* Phase B (`mehlerSmooth_hasDerivAt_angle`): for `f ∈ C²_b` and `0 < a < π/2`,
  `∂_a U_a f(w) = tan a ((U_a f)''(w) - w (U_a f)'(w))`.
* Phase C (`ouHeatEquation_holds`): the named open input `OUHeatEquation` of
  `GaussianLogSobolevOU.lean`, via `cos a = e^{-t}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

noncomputable section

/-- The Mehler smoothing `U_a f (w) = E f (w cos a + Z sin a)`, `Z ~ N(0,1)`. -/
def mehlerSmooth (a : ℝ) (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ z, f (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)

/-- The standard Gaussian density, in an explicit form. -/
def mehlerPhi (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))

/-- The Hermite profile `He_r(x) φ(x)`. -/
def mehlerProfile (r : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite r) * mehlerPhi x

theorem mehlerPhi_eq : gaussianPDFReal 0 1 = mehlerPhi := by
  funext x
  simp only [gaussianPDFReal, mehlerPhi, NNReal.coe_one, mul_one, sub_zero]
  rw [neg_div]

/-- The integral against `gaussianReal 0 1` as a Lebesgue integral against `mehlerPhi`. -/
theorem mehler_integral_gaussian (g : ℝ → ℝ) :
    ∫ x, g x ∂(gaussianReal 0 1) = ∫ x, mehlerPhi x * g x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num), mehlerPhi_eq]
  rfl

theorem mehlerPhi_pos (x : ℝ) : 0 < mehlerPhi x := by
  unfold mehlerPhi; positivity

theorem mehlerPhi_hasDerivAt (x : ℝ) : HasDerivAt mehlerPhi (-x * mehlerPhi x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).fun_neg
    exact this.congr_deriv (by simp)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  exact h2.congr_deriv (by simp only [mehlerPhi]; ring)

theorem mehlerProfile_hasDerivAt (r : ℕ) (x : ℝ) :
    HasDerivAt (mehlerProfile r) (-mehlerProfile (r + 1) x) x := by
  have h1 := ((Polynomial.hermite r).hasDerivAt_aeval x).mul (mehlerPhi_hasDerivAt x)
  refine h1.congr_deriv ?_
  simp only [mehlerProfile]
  rw [Polynomial.hermite_succ]
  simp only [map_sub, map_mul, Polynomial.aeval_X]
  ring

/-- Polynomial-times-Gaussian bound. -/
theorem mehler_poly_gauss_bound (p : Polynomial ℤ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ,
      |Polynomial.aeval u p| * Real.exp (-(u ^ 2 / 2)) ≤ M * Real.exp (-(1 / 8) * u ^ 2) := by
  have key : ∀ k : ℕ, ∀ u : ℝ, |u| ^ k * Real.exp (-(u ^ 2 / 2))
      ≤ (k.factorial * Real.exp 2) * Real.exp (-(1 / 8) * u ^ 2) := by
    intro k u
    have h1 : |u| ^ k ≤ k.factorial * Real.exp |u| := by
      have := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) k
      have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
      rw [div_le_iff₀ hk] at this
      linarith
    have h2 : Real.exp |u| * Real.exp (-(u ^ 2 / 2))
        ≤ Real.exp 2 * Real.exp (-(1 / 8) * u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : |u| ^ 2 = u ^ 2 := sq_abs u
      nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    calc |u| ^ k * Real.exp (-(u ^ 2 / 2))
        ≤ (k.factorial * Real.exp |u|) * Real.exp (-(u ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = k.factorial * (Real.exp |u| * Real.exp (-(u ^ 2 / 2))) := by ring
      _ ≤ k.factorial * (Real.exp 2 * Real.exp (-(1 / 8) * u ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1),
    |(p.coeff k : ℝ)| * (k.factorial * Real.exp 2), Finset.sum_nonneg (fun k _ => by positivity),
    fun u => ?_⟩
  rw [Polynomial.aeval_eq_sum_range]
  calc |∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • u ^ k| * Real.exp (-(u ^ 2 / 2))
      ≤ (∑ k ∈ Finset.range (p.natDegree + 1), |(p.coeff k : ℝ)| * |u| ^ k)
          * Real.exp (-(u ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [abs_smul, abs_pow]
        simp
    _ = ∑ k ∈ Finset.range (p.natDegree + 1),
          |(p.coeff k : ℝ)| * (|u| ^ k * Real.exp (-(u ^ 2 / 2))) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ ∑ k ∈ Finset.range (p.natDegree + 1),
          |(p.coeff k : ℝ)| * ((k.factorial * Real.exp 2) * Real.exp (-(1 / 8) * u ^ 2)) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (key k u) (abs_nonneg _))
    _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)

/-- Locally uniform dominator for the shifted Hermite profiles. -/
theorem mehler_profile_bound (r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z δ : ℝ, |δ| ≤ 1 →
      |mehlerProfile r (z - δ)| ≤ M * Real.exp (-(1 / 16) * z ^ 2) := by
  obtain ⟨M0, hM0, hb⟩ := mehler_poly_gauss_bound (Polynomial.hermite r)
  refine ⟨(Real.sqrt (2 * Real.pi))⁻¹ * M0 * Real.exp (1 / 8), by positivity, fun z δ hδ => ?_⟩
  have hb1 := hb (z - δ)
  have hexp : Real.exp (-(1 / 8) * (z - δ) ^ 2)
      ≤ Real.exp (1 / 8) * Real.exp (-(1 / 16) * z ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hδ2 : δ ^ 2 ≤ 1 := by
      have := sq_abs δ
      nlinarith [abs_nonneg δ]
    nlinarith [sq_nonneg (z - 2 * δ)]
  have hphi : mehlerProfile r (z - δ) = Polynomial.aeval (z - δ) (Polynomial.hermite r)
      * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((z - δ) ^ 2 / 2))) := rfl
  rw [hphi, abs_mul, abs_of_pos (by positivity : 0 < (Real.sqrt (2 * Real.pi))⁻¹
      * Real.exp (-((z - δ) ^ 2 / 2)))]
  calc |Polynomial.aeval (z - δ) (Polynomial.hermite r)|
        * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((z - δ) ^ 2 / 2)))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (|Polynomial.aeval (z - δ) (Polynomial.hermite r)|
        * Real.exp (-((z - δ) ^ 2 / 2))) := by ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (M0 * Real.exp (-(1 / 8) * (z - δ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (M0 * (Real.exp (1 / 8) * Real.exp (-(1 / 16) * z ^ 2))) := by
        gcongr
    _ = _ := by ring

theorem mehlerProfile_continuous (r : ℕ) : Continuous (mehlerProfile r) :=
  continuous_iff_continuousAt.2 fun x => (mehlerProfile_hasDerivAt r x).continuousAt

theorem mehlerProfile_integrable (r : ℕ) : Integrable (mehlerProfile r) := by
  obtain ⟨M, hM, hb⟩ := mehler_profile_bound r
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 16)).const_mul M)
    (mehlerProfile_continuous r).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  simpa using hb z 0 (by simp)

/-- **The reusable dominated-derivative step** (in the shift variable): for a bounded
measurable `g`, the map `δ ↦ ∫ g(z) He_r(z-δ) φ(z-δ) dz` has derivative
`∫ g(z) He_{r+1}(z) φ(z) dz` at `δ = 0`. -/
theorem mehler_hasDerivAt_shift (r : ℕ) (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) :
    HasDerivAt (fun δ : ℝ => ∫ z, g z * mehlerProfile r (z - δ))
      (∫ z, g z * mehlerProfile (r + 1) z) 0 := by
  obtain ⟨M, hM, hb⟩ := mehler_profile_bound (r + 1)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hmeas : ∀ (k : ℕ) (δ : ℝ), AEStronglyMeasurable (fun z => g z * mehlerProfile k (z - δ))
      volume := fun k δ =>
    (hg.mul ((mehlerProfile_continuous k).comp (continuous_id.sub continuous_const)).measurable
      ).aestronglyMeasurable
  have hbd : Integrable (fun z => C * M * Real.exp (-(1 / 16) * z ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 16)).const_mul (C * M)
  have hF0 : Integrable (fun z => g z * mehlerProfile r (z - 0)) := by
    have : Integrable (fun z => g z * mehlerProfile r z) := by
      obtain ⟨M', hM', hb'⟩ := mehler_profile_bound r
      refine Integrable.mono' ((integrable_exp_neg_mul_sq
        (by norm_num : (0 : ℝ) < 1 / 16)).const_mul (C * M')) (by simpa using hmeas r 0)
        (ae_of_all _ fun z => ?_)
      have h1 := hb' z 0 (by simp)
      simp only [sub_zero] at h1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |g z| * |mehlerProfile r z| ≤ C * (M' * Real.exp (-(1 / 16) * z ^ 2)) :=
            mul_le_mul (hC z) h1 (abs_nonneg _) hC0
        _ = _ := by ring
    simpa using this
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (F := fun δ z => g z * mehlerProfile r (z - δ))
    (F' := fun δ z => g z * mehlerProfile (r + 1) (z - δ)) (x₀ := 0)
    (s := Metric.ball 0 1) (bound := fun z => C * M * Real.exp (-(1 / 16) * z ^ 2))
    (Metric.ball_mem_nhds 0 one_pos) (Filter.Eventually.of_forall fun δ => hmeas r δ) hF0
    (hmeas (r + 1) 0) ?_ hbd ?_
  · simpa using this.2
  · refine ae_of_all _ fun z δ hδ => ?_
    have hδ1 : |δ| ≤ 1 := by
      have := mem_ball_zero_iff.1 hδ
      rw [Real.norm_eq_abs] at this
      exact this.le
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |g z| * |mehlerProfile (r + 1) (z - δ)| ≤ C * (M * Real.exp (-(1 / 16) * z ^ 2)) :=
          mul_le_mul (hC z) (hb z δ hδ1) (abs_nonneg _) hC0
      _ = _ := by ring
  · refine ae_of_all _ fun z δ _ => ?_
    have h1 := (mehlerProfile_hasDerivAt r (z - δ)).comp δ ((hasDerivAt_id δ).const_sub z)
    have h2 := h1.const_mul (g z)
    refine h2.congr_deriv ?_
    simp

/-- The Lebesgue form of the `r`-th Hermite-weighted Mehler integral
`∫ f(w cos a + z sin a) He_r(z) φ(z) dz`. -/
def mehlerH (a : ℝ) (f : ℝ → ℝ) (r : ℕ) (w : ℝ) : ℝ :=
  ∫ z, f (w * Real.cos a + z * Real.sin a) * mehlerProfile r z

/-- Moving the base point `w` to `w'` is a translation of the Gaussian profile. -/
theorem mehlerH_shift (a : ℝ) (f : ℝ → ℝ) (r : ℕ) (w w' : ℝ) (hs : 0 < Real.sin a) :
    mehlerH a f r w' = ∫ z, f (w * Real.cos a + z * Real.sin a)
      * mehlerProfile r (z - (w' - w) * Real.cos a / Real.sin a) := by
  set δ : ℝ := (w' - w) * Real.cos a / Real.sin a with hδ
  have hδs : δ * Real.sin a = (w' - w) * Real.cos a := by
    rw [hδ]; field_simp
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun z => f (w * Real.cos a + z * Real.sin a) * mehlerProfile r (z - δ)) δ]
  unfold mehlerH
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [add_sub_cancel_right]
  congr 2
  linear_combination (-1 : ℝ) * hδs

/-- **The derivative step `r → r + 1`.**  For a bounded measurable `f` and `0 < sin a`,
`d/dw ∫ f(w cos a + z sin a) He_r φ dz = cot a · ∫ f(w cos a + z sin a) He_{r+1} φ dz`. -/
theorem mehlerH_hasDerivAt (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w : ℝ) :
    HasDerivAt (mehlerH a f r) (Real.cos a / Real.sin a * mehlerH a f (r + 1) w) w := by
  have hg : Measurable (fun z => f (w * Real.cos a + z * Real.sin a)) :=
    hf.comp (by fun_prop)
  have h1 := mehler_hasDerivAt_shift r (fun z => f (w * Real.cos a + z * Real.sin a)) hg C
    (fun z => hC _)
  have h2 : HasDerivAt (fun w' : ℝ => (w' - w) * Real.cos a / Real.sin a)
      (Real.cos a / Real.sin a) w := by
    have := (((hasDerivAt_id w).sub_const w).mul_const (Real.cos a)).div_const (Real.sin a)
    exact this.congr_deriv (by simp)
  have h3 := HasDerivAt.scomp w (by simpa using h1) h2
  have h4 : (fun δ : ℝ => ∫ z, f (w * Real.cos a + z * Real.sin a) * mehlerProfile r (z - δ))
      ∘ (fun w' : ℝ => (w' - w) * Real.cos a / Real.sin a) = mehlerH a f r := by
    funext w'
    simp only [Function.comp]
    exact (mehlerH_shift a f r w w' hs).symm
  rw [h4] at h3
  exact h3.congr_deriv (by simp [mehlerH, smul_eq_mul])

theorem mehler_integrable_gaussian_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => mehlerPhi x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, mehlerPhi_eq, smul_eq_mul]

theorem mehlerH_eq_integral (a : ℝ) (f : ℝ → ℝ) (r : ℕ) (w : ℝ) :
    mehlerH a f r w = ∫ z, f (w * Real.cos a + z * Real.sin a)
      * Polynomial.aeval z (Polynomial.hermite r) ∂(gaussianReal 0 1) := by
  rw [mehler_integral_gaussian]
  unfold mehlerH
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [mehlerProfile]
  ring

theorem mehlerH_zero (a : ℝ) (f : ℝ → ℝ) (w : ℝ) : mehlerH a f 0 w = mehlerSmooth a f w := by
  rw [mehlerH_eq_integral]
  unfold mehlerSmooth
  simp

/-- The iterated derivatives of the Mehler smoothing in terms of the Lebesgue-form integrals. -/
theorem mehlerSmooth_iteratedDeriv_eq_mehlerH (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) :
    iteratedDeriv r (mehlerSmooth a f)
      = fun w => (Real.cos a / Real.sin a) ^ r * mehlerH a f r w := by
  induction r with
  | zero =>
    funext w
    simp [mehlerH_zero]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    exact (((mehlerH_hasDerivAt a f hf C hC hs r w).const_mul
      ((Real.cos a / Real.sin a) ^ r)).deriv).trans (by ring)

/-- **Phase A, iterated derivatives.**  For a bounded Borel `f` and `0 < sin a`,
`(U_a f)^{(r)}(w) = (cot a)^r ∫ f(w cos a + z sin a) He_r(z) dγ(z)` with `He_r` the
probabilists' Hermite polynomial `Polynomial.hermite r` evaluated through `Polynomial.aeval`
(note `Polynomial.hermite r : Polynomial ℤ`). -/
theorem mehlerSmooth_iteratedDeriv (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) :
    iteratedDeriv r (mehlerSmooth a f) = fun w => (Real.cos a / Real.sin a) ^ r *
      ∫ z, f (w * Real.cos a + z * Real.sin a) * Polynomial.aeval z (Polynomial.hermite r)
        ∂(gaussianReal 0 1) := by
  obtain ⟨C, hC⟩ := hb
  rw [mehlerSmooth_iteratedDeriv_eq_mehlerH a f hf C hC hs r]
  funext w
  rw [mehlerH_eq_integral]

/-- Sanity check of the Hermite convention: `He_2 = X^2 - 1`. -/
theorem mehler_hermite_two : Polynomial.hermite 2 = Polynomial.X ^ 2 - 1 := by
  rw [Polynomial.hermite_succ, Polynomial.hermite_one]
  simp [pow_two]

theorem mehlerSmooth_differentiable_iteratedDeriv (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m (mehlerSmooth a f)) := by
  obtain ⟨C, hC⟩ := hb
  rw [mehlerSmooth_iteratedDeriv_eq_mehlerH a f hf C hC hs m]
  intro w
  exact (((mehlerH_hasDerivAt a f hf C hC hs m w).const_mul
    ((Real.cos a / Real.sin a) ^ m)).differentiableAt)

/-- **Phase A, smoothness.**  The Mehler smoothing of a bounded Borel function is `C^∞`
(`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`; note that in current Mathlib the bare `⊤ : WithTop ℕ∞`
means analytic, which we do not claim). -/
theorem mehlerSmooth_contDiff (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mehlerSmooth a f) :=
  contDiff_of_differentiable_iteratedDeriv fun m _ =>
    mehlerSmooth_differentiable_iteratedDeriv a f hf hb hs m

theorem mehler_integrable_aeval_hermite_gaussian (r : ℕ) :
    Integrable (fun z : ℝ => Polynomial.aeval z (Polynomial.hermite r)) (gaussianReal 0 1) := by
  rw [mehler_integrable_gaussian_iff]
  refine (mehlerProfile_integrable r).congr (ae_of_all _ fun z => ?_)
  simp only [mehlerProfile]
  ring

/-- **Phase A, bounds.**  `‖U_a f^{(r)}‖ ≤ C |cot a|^r ∫ |He_r| dγ`. -/
theorem mehlerSmooth_iteratedDeriv_bound (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w : ℝ) :
    ‖iteratedDeriv r (mehlerSmooth a f) w‖ ≤
      C * |Real.cos a / Real.sin a| ^ r *
        ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  rw [mehlerSmooth_iteratedDeriv a f hf ⟨C, hC⟩ hs r, norm_mul, norm_pow, Real.norm_eq_abs]
  have hint : Integrable (fun z => |Polynomial.aeval z (Polynomial.hermite r)|)
      (gaussianReal 0 1) := (mehler_integrable_aeval_hermite_gaussian r).abs
  have hle : ‖∫ z, f (w * Real.cos a + z * Real.sin a)
      * Polynomial.aeval z (Polynomial.hermite r) ∂(gaussianReal 0 1)‖ ≤
      ∫ z, C * |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
    refine norm_integral_le_of_norm_le (hint.const_mul C) (ae_of_all _ fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hC _)) (abs_nonneg _)
  rw [integral_const_mul] at hle
  calc |Real.cos a / Real.sin a| ^ r * ‖∫ z, f (w * Real.cos a + z * Real.sin a)
      * Polynomial.aeval z (Polynomial.hermite r) ∂(gaussianReal 0 1)‖
      ≤ |Real.cos a / Real.sin a| ^ r *
        (C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1)) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-! ### Phase B: the derivative in the angle -/

theorem mehlerProfile_zero (x : ℝ) : mehlerProfile 0 x = mehlerPhi x := by
  simp [mehlerProfile]

theorem mehlerProfile_one (x : ℝ) : mehlerProfile 1 x = x * mehlerPhi x := by
  simp [mehlerProfile]

/-- **Gaussian integration by parts** `E[Z h(Z)] = E[h'(Z)]` for `C^1` bounded `h` with bounded
derivative. -/
theorem mehler_gaussian_ibp (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) (C0 C1 : ℝ)
    (h0 : ∀ x, |h x| ≤ C0) (h1 : ∀ x, |deriv h x| ≤ C1) :
    ∫ z, z * h z ∂(gaussianReal 0 1) = ∫ z, deriv h z ∂(gaussianReal 0 1) := by
  have hd : ∀ x, HasDerivAt h (deriv h x) x := fun x =>
    (hh.differentiable one_ne_zero x).hasDerivAt
  have hcd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  have hv : ∀ x, HasDerivAt (fun x => -mehlerProfile 0 x) (mehlerProfile 1 x) x := fun x => by
    have := (mehlerProfile_hasDerivAt 0 x).fun_neg
    simpa using this
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := h) (v := fun x => -mehlerProfile 0 x) (u' := deriv h) (v' := mehlerProfile 1)
    (fun x _ => hd x) (fun x _ => hv x)
    (by
      have := (mehlerProfile_integrable 1).bdd_mul (f := h) hh.continuous.aestronglyMeasurable
        (c := C0) (ae_of_all _ fun x => by simpa using h0 x)
      exact this)
    (by
      have := ((mehlerProfile_integrable 0).neg).bdd_mul (f := deriv h) hcd.aestronglyMeasurable
        (c := C1) (ae_of_all _ fun x => by simpa using h1 x)
      exact this)
    (by
      have := ((mehlerProfile_integrable 0).neg).bdd_mul (f := h) hh.continuous.aestronglyMeasurable
        (c := C0) (ae_of_all _ fun x => by simpa using h0 x)
      exact this)
  rw [mehler_integral_gaussian, mehler_integral_gaussian]
  have e1 : ∫ z, mehlerPhi z * (z * h z) = ∫ x, h x * mehlerProfile 1 x := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [mehlerProfile_one]; ring
  have e2 : ∫ z, mehlerPhi z * deriv h z = -∫ x, deriv h x * -mehlerProfile 0 x := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [mehlerProfile_zero]; ring
  rw [e1, e2]
  exact key

/-- Differentiation in the base point `w` of the Mehler integral of a `C^1` function with
bounded derivative. -/
theorem mehler_hasDerivAt_w_smooth (a : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (C0 C1 : ℝ)
    (h0 : ∀ x, |g x| ≤ C0) (h1 : ∀ x, |deriv g x| ≤ C1) (w : ℝ) :
    HasDerivAt (fun w' => ∫ z, g (w' * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1))
      (Real.cos a * ∫ z, deriv g (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)) w := by
  have hcg : Continuous g := hg.continuous
  have hcd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := gaussianReal 0 1)
    (F := fun w' z => g (w' * Real.cos a + z * Real.sin a))
    (F' := fun w' z => deriv g (w' * Real.cos a + z * Real.sin a) * Real.cos a) (x₀ := w)
    (s := Set.univ) (bound := fun _ => C1 * |Real.cos a|) Filter.univ_mem
    (Filter.Eventually.of_forall fun w' =>
      (hcg.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hcg.comp (by fun_prop)).aestronglyMeasurable C0
      (ae_of_all _ fun z => by simpa using h0 _))
    ((hcd.comp (by fun_prop)).mul continuous_const).aestronglyMeasurable
    (ae_of_all _ fun z w' _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (h1 _) (abs_nonneg _))
    (integrable_const _)
    (ae_of_all _ fun z w' _ => by
      have h2 : HasDerivAt (fun w' : ℝ => w' * Real.cos a + z * Real.sin a) (Real.cos a) w' := by
        simpa using ((hasDerivAt_id w').mul_const (Real.cos a)).add_const (z * Real.sin a)
      exact (((hg.differentiable one_ne_zero) _).hasDerivAt).comp w' h2)
  have h3 := this.2
  rw [integral_mul_const] at h3
  rw [mul_comm]
  exact h3

/-- Differentiation in the angle `a` of the Mehler integral of a `C^1` function with bounded
derivative. -/
theorem mehler_hasDerivAt_angle_smooth (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (C0 C1 : ℝ)
    (h0 : ∀ x, |g x| ≤ C0) (h1 : ∀ x, |deriv g x| ≤ C1) (a w : ℝ) :
    HasDerivAt (fun a' => ∫ z, g (w * Real.cos a' + z * Real.sin a') ∂(gaussianReal 0 1))
      (∫ z, deriv g (w * Real.cos a + z * Real.sin a)
        * (-(w * Real.sin a) + z * Real.cos a) ∂(gaussianReal 0 1)) a := by
  have hcg : Continuous g := hg.continuous
  have hcd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hid : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp))).abs
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := gaussianReal 0 1)
    (F := fun a' z => g (w * Real.cos a' + z * Real.sin a'))
    (F' := fun a' z => deriv g (w * Real.cos a' + z * Real.sin a')
      * (-(w * Real.sin a') + z * Real.cos a')) (x₀ := a)
    (s := Set.univ) (bound := fun z => C1 * (|w| + |z|)) Filter.univ_mem
    (Filter.Eventually.of_forall fun a' =>
      (hcg.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hcg.comp (by fun_prop)).aestronglyMeasurable C0
      (ae_of_all _ fun z => by simpa using h0 _))
    ((hcd.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z a' _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul (h1 _) ?_ (abs_nonneg _) ((abs_nonneg _).trans (h1 0))
      calc |-(w * Real.sin a') + z * Real.cos a'|
          ≤ |-(w * Real.sin a')| + |z * Real.cos a'| := abs_add_le _ _
        _ = |w| * |Real.sin a'| + |z| * |Real.cos a'| := by
          rw [abs_neg, abs_mul, abs_mul]
        _ ≤ |w| * 1 + |z| * 1 := by
          gcongr
          · exact Real.abs_sin_le_one a'
          · exact Real.abs_cos_le_one a'
        _ = |w| + |z| := by ring)
    (((integrable_const |w|).add hid).const_mul C1)
    (ae_of_all _ fun z a' _ => by
      have h2 : HasDerivAt (fun a'' : ℝ => w * Real.cos a'' + z * Real.sin a'')
          (-(w * Real.sin a') + z * Real.cos a') a' := by
        have h3 := ((Real.hasDerivAt_cos a').const_mul w).add ((Real.hasDerivAt_sin a').const_mul z)
        exact h3.congr_deriv (by ring)
      exact (((hg.differentiable one_ne_zero) _).hasDerivAt).comp a' h2)
  exact this.2

/-- First and second `w`-derivatives of the Mehler smoothing of a `C^2_b` function. -/
theorem mehlerSmooth_deriv_formulas (a : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (C0 C1 C2 : ℝ)
    (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, |deriv f x| ≤ C1) (h2 : ∀ x, |deriv (deriv f) x| ≤ C2)
    (w : ℝ) :
    deriv (mehlerSmooth a f) w = Real.cos a *
        ∫ z, deriv f (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1) ∧
      iteratedDeriv 2 (mehlerSmooth a f) w = Real.cos a * (Real.cos a *
        ∫ z, deriv (deriv f) (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hU : deriv (mehlerSmooth a f) = fun w => Real.cos a *
      ∫ z, deriv f (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1) := by
    funext w
    exact (mehler_hasDerivAt_w_smooth a f hf1 C0 C1 h0 h1 w).deriv
  refine ⟨by rw [hU], ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, hU]
  exact ((mehler_hasDerivAt_w_smooth a (deriv f) hf' C1 C2 h1 h2 w).const_mul (Real.cos a)).deriv

/-- The `a`-derivative of the Mehler smoothing, in terms of the `w`-derivatives of `f`:
`∫ f'(w cos a + z sin a)(-w sin a + z cos a) dγ = -w sin a ∫ f' + cos a sin a ∫ f''`. -/
theorem mehler_angle_integral_eq (a w : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (C1 C2 : ℝ)
    (h1 : ∀ x, |deriv f x| ≤ C1) (h2 : ∀ x, |deriv (deriv f) x| ≤ C2) :
    ∫ z, deriv f (w * Real.cos a + z * Real.sin a) * (-(w * Real.sin a) + z * Real.cos a)
        ∂(gaussianReal 0 1) =
      -(w * Real.sin a) * ∫ z, deriv f (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)
      + Real.cos a * (Real.sin a *
        ∫ z, deriv (deriv f) (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)) := by
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  set h : ℝ → ℝ := fun z => deriv f (w * Real.cos a + z * Real.sin a) with hh
  have hlin : ContDiff ℝ 1 (fun z : ℝ => w * Real.cos a + z * Real.sin a) := by fun_prop
  have hhd : ContDiff ℝ 1 h := hf'.comp hlin
  have hderiv : ∀ z, deriv h z = deriv (deriv f) (w * Real.cos a + z * Real.sin a)
      * Real.sin a := fun z => by
    have h3 : HasDerivAt (fun z : ℝ => w * Real.cos a + z * Real.sin a) (Real.sin a) z := by
      simpa using ((hasDerivAt_id z).mul_const (Real.sin a)).const_add (w * Real.cos a)
    have h4 := ((hf'.differentiable one_ne_zero) _).hasDerivAt.comp z h3
    exact h4.deriv
  have hb2 : ∀ x, |deriv h x| ≤ C2 := fun x => by
    rw [hderiv, abs_mul]
    calc |deriv (deriv f) (w * Real.cos a + x * Real.sin a)| * |Real.sin a|
        ≤ |deriv (deriv f) (w * Real.cos a + x * Real.sin a)| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one a) (abs_nonneg _)
      _ ≤ C2 := by rw [mul_one]; exact h2 _
  have hibp := mehler_gaussian_ibp h hhd C1 C2 (fun x => h1 _) hb2
  have hint1 : Integrable h (gaussianReal 0 1) :=
    Integrable.of_bound hhd.continuous.aestronglyMeasurable C1
      (ae_of_all _ fun z => by simpa using h1 _)
  have hid : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by simp))
  have hint2 : Integrable (fun z => z * h z) (gaussianReal 0 1) := by
    have := hid.bdd_mul (f := h) hhd.continuous.aestronglyMeasurable (c := C1)
      (ae_of_all _ fun z => by simpa using h1 _)
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only; ring
  have e1 : ∀ z, h z * (-(w * Real.sin a) + z * Real.cos a)
      = (-(w * Real.sin a)) * h z + Real.cos a * (z * h z) := fun z => by ring
  have e2 : (∫ z, deriv f (w * Real.cos a + z * Real.sin a)
        * (-(w * Real.sin a) + z * Real.cos a) ∂(gaussianReal 0 1))
      = ∫ z, ((-(w * Real.sin a)) * h z + Real.cos a * (z * h z)) ∂(gaussianReal 0 1) :=
    integral_congr_ae (ae_of_all _ fun z => e1 z)
  rw [e2, integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
    integral_const_mul, hibp]
  have e3 : (∫ z, deriv h z ∂(gaussianReal 0 1)) = (∫ z, deriv (deriv f)
      (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1)) * Real.sin a := by
    rw [← integral_mul_const]
    exact integral_congr_ae (ae_of_all _ fun z => hderiv z)
  rw [e3]
  ring

/-- **Phase B.**  For `f ∈ C²_b` and `cos a ≠ 0`,
`∂_a U_a f(w) = tan a (U_a f'' - w U_a f')`, where the primes are `w`-derivatives of `U_a f`. -/
theorem mehlerSmooth_hasDerivAt_angle_of_cos_ne_zero (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, |deriv f x| ≤ C)
    (h2 : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C) (a w : ℝ) (hc : Real.cos a ≠ 0) :
    HasDerivAt (fun a' => mehlerSmooth a' f w)
      (Real.tan a * (iteratedDeriv 2 (mehlerSmooth a f) w - w * deriv (mehlerSmooth a f) w)) a := by
  obtain ⟨C0, h0⟩ := h0
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hA := mehler_hasDerivAt_angle_smooth f hf1 C0 C1 h0 h1 a w
  rw [mehler_angle_integral_eq a w f hf C1 C2 h1 h2] at hA
  obtain ⟨hd1, hd2⟩ := mehlerSmooth_deriv_formulas a f hf C0 C1 C2 h0 h1 h2 w
  rw [hd1, hd2, Real.tan_eq_sin_div_cos]
  refine hA.congr_deriv ?_
  field_simp
  ring

/-- **Phase B**, in the range `0 < a < π/2` of the brief:
`∂_a U_a f(w) = tan a (U_a f)''(w) - tan a · w (U_a f)'(w)` for `f ∈ C²_b`.  The sign and the
normalisation `tan a (D² - w D)` stated in the brief are correct (checked by the computation
above: both sides equal `-w sin a E f' + sin a cos a E f''`). -/
theorem mehlerSmooth_hasDerivAt_angle (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, |deriv f x| ≤ C)
    (h2 : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C) (a w : ℝ) (ha0 : 0 < a) (ha1 : a < Real.pi / 2) :
    HasDerivAt (fun a' => mehlerSmooth a' f w)
      (Real.tan a * (iteratedDeriv 2 (mehlerSmooth a f) w - w * deriv (mehlerSmooth a f) w)) a :=
  mehlerSmooth_hasDerivAt_angle_of_cos_ne_zero f hf h0 h1 h2 a w
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩).ne'

/-- **The `C²_b` form of the third derivative** (Raic (2.7) in dimension one):
for `f ∈ C²_b` and `0 < sin a`,
`(U_a f)^{(3)}(w) = (cos a)^3 / sin a · ∫ z · f''(w cos a + z sin a) dγ(z)`. -/
theorem mehlerSmooth_iteratedDeriv_three_C2b (a : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, |deriv f x| ≤ C)
    (h2 : ∃ C, ∀ x, |deriv (deriv f) x| ≤ C) (hs : 0 < Real.sin a) (w : ℝ) :
    iteratedDeriv 3 (mehlerSmooth a f) w = Real.cos a ^ 3 / Real.sin a *
      ∫ z, z * deriv (deriv f) (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1) := by
  obtain ⟨C0, h0⟩ := h0
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  have hf'' : Continuous (deriv (deriv f)) := (hf.deriv').continuous_deriv le_rfl
  have hII : iteratedDeriv 2 (mehlerSmooth a f)
      = fun w => Real.cos a * (Real.cos a * mehlerH a (deriv (deriv f)) 0 w) := by
    funext w
    rw [(mehlerSmooth_deriv_formulas a f hf C0 C1 C2 h0 h1 h2 w).2, mehlerH_zero]
    rfl
  rw [iteratedDeriv_succ, hII]
  have hd := ((mehlerH_hasDerivAt a (deriv (deriv f)) hf''.measurable C2 h2 hs 0 w).const_mul
    (Real.cos a)).const_mul (Real.cos a)
  rw [hd.deriv, mehlerH_eq_integral]
  simp only [zero_add, Polynomial.hermite_one, Polynomial.aeval_X]
  have : ∫ z, deriv (deriv f) (w * Real.cos a + z * Real.sin a) * z ∂(gaussianReal 0 1)
      = ∫ z, z * deriv (deriv f) (w * Real.cos a + z * Real.sin a) ∂(gaussianReal 0 1) :=
    integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [this]
  field_simp

/-! ### Phase C: the Ornstein-Uhlenbeck heat equation -/

/-- The Ornstein-Uhlenbeck semigroup is the Mehler smoothing at the angle `arccos (e^{-t})`. -/
theorem mehler_ouSemigroup_eq (t : ℝ) (ht : 0 ≤ t) (f : ℝ → ℝ) :
    ouSemigroup t f = mehlerSmooth (Real.arccos (Real.exp (-t))) f := by
  have hle : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hge : -1 ≤ Real.exp (-t) := by linarith [Real.exp_pos (-t)]
  have h2 : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  funext x
  unfold ouSemigroup mehlerSmooth
  rw [Real.cos_arccos hge hle, Real.sin_arccos, h2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show f _ = f _
  congr 1
  ring

/-- The angle `arccos (e^{-t})` has derivative `cot` of itself in `t`. -/
theorem mehler_hasDerivAt_arccos_exp_neg (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => Real.arccos (Real.exp (-s)))
      (Real.cos (Real.arccos (Real.exp (-t))) / Real.sin (Real.arccos (Real.exp (-t)))) t := by
  have hlt : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hpos := Real.exp_pos (-t)
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    exact (((hasDerivAt_id t).fun_neg).exp).congr_deriv (by simp)
  have h2 := (Real.hasDerivAt_arccos (x := Real.exp (-t)) (by linarith) hlt.ne).comp t h1
  refine h2.congr_deriv ?_
  rw [Real.cos_arccos (by linarith) hlt.le, Real.sin_arccos]
  have hs : 0 < Real.sqrt (1 - Real.exp (-t) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  field_simp

/-- **Phase C.**  The named open input `OUHeatEquation` of `GaussianLogSobolevOU.lean` holds. -/
theorem ouHeatEquation_holds : OUHeatEquation := by
  intro f hf hcs t ht x
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  obtain ⟨C0, h0⟩ := hcs.exists_bound_of_continuous hf.continuous
  obtain ⟨C1, h1⟩ := hcs.deriv.exists_bound_of_continuous (hf.continuous_deriv (by norm_num))
  obtain ⟨C2, h2⟩ := hcs.deriv.deriv.exists_bound_of_continuous (hf'.continuous_deriv le_rfl)
  set a : ℝ := Real.arccos (Real.exp (-t)) with ha
  have hlt : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hpos := Real.exp_pos (-t)
  have hcos : Real.cos a = Real.exp (-t) := Real.cos_arccos (by linarith) hlt.le
  have hsin : 0 < Real.sin a := by
    rw [ha, Real.sin_arccos]; exact Real.sqrt_pos.2 (by nlinarith)
  have hc : Real.cos a ≠ 0 := by rw [hcos]; exact hpos.ne'
  have hD := mehlerSmooth_hasDerivAt_angle_of_cos_ne_zero f hf ⟨C0, fun x => by simpa using h0 x⟩
    ⟨C1, fun x => by simpa using h1 x⟩ ⟨C2, fun x => by simpa using h2 x⟩ a x hc
  have hθ : HasDerivAt (fun s => Real.arccos (Real.exp (-s))) (Real.cos a / Real.sin a) t :=
    mehler_hasDerivAt_arccos_exp_neg t ht
  have hcomp := hD.comp t hθ
  have heq : (fun s => ouSemigroup s f x) =ᶠ[nhds t]
      ((fun a' => mehlerSmooth a' f x) ∘ fun s => Real.arccos (Real.exp (-s))) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [Function.comp]
    rw [mehler_ouSemigroup_eq s (le_of_lt hs) f]
  have hU : ouSemigroup t f = mehlerSmooth a f := mehler_ouSemigroup_eq t ht.le f
  refine (hcomp.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold ouGenerator
  rw [hU, ← iteratedDeriv_one, ← iteratedDeriv_succ, Real.tan_eq_sin_div_cos]
  field_simp

end

end LatticeProb
