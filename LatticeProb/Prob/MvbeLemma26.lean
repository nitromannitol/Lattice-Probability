import Mathlib
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.MvbeKeyEstimate
import LatticeProb.Prob.MvbeGaussConv

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder RealInnerProductSpace


/-!
# Raic's Lemma 2.6: the Gaussian average of the derivatives of the Mehler smoothing

Packet P14 of the staged formalisation of Raic, "A multivariate Berry-Esseen theorem with explicit
constants" (arXiv:1802.06475, Thm 1.3).

**Main result** `mvbe_lemma_2_6`.  For `f : ℝ^d → ℝ` bounded measurable with `|f - mid| ≤ M`,
`0 < α ≤ π/2`, `r ∈ {1,2,3}`, `μ u : ℝ^d`, and `S` with `σ • 1 ≤ CFC.sqrt S` (`0 < σ ≤ 1`),
`|∫ iteratedFDeriv ℝ r (mehlerN α f) w (u, …, u) dN(μ, S)(w)| ≤ c_r M cos^r α ‖u‖^r / σ^r`.
The case `α = π/2` is not special: there `cos α = 0`, `u' = 0` below, and the bound is `0`.
(The hypothesis `σ ≤ 1` is the paper's standing assumption "the largest eigenvalue of `Σ` is at
most one"; without it the statement is false, e.g. `d = 1`, `r = 1`, `f = sign`, `S = σ²`,
`σ > 1`; `mvbe_lemma_2_6_min` gives the sharp form for arbitrary `σ > 0` with `min σ 1`.)

**Route** (differs from the paper's explicit `Q_α = (Σ cos² α + sin² α)^{1/2}`, which would
require the inverse square root and the density of `N(0, Q_α²)`).  Write
`N(μ, S) = γ.map (μ + A ·)`, `A = toEuclideanCLM (CFC.sqrt S)`, `c = cos α`, `s = sin α`.

1. (`mvbe_iteratedDeriv_integral`, `mvbe_iteratedDeriv_integral_mehlerN`) differentiation under
   the integral sign to every order, with bounds uniform in the parameter, for a family of Mehler
   smoothings along a line.  With the diagonal bridge `mehlerN_iteratedDeriv_line_eq` this gives
   `∫ D^r(U_α f)(μ + A x)[u^r] dγ(x) = (d/dt)^r|_0 F(t)`, `F(t) = ∫ U_α f(μ + A x + t u) dγ(x)`
   (this is `∇^r F(μ)[u^r]` of the paper, only along the line `t ↦ μ + t u`).
2. (`mvbe_conv_decomp`, `mvbe_integral_decomp`) the Gaussian decomposition
   `c A x + s z ~ N(0, (cA)² + s²) = σ z' + R`, `R ~ ρ := N(0, (cA)² + s² - σ²)`, `z'` independent
   of `R`; the covariance of `ρ` is positive semidefinite exactly when `σ ≤ 1` and
   `σ ≤ A` (`mvbe_psd_aux`).  Hence `F(t) = ∫ ∫ f(c(μ + t u) + R + σ z) dγ(z) dρ(R)`.
3. The inner integral is `U_{π/4}` of `y ↦ f(c μ + R + √2 σ y)` at the point `t u'`,
   `u' = (c/σ) u` (here `cot (π/4) = 1`), so by the line formula `mehlerN_iteratedDeriv_line`
   its `r`-th derivative at `0` is `∫ f(c μ + R + σ z) mehlerNHerm r z u' dγ(z)`, which Lemma 2.5
   (`mvbe_gaussian_hermite_integral_le_scaled`) bounds by `c_r M ‖u'‖^r`, `‖u'‖ = c ‖u‖/σ`.
   A second differentiation under the integral sign (over `ρ`) finishes the proof.
-/

namespace LatticeProb

/-! ### Differentiation under the integral sign, to every order -/

/-- **Iterated differentiation under the integral sign.** -/
theorem mvbe_iteratedDeriv_integral {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] (φ : X → ℝ → ℝ) (hφ : ∀ (k : ℕ) x, ContDiff ℝ k (φ x))
    (hb : ∀ k, ∃ C, ∀ x t, |iteratedDeriv k (φ x) t| ≤ C)
    (hm : ∀ k t, AEStronglyMeasurable (fun x => iteratedDeriv k (φ x) t) P) (k : ℕ) :
    iteratedDeriv k (fun t => ∫ x, φ x t ∂P) = fun t => ∫ x, iteratedDeriv k (φ x) t ∂P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    obtain ⟨C, hC⟩ := hb (k + 1)
    obtain ⟨C0, hC0⟩ := hb k
    have hd : ∀ x s, HasDerivAt (iteratedDeriv k (φ x)) (iteratedDeriv (k + 1) (φ x) s) s := by
      intro x s
      have h1 := ((hφ (k + 1) x).differentiable_iteratedDeriv' k) s
      rw [iteratedDeriv_succ]
      exact h1.hasDerivAt
    have hint : Integrable (fun x => iteratedDeriv k (φ x) t) P :=
      Integrable.of_bound (hm k t) C0 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hC0 x t)
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (x₀ := t)
      (s := Set.univ) Filter.univ_mem
      (F := fun s x => iteratedDeriv k (φ x) s) (F' := fun s x => iteratedDeriv (k + 1) (φ x) s)
      (bound := fun _ => C)
      (Filter.Eventually.of_forall fun s => hm k s) hint (hm (k + 1) t)
      (ae_of_all _ fun x s _ => by rw [Real.norm_eq_abs]; exact hC x s)
      (integrable_const C) (ae_of_all _ fun x s _ => hd x s)
    exact this.2.deriv


section mehlerFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mvbe_continuous_mehlerNHerm (k : ℕ) (u : E) :
    Continuous (fun z : E => mehlerNHerm k z u) := by
  unfold mehlerNHerm
  exact continuous_const.mul
    ((Polynomial.continuous_aeval (A := ℝ) (Polynomial.hermite k)).comp
      ((continuous_id.inner continuous_const).div_const _))

/-- **Iterated differentiation under the integral sign for a family of Mehler smoothings.** -/
theorem mvbe_iteratedDeriv_integral_mehlerN {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsFiniteMeasure P] {a : ℝ} (hs : 0 < Real.sin a) {g : X → E → ℝ}
    (hg : Measurable (Function.uncurry g)) {C : ℝ} (hC : ∀ x y, |g x y| ≤ C)
    {w : X → E} (hw : Measurable w) (u : E) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => ∫ x, mehlerN a (g x) (w x + t • u) ∂P) 0 =
      ∫ x, iteratedDeriv k (fun t : ℝ => mehlerN a (g x) (w x + t • u)) 0 ∂P := by
  have hgx : ∀ x, Measurable (g x) := fun x => hg.of_uncurry_left
  refine congrFun (mvbe_iteratedDeriv_integral P
    (fun x t => mehlerN a (g x) (w x + t • u)) ?_ ?_ ?_ k) 0
  · intro k x
    exact (mehlerN_contDiff_nat k a (g x) (hgx x) ⟨C, hC x⟩ hs).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const))
  · intro k
    refine ⟨C * |Real.cos a / Real.sin a| ^ k * ‖u‖ ^ k *
        ∫ z, |Polynomial.aeval z (Polynomial.hermite k)| ∂(gaussianReal 0 1), ?_⟩
    intro x t
    exact mehlerN_iteratedDeriv_line_bound_at a (hgx x) (hC x) hs k (w x) u t
  · intro k t
    have hobv : ∀ x, iteratedDeriv k (fun s : ℝ => mehlerN a (g x) (w x + s • u)) t =
        (Real.cos a / Real.sin a) ^ k *
          ∫ z, g x (Real.cos a • (w x + t • u) + Real.sin a • z) * mehlerNHerm k z u
            ∂(stdGaussian E) := fun x =>
      mehlerN_iteratedDeriv_line_at a (hgx x) ⟨C, hC x⟩ hs k (w x) u t
    simp only [hobv]
    refine (StronglyMeasurable.const_mul ?_ _).aestronglyMeasurable
    refine StronglyMeasurable.integral_prod_right (f := fun x z =>
      g x (Real.cos a • (w x + t • u) + Real.sin a • z) * mehlerNHerm k z u) ?_
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · have hm2 : Measurable (fun p : X × E =>
          (p.1, Real.cos a • (w p.1 + t • u) + Real.sin a • p.2)) :=
        measurable_fst.prodMk
          ((((hw.comp measurable_fst).add_const (t • u)).const_smul (Real.cos a)).add
            (measurable_snd.const_smul (Real.sin a)))
      exact hg.comp hm2
    · exact (mvbe_continuous_mehlerNHerm k u).measurable.comp measurable_snd

end mehlerFamily



theorem mvbe_psd_aux {d : ℕ} {Sq : Matrix (Fin d) (Fin d) ℝ} {σ c s : ℝ} (hσ : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hcs : c ^ 2 + s ^ 2 = 1)
    (hS : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ Sq) :
    ((c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
      - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  set D : Matrix (Fin d) (Fin d) ℝ := Sq - σ • 1 with hD
  have hD0 : 0 ≤ D := sub_nonneg.2 hS
  have hDsa : IsSelfAdjoint D := hD0.isSelfAdjoint
  have hSq : Sq = D + σ • 1 := by rw [hD]; abel
  have h1 : 0 ≤ D * D := by
    have := star_mul_self_nonneg D
    rwa [hDsa.star_eq] at this
  have key : (c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
      - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
      = (c ^ 2) • (D * D + (2 * σ) • D)
        + (s ^ 2 * (1 - σ ^ 2)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [hSq]
    have hs2 : s ^ 2 = 1 - c ^ 2 := by linarith
    simp only [smul_add, add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, smul_smul]
    rw [hs2]
    module
  rw [← Matrix.nonneg_iff_posSemidef, key]
  refine add_nonneg (smul_nonneg (sq_nonneg c)
    (add_nonneg h1 (smul_nonneg (by positivity) hD0))) ?_
  exact smul_nonneg (mul_nonneg (sq_nonneg s) (by nlinarith)) zero_le_one

section gaussianPart

variable {d : ℕ}

/-- The image of the standard Gaussian under `c • toEuclideanCLM Sq` is the centred Gaussian of
covariance `(c • Sq)²`. -/
theorem mvbe_map_smul_clm {Sq : Matrix (Fin d) (Fin d) ℝ} (hSq : 0 ≤ Sq) {c : ℝ} (hc : 0 ≤ c) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map
        (fun x => c • toEuclideanCLM (𝕜 := ℝ) Sq x)
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) ((c • Sq) * (c • Sq)) := by
  rw [multivariateGaussian_eq_map, CFC.sqrt_mul_self _ (smul_nonneg hc hSq)]
  congr 1
  funext x
  simp

/-- The Gaussian decomposition of `cos α A x + sin α z`: it is the convolution of the isotropic
`σ z` with an independent centred Gaussian `ρ`. -/
theorem mvbe_conv_decomp {Sq : Matrix (Fin d) (Fin d) ℝ} (hSq : 0 ≤ Sq) {σ c s : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hS : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ Sq) :
    ((stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (fun x => c • toEuclideanCLM (𝕜 := ℝ) Sq x)) ∗
        ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => s • z))
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          ((c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
            - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∗
        ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => σ • z)) := by
  have hM1 : ((c • Sq) * (c • Sq)).PosSemidef := by
    have hb : 0 ≤ c • Sq := smul_nonneg hc hSq
    have := hb.isSelfAdjoint
    rw [← Matrix.nonneg_iff_posSemidef]
    have h2 := star_mul_self_nonneg (c • Sq)
    rwa [this.star_eq] at h2
  rw [mvbe_map_smul_clm hSq hc, mvbe_stdGaussian_map_smul hs,
    mvbe_multivariateGaussian_add 0 0 hM1 (mvbe_posSemidef_smul_one d s), add_zero]
  have hdec := mvbe_gaussian_decomp (0 : EuclideanSpace ℝ (Fin d)) hσ
    (mvbe_psd_aux hσ hσ1 hcs hS)
  rw [hdec, Measure.conv_comm]
  simp


/-- Parametric integral of a measurable function against a convolution kernel is measurable. -/
theorem mvbe_measurable_integral_add {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] (ν : Measure M) [SFinite ν] {h : M → ℝ} (hh : Measurable h) :
    Measurable (fun a => ∫ b, h (a + b) ∂ν) :=
  (StronglyMeasurable.integral_prod_right (f := fun a b => h (a + b))
    (hh.comp measurable_add).stronglyMeasurable).measurable

/-- **Integral form of the Gaussian decomposition.**  For bounded measurable `h`,
`∫∫ h(c A x + s z) dγ(z) dγ(x) = ∫∫ h(R + σ z) dγ(z) dρ(R)`, with `ρ` the centred Gaussian of
covariance `(c Sq)² + s² - σ²`. -/
theorem mvbe_integral_decomp {Sq : Matrix (Fin d) (Fin d) ℝ} (hSq : 0 ≤ Sq) {σ c s : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hS : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ Sq) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ y, |h y| ≤ C) :
    ∫ x, ∫ z, h (c • toEuclideanCLM (𝕜 := ℝ) Sq x + s • z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ R, ∫ z, h (R + σ • z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            ((c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
              - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set ν₁ := γ.map (fun x => c • toEuclideanCLM (𝕜 := ℝ) Sq x) with hν₁
  set ν₂ := γ.map (fun z : EuclideanSpace ℝ (Fin d) => s • z) with hν₂
  set ν₃ := γ.map (fun z : EuclideanSpace ℝ (Fin d) => σ • z) with hν₃
  set ρ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
    ((c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
      - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) with hρ
  have hm1 : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      c • toEuclideanCLM (𝕜 := ℝ) Sq x) := by fun_prop
  have hm2 : Measurable (fun z : EuclideanSpace ℝ (Fin d) => s • z) := by fun_prop
  have hm3 : Measurable (fun z : EuclideanSpace ℝ (Fin d) => σ • z) := by fun_prop
  haveI : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map hm1.aemeasurable
  haveI : IsProbabilityMeasure ν₂ := Measure.isProbabilityMeasure_map hm2.aemeasurable
  haveI : IsProbabilityMeasure ν₃ := Measure.isProbabilityMeasure_map hm3.aemeasurable
  have hdec := mvbe_conv_decomp hSq hσ hσ1 hc hs hcs hS
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]; infer_instance
  have hint : Integrable h (ν₁ ∗ ν₂) :=
    Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hC y)
  have hint' : Integrable h (ρ ∗ ν₃) :=
    Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hC y)
  have e1 : ∫ y, h y ∂(ν₁ ∗ ν₂) =
      ∫ x, ∫ z, h (c • toEuclideanCLM (𝕜 := ℝ) Sq x + s • z) ∂γ ∂γ := by
    rw [integral_conv hint, hν₁, integral_map hm1.aemeasurable
      (mvbe_measurable_integral_add ν₂ hh).stronglyMeasurable.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact integral_map (φ := fun z : EuclideanSpace ℝ (Fin d) => s • z) hm2.aemeasurable
      (f := fun b => h (c • toEuclideanCLM (𝕜 := ℝ) Sq x + b))
      (hh.comp (measurable_const_add _)).stronglyMeasurable.aestronglyMeasurable
  have e2 : ∫ y, h y ∂(ρ ∗ ν₃) = ∫ R, ∫ z, h (R + σ • z) ∂γ ∂ρ := by
    rw [integral_conv hint']
    refine integral_congr_ae (ae_of_all _ fun R => ?_)
    exact integral_map (φ := fun z : EuclideanSpace ℝ (Fin d) => σ • z) hm3.aemeasurable
      (f := fun b => h (R + b))
      (hh.comp (measurable_const_add _)).stronglyMeasurable.aestronglyMeasurable
  rw [← e1, ← e2, hdec]

end gaussianPart


section main

open Real in
/-- **Raic's Lemma 2.6**, for `r ∈ {1,2,3}`, `0 < α ≤ π/2` and `0 < σ ≤ 1`:
`|∫ D^r (U_α f)(w)[u^r] dN(μ, S)(w)| ≤ c_r M cos^r α ‖u‖^r / σ^r`, where `U_α f = mehlerN α f`,
`|f - mid| ≤ M` and `σ • 1 ≤ CFC.sqrt S`. -/
theorem mvbe_lemma_2_6 {d r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ π / 2) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (mid M : ℝ)
    (hM : ∀ x, |f x - mid| ≤ M) (μ u : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hS : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ CFC.sqrt S) :
    |∫ w, iteratedFDeriv ℝ r (mehlerN α f) w (fun _ => u) ∂(multivariateGaussian μ S)| ≤
      mvbeHermiteConst r * M * Real.cos α ^ r * ‖u‖ ^ r / σ ^ r := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγ
  set Sq : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt S with hSqdef
  set c := Real.cos α with hcdef
  set s := Real.sin α with hsdef
  have hc : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα⟩
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have hSq0 : 0 ≤ Sq := CFC.sqrt_nonneg S
  have hfb : ∀ x, |f x| ≤ M + |mid| := by
    intro x
    have h1 : |f x| ≤ |f x - mid| + |mid| := by
      have := abs_add_le (f x - mid) mid
      simpa using this
    linarith [hM x]
  set C : ℝ := M + |mid| with hCdef
  have hG : ∀ k : ℕ, ContDiff ℝ k (mehlerN α f) := fun k =>
    mehlerN_contDiff_nat k α f hf ⟨C, hfb⟩ hs
  set A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    toEuclideanCLM (𝕜 := ℝ) Sq with hAdef
  -- Step 1: change of variables
  have hAm : Measurable (fun x : EuclideanSpace ℝ (Fin d) => μ + A x) := by fun_prop
  have hIc : Continuous (fun w => iteratedFDeriv ℝ r (mehlerN α f) w (fun _ => u)) :=
    ((hG r).continuous_iteratedFDeriv le_rfl).eval_const (fun _ => u)
  have step1 : ∫ w, iteratedFDeriv ℝ r (mehlerN α f) w (fun _ => u) ∂(multivariateGaussian μ S) =
      ∫ x, iteratedFDeriv ℝ r (mehlerN α f) (μ + A x) (fun _ => u) ∂γ := by
    unfold multivariateGaussian
    exact integral_map hAm.aemeasurable hIc.aestronglyMeasurable
  set u' : EuclideanSpace ℝ (Fin d) := (c / σ) • u with hu'def
  have hg : Measurable (Function.uncurry
      (fun (_ : EuclideanSpace ℝ (Fin d)) => f)) := hf.comp measurable_snd
  -- Step 2/3: differentiate under the integral sign (first time)
  have step3 : ∫ x, iteratedFDeriv ℝ r (mehlerN α f) (μ + A x) (fun _ => u) ∂γ =
      iteratedDeriv r (fun t : ℝ => ∫ x, mehlerN α f (μ + A x + t • u) ∂γ) 0 := by
    rw [mvbe_iteratedDeriv_integral_mehlerN γ hs hg (fun _ => hfb) hAm u r]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (mehlerN_iteratedDeriv_line_eq (hG r) (μ + A x) u).symm
  -- Step 4: the decomposition
  set ρ : Measure (EuclideanSpace ℝ (Fin d)) := multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin d))
    ((c • Sq) * (c • Sq) + (s ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)
      - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) with hρ
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  set g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun R y => f (c • μ + R + (σ * √2) • y) with hg'def
  have hg'm : Measurable (Function.uncurry g') := by
    have : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        c • μ + p.1 + (σ * √2) • p.2) :=
      (measurable_fst.const_add (c • μ)).add (measurable_snd.const_smul (σ * √2))
    exact hf.comp this
  have hk : √2 * (√2 / 2) = 1 := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have e1 : σ * √2 * (√2 / 2) = σ := by linear_combination σ * hk
  have step4 : ∀ t : ℝ, ∫ x, mehlerN α f (μ + A x + t • u) ∂γ =
      ∫ R, mehlerN (π / 4) (g' R) (0 + t • u') ∂ρ := by
    intro t
    set ht : EuclideanSpace ℝ (Fin d) → ℝ := fun y => f (c • (μ + t • u) + y) with hht
    have hhtm : Measurable ht := hf.comp (measurable_const_add _)
    have h1 : ∫ x, mehlerN α f (μ + A x + t • u) ∂γ =
        ∫ x, ∫ z, ht (c • A x + s • z) ∂γ ∂γ := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show ∫ z, f (c • (μ + A x + t • u) + s • z) ∂γ = _
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hht]
      congr 1
      module
    rw [h1, mvbe_integral_decomp hSq0 hσ.le hσ1 hc hs.le hcs hS hhtm (fun y => hfb _)]
    refine integral_congr_ae (ae_of_all _ fun R => ?_)
    show _ = ∫ z, g' R (Real.cos (π / 4) • (0 + t • u') + Real.sin (π / 4) • z) ∂γ
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hht, hg'def, hu'def, Real.cos_pi_div_four, Real.sin_pi_div_four]
    congr 1
    have e2 : (σ * √2) • ((√2 / 2) • ((0 : EuclideanSpace ℝ (Fin d)) + t • (c / σ) • u)
        + (√2 / 2) • z) = (t * c) • u + σ • z := by
      simp only [zero_add, smul_add, smul_smul]
      have e3 : σ * √2 * (√2 / 2 * (t * (c / σ))) = t * c := by
        have : σ * √2 * (√2 / 2 * (t * (c / σ))) = (σ * √2 * (√2 / 2)) * (t * (c / σ)) := by ring
        rw [this, e1]
        field_simp
      rw [e1, e3]
    rw [e2]
    module
  -- Step 5: differentiate under the integral sign (second time)
  have hg'b : ∀ R y, |g' R y| ≤ C := fun R y => hfb _
  have hsin4 : 0 < Real.sin (π / 4) := by rw [Real.sin_pi_div_four]; positivity
  have step5 : iteratedDeriv r (fun t : ℝ => ∫ x, mehlerN α f (μ + A x + t • u) ∂γ) 0 =
      ∫ R, iteratedDeriv r (fun t : ℝ => mehlerN (π / 4) (g' R) (0 + t • u')) 0 ∂ρ := by
    have := mvbe_iteratedDeriv_integral_mehlerN ρ hsin4 hg'm hg'b
      (w := fun _ => 0) measurable_const u' r
    rw [← this]
    congr 1
    funext t
    exact step4 t
  -- Step 6: Raic's Lemma 2.5 for each `R`
  have step6 : ∀ R, |iteratedDeriv r (fun t : ℝ => mehlerN (π / 4) (g' R) (0 + t • u')) 0| ≤
      mvbeHermiteConst r * M * ‖u'‖ ^ r := by
    intro R
    have hgR : Measurable (g' R) := hg'm.of_uncurry_left
    rw [mehlerN_iteratedDeriv_line (π / 4) hgR ⟨C, hg'b R⟩ hsin4 r 0 u']
    have hcot : Real.cos (π / 4) / Real.sin (π / 4) = 1 := by
      rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      exact div_self (by positivity)
    rw [hcot, one_pow, one_mul]
    set fh : EuclideanSpace ℝ (Fin d) → ℝ := fun z => f (c • μ + R + σ • z) with hfh
    have hfhm : Measurable fh :=
      hf.comp ((measurable_id.const_smul σ).const_add (c • μ + R))
    have hint : ∫ z, g' R (Real.cos (π / 4) • (0 : EuclideanSpace ℝ (Fin d))
          + Real.sin (π / 4) • z) * mehlerNHerm r z u' ∂γ
        = ∫ z, fh z * mehlerNHerm r z u' ∂γ := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hg'def, hfh, smul_zero, zero_add, Real.sin_pi_div_four, smul_smul, e1]
    rw [hint]
    have hb := mvbe_gaussian_hermite_integral_le_scaled hr1 hr3 u' fh hfhm mid M
      (fun z => hM _)
    have hform : ∫ z, fh z * mehlerNHerm r z u' ∂γ =
        ‖u'‖ ^ r * ∫ z, fh z * Polynomial.aeval (⟪z, u'⟫ / ‖u'‖) (Polynomial.hermite r) ∂γ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [mehlerNHerm]
      ring
    rw [hform, abs_mul, abs_pow, abs_norm, mul_comm]
    exact hb
  -- Step 7: integrate the bound over the probability measure `ρ`
  have step7 : |∫ R, iteratedDeriv r (fun t : ℝ => mehlerN (π / 4) (g' R) (0 + t • u')) 0 ∂ρ|
      ≤ mvbeHermiteConst r * M * ‖u'‖ ^ r := by
    have := norm_integral_le_of_norm_le_const (μ := ρ)
      (f := fun R => iteratedDeriv r (fun t : ℝ => mehlerN (π / 4) (g' R) (0 + t • u')) 0)
      (C := mvbeHermiteConst r * M * ‖u'‖ ^ r)
      (ae_of_all _ fun R => by rw [Real.norm_eq_abs]; exact step6 R)
    simpa [Measure.real] using this
  -- Step 8: assemble
  rw [step1, step3, step5]
  refine step7.trans (le_of_eq ?_)
  rw [hu'def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc hσ.le), mul_pow, div_pow]
  field_simp

open Real in
/-- **Lemma 2.6 for arbitrary `σ > 0`** (no upper bound on `σ`): the bound with `min σ 1`. -/
theorem mvbe_lemma_2_6_min {d r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ π / 2) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (mid M : ℝ)
    (hM : ∀ x, |f x - mid| ≤ M) (μ u : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hS : σ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ CFC.sqrt S) :
    |∫ w, iteratedFDeriv ℝ r (mehlerN α f) w (fun _ => u) ∂(multivariateGaussian μ S)| ≤
      mvbeHermiteConst r * M * Real.cos α ^ r * ‖u‖ ^ r / (min σ 1) ^ r := by
  refine mvbe_lemma_2_6 hr1 hr3 hα0 hα hf mid M hM μ u S (lt_min hσ one_pos) (min_le_right _ _)
    (le_trans ?_ hS)
  rw [← sub_nonneg, ← sub_smul]
  exact smul_nonneg (sub_nonneg.2 (min_le_left _ _)) zero_le_one

end main


end LatticeProb
