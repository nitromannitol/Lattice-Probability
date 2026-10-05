import Mathlib

/-!
# Mollification of a `C¹` function with Lipschitz gradient

Packet P17 of the staged formalisation of Raic's Theorem 1.3 (A multivariate Berry-Esseen theorem
with explicit constants, arXiv:1802.06475): the mollification step replacing Rademacher's theorem
in Lemma 2.7.  The smoothing function `f = g(ρ_A / ε)` of Lemma 2.1 is `C¹` with
`4(1+κ)/ε²`-Lipschitz gradient but need not be `C²`.  We convolve it with a smooth normalised bump.

Let `E` be a finite-dimensional real normed space (e.g. `EuclideanSpace ℝ (Fin m)`).

* `MvbeMollifyKernel μ φ r`: `φ` is smooth, compactly supported, nonnegative, even, of integral
  `1`, and vanishes outside the closed ball of radius `r`; `mvbeMollifyKernel_exists` builds one
  from `ContDiffBump.normed` for any `r > 0`.
* `mvbeMollify μ φ f x = ∫ φ t • f (x - t) dμ(t)`.
* `mvbeMollify_taylor`: `|f (x + v) - f x - Df x v| ≤ L ‖v‖² / 2` for `C¹` `f` with `L`-Lipschitz
  gradient.
* `mvbeMollify_hasFDerivAt`, `mvbeMollify_fderiv`: `D(f * φ) = (Df) * φ` (differentiation under
  the integral sign), `mvbeMollify_fderiv_lipschitz`: this gradient is again `L`-Lipschitz,
  `mvbeMollify_contDiff`: `f * φ` is `C^∞` (Mathlib's convolution API).
* `mvbeMollify_sub_le`: `|f * φ - f| ≤ L r² / 2`.  The first-order Taylor term cancels because `φ`
  is even.
* `mvbeMollify_fderiv_eq_zero`: if `f` is constant on `ball x ρ` and `r < ρ`, then `D(f * φ) = 0`
  on `ball x (ρ - r)`.
* `mvbeMollify_exists` (generic), `mvbeMollify_exists_of_sets` (constant regions `S1`, `S0`),
  `mvbeMollify_exists_euclidean` (`EuclideanSpace ℝ (Fin m)`, closed-ball form): for every
  `η > 0` there is `g` with
  (a) `g` is `C^∞`, and `g`, `fderiv g`, `iteratedFDeriv ℝ 2 g` are bounded (so `g` is `C²_b`);
  (b) `‖iteratedFDeriv ℝ 2 g x‖ ≤ L` for all `x`;
  (c) `|g x - f x| ≤ L η²` (the proof gives `L η² / 8`: the kernel has radius `η / 2` and the
      first-order term cancels);
  (d) `iteratedFDeriv ℝ 2 g x = 0` whenever `f` is constant on the open ball `ball x η` (hence also
      when `f` is constant on `closedBall x η`).  The kernel has radius `η / 2`, so the gradient
      of `g` vanishes on `ball x (η / 2)`.
-/

namespace LatticeProb

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

/-- Quadratic Taylor bound for a `C¹` function with `L`-Lipschitz gradient. -/
theorem mvbeMollify_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) (x v : E) :
    |f (x + v) - f x - fderiv ℝ f x v| ≤ L * ‖v‖ ^ 2 / 2 := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  set h : ℝ → ℝ := fun s => f (x + s • v) - f x - s * fderiv ℝ f x v with hh_def
  have hh : ∀ s : ℝ, HasDerivAt h (fderiv ℝ f (x + s • v) v - fderiv ℝ f x v) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add x
    have h2 := (hd (x + s • v)).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => s * fderiv ℝ f x v) (fderiv ℝ f x v) s := by
      simpa using (hasDerivAt_id s).mul_const (fderiv ℝ f x v)
    exact (h2.sub_const (f x)).sub h3
  have hB : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (L * ‖v‖ ^ 2 / 2) * s ^ 2)
      ((L * ‖v‖ ^ 2 / 2) * (2 * s)) s := by
    intro s
    simpa using ((hasDerivAt_pow 2 s).const_mul (L * ‖v‖ ^ 2 / 2))
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := h)
    (f' := fun s => fderiv ℝ f (x + s • v) v - fderiv ℝ f x v)
    (fun s _ => (hh s).continuousAt.continuousWithinAt)
    (fun s _ => (hh s).hasDerivWithinAt) (B := fun s : ℝ => (L * ‖v‖ ^ 2 / 2) * s ^ 2)
    (B' := fun s => (L * ‖v‖ ^ 2 / 2) * (2 * s)) (by simp [hh_def]) hB
    (by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have h1 : ‖fderiv ℝ f (x + s • v) - fderiv ℝ f x‖ ≤ L * (s * ‖v‖) := by
        rw [← dist_eq_norm]
        have := hL.dist_le_mul (x + s • v) x
        simpa [dist_eq_norm, norm_smul, abs_of_nonneg hs0] using this
      calc ‖fderiv ℝ f (x + s • v) v - fderiv ℝ f x v‖
          = ‖(fderiv ℝ f (x + s • v) - fderiv ℝ f x) v‖ := by simp
        _ ≤ ‖fderiv ℝ f (x + s • v) - fderiv ℝ f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * (s * ‖v‖) * ‖v‖ := by gcongr
        _ = (L * ‖v‖ ^ 2 / 2) * (2 * s) := by ring)
  have := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [hh_def, Real.norm_eq_abs] using this

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A mollifier kernel of radius `r` for the measure `μ`: smooth, compactly supported, nonnegative,
even, supported in the closed ball of radius `r`, and of integral `1`. -/
structure MvbeMollifyKernel (μ : Measure E) (φ : E → ℝ) (r : ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ
  hasCompactSupport : HasCompactSupport φ
  nonneg : ∀ t, 0 ≤ φ t
  integral_eq_one : ∫ t, φ t ∂μ = 1
  neg : ∀ t, φ (-t) = φ t
  norm_le : ∀ t, φ t ≠ 0 → ‖t‖ ≤ r

/-- Existence of a mollifier kernel of any positive radius. -/
theorem mvbeMollifyKernel_exists (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    ∃ φ : E → ℝ, MvbeMollifyKernel μ φ r := by
  let b : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨b.normed μ, ⟨b.contDiff_normed (n := ⊤), b.hasCompactSupport_normed,
    b.nonneg_normed, b.integral_normed, b.normed_neg, ?_⟩⟩
  intro t ht
  have : t ∈ Function.support (b.normed μ) := ht
  rw [b.support_normed_eq] at this
  simpa using (mem_ball_zero_iff.mp this).le

end Kernel


section Mollify

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {φ : E → ℝ} {r : ℝ}

/-- The mollification `f * φ`: `x ↦ ∫ φ t • f (x - t) dμ(t)`. -/
noncomputable def mvbeMollify (μ : Measure E) (φ f : E → ℝ) : E → ℝ :=
  fun x => ∫ t, φ t • f (x - t) ∂μ

omit [FiniteDimensional ℝ E] in
theorem MvbeMollifyKernel.integrable (hφ : MvbeMollifyKernel μ φ r) : Integrable φ μ :=
  hφ.contDiff.continuous.integrable_of_hasCompactSupport hφ.hasCompactSupport

theorem MvbeMollifyKernel.integrable_smul_comp (hφ : MvbeMollifyKernel μ φ r)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : E → G} (hk : Continuous k)
    {C : ℝ} (hC : ∀ y, ‖k y‖ ≤ C) (x : E) : Integrable (fun t => φ t • k (x - t)) μ := by
  refine Integrable.mono' (g := fun t => φ t * C) (hφ.integrable.mul_const C) ?_ ?_
  · exact (hφ.contDiff.continuous.smul
      (hk.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_smul, Real.norm_of_nonneg (hφ.nonneg t)]
    exact mul_le_mul_of_nonneg_left (hC _) (hφ.nonneg t)

omit [FiniteDimensional ℝ E] in
theorem MvbeMollifyKernel.norm_integral_smul_comp_le (hφ : MvbeMollifyKernel μ φ r)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : E → G}
    {C : ℝ} (hC : ∀ y, ‖k y‖ ≤ C) (x : E) : ‖∫ t, φ t • k (x - t) ∂μ‖ ≤ C := by
  calc ‖∫ t, φ t • k (x - t) ∂μ‖ ≤ ∫ t, φ t * C ∂μ := by
        refine norm_integral_le_of_norm_le (hφ.integrable.mul_const C)
          (Filter.Eventually.of_forall fun t => ?_)
        rw [norm_smul, Real.norm_of_nonneg (hφ.nonneg t)]
        exact mul_le_mul_of_nonneg_left (hC _) (hφ.nonneg t)
    _ = C := by rw [integral_mul_const, hφ.integral_eq_one, one_mul]

theorem mvbeMollify_hasFDerivAt (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {C0 C1 : ℝ} (hC0 : ∀ x, |f x| ≤ C0) (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) (x : E) :
    HasFDerivAt (mvbeMollify μ φ f) (∫ t, φ t • fderiv ℝ f (x - t) ∂μ) x := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hcont : Continuous f := hf.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => φ t • f (x - t))
    (F' := fun x t => φ t • fderiv ℝ f (x - t)) (bound := fun t => φ t * C1) (s := univ)
    univ_mem ?_ ?_ ?_ ?_ (hφ.integrable.mul_const C1) ?_
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (hφ.contDiff.continuous.smul
      (hcont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact hφ.integrable_smul_comp hcont hC0 x
  · exact (hφ.contDiff.continuous.smul
      (hdc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t y _ => ?_
    rw [norm_smul, Real.norm_of_nonneg (hφ.nonneg t)]
    exact mul_le_mul_of_nonneg_left (hC1 _) (hφ.nonneg t)
  · refine Filter.Eventually.of_forall fun t y _ => ?_
    have h1 : HasFDerivAt (fun z : E => z - t) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).sub_const t
    have h2 := ((hfd (y - t)).hasFDerivAt.comp y h1).const_smul (φ t)
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2

theorem mvbeMollify_fderiv (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {C0 C1 : ℝ} (hC0 : ∀ x, |f x| ≤ C0) (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) :
    fderiv ℝ (mvbeMollify μ φ f) = fun x => ∫ t, φ t • fderiv ℝ f (x - t) ∂μ :=
  funext fun x => (mvbeMollify_hasFDerivAt hφ hf hC0 hC1 x).fderiv

theorem mvbeMollify_contDiff (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ} (hf : Continuous f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mvbeMollify μ φ f) :=
  hφ.hasCompactSupport.contDiff_convolution_left (μ := μ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (n := ⊤) hφ.contDiff hf.locallyIntegrable

theorem mvbeMollify_fderiv_lipschitz (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {C1 : ℝ} (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ f)) :
    LipschitzWith L (fun x => ∫ t, φ t • fderiv ℝ f (x - t) ∂μ) := by
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, ← integral_sub (hφ.integrable_smul_comp hdc hC1 x)
    (hφ.integrable_smul_comp hdc hC1 y)]
  calc ‖∫ t, (φ t • fderiv ℝ f (x - t) - φ t • fderiv ℝ f (y - t)) ∂μ‖
      ≤ ∫ t, φ t * (L * dist x y) ∂μ := by
        refine norm_integral_le_of_norm_le (hφ.integrable.mul_const _)
          (Filter.Eventually.of_forall fun t => ?_)
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ.nonneg t), ← dist_eq_norm]
        have := hL.dist_le_mul (x - t) (y - t)
        rw [dist_sub_right] at this
        exact mul_le_mul_of_nonneg_left this (hφ.nonneg t)
    _ = L * dist x y := by rw [integral_mul_const, hφ.integral_eq_one, one_mul]

/-- The norm of the second Fréchet derivative is the norm of the derivative of the derivative. -/
theorem mvbeMollify_norm_iteratedFDeriv_two_eq {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : G → ℝ) (x : G) :
    ‖iteratedFDeriv ℝ 2 g x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := 1)
  rw [norm_iteratedFDeriv_one] at h
  simpa using h.symm

/-- If the derivative of the derivative vanishes at `x`, so does the second iterated derivative. -/
theorem mvbeMollify_iteratedFDeriv_two_eq_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : G → ℝ) (x : G) (h : fderiv ℝ (fderiv ℝ g) x = 0) :
    iteratedFDeriv ℝ 2 g x = 0 := by
  have h0 : ‖fderiv ℝ (fderiv ℝ g) x‖ = 0 := (norm_eq_zero (E := G →L[ℝ] G →L[ℝ] ℝ)).mpr h
  exact norm_eq_zero.mp ((mvbeMollify_norm_iteratedFDeriv_two_eq g x).trans h0)

/-- The first-order Taylor term of `f` integrates to zero against an even kernel. -/
theorem MvbeMollifyKernel.integral_fderiv_eq_zero (hφ : MvbeMollifyKernel μ φ r)
    (ℓ : E →L[ℝ] ℝ) :
    ∫ t, φ t * ℓ t ∂μ = 0 := by
  have h : ∫ t, φ t * ℓ t ∂μ = - ∫ t, φ t * ℓ t ∂μ := by
    conv_lhs => rw [← integral_neg_eq_self (fun t => φ t * ℓ t) μ]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [hφ.neg t]
  linarith

/-- **Approximation by the mollification (order two).**  If `f` is `C¹` with bounded `f`, `∇f`,
and `L`-Lipschitz `∇f`, then `|f * φ - f| ≤ L r² / 2` for a kernel supported in the ball of
radius `r`. -/
theorem mvbeMollify_sub_le (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {C0 C1 : ℝ} (hC0 : ∀ x, |f x| ≤ C0) (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) {L : ℝ≥0}
    (hL : LipschitzWith L (fderiv ℝ f)) (x : E) :
    |mvbeMollify μ φ f x - f x| ≤ L * r ^ 2 / 2 := by
  have hcont : Continuous f := hf.continuous
  have hr : 0 ≤ r := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have hzero : ∀ t, φ t = 0 := fun t => by
      by_contra h
      have := hφ.norm_le t h
      linarith [norm_nonneg t]
    have := hφ.integral_eq_one
    simp [hzero] at this
  have hC1' : 0 ≤ C1 := (norm_nonneg _).trans (hC1 x)
  have hA : Integrable (fun t => φ t • f (x - t)) μ :=
    hφ.integrable_smul_comp hcont (fun y => by simpa using hC0 y) x
  have hB : Integrable (fun t => φ t • f x) μ := hφ.integrable.smul_const (f x)
  have hψ : Integrable (fun t => φ t * fderiv ℝ f x t) μ := by
    refine Integrable.mono' (g := fun t => φ t * (C1 * r)) (hφ.integrable.mul_const (C1 * r)) ?_ ?_
    · exact (hφ.contDiff.continuous.mul (fderiv ℝ f x).continuous).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      by_cases h : φ t = 0
      · simp [h]
      · rw [norm_mul, Real.norm_of_nonneg (hφ.nonneg t)]
        refine mul_le_mul_of_nonneg_left ?_ (hφ.nonneg t)
        calc ‖fderiv ℝ f x t‖ ≤ ‖fderiv ℝ f x‖ * ‖t‖ := (fderiv ℝ f x).le_opNorm t
          _ ≤ C1 * r := mul_le_mul (hC1 x) (hφ.norm_le t h) (norm_nonneg _) hC1'
  have hAB : Integrable (fun t => φ t • f (x - t) - φ t • f x) μ := hA.sub hB
  have hB' : ∫ t, φ t • f x ∂μ = f x := by
    rw [integral_smul_const, hφ.integral_eq_one, one_smul]
  have hdiff : mvbeMollify μ φ f x - f x
      = ∫ t, (φ t • f (x - t) - φ t • f x + φ t * fderiv ℝ f x t) ∂μ := by
    rw [integral_add hAB hψ, integral_sub hA hB, hB', hφ.integral_fderiv_eq_zero]
    simp [mvbeMollify]
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∫ t, (φ t • f (x - t) - φ t • f x + φ t * fderiv ℝ f x t) ∂μ‖
      ≤ ∫ t, φ t * (L * r ^ 2 / 2) ∂μ := by
        refine norm_integral_le_of_norm_le (hφ.integrable.mul_const _)
          (Filter.Eventually.of_forall fun t => ?_)
        by_cases h : φ t = 0
        · simp [h]
        · have htay := mvbeMollify_taylor hf hL x (-t)
          have hrt : ‖-t‖ ^ 2 ≤ r ^ 2 := by
            rw [norm_neg]
            exact pow_le_pow_left₀ (norm_nonneg _) (hφ.norm_le t h) 2
          have e : φ t • f (x - t) - φ t • f x + φ t * fderiv ℝ f x t
              = φ t * (f (x + -t) - f x - fderiv ℝ f x (-t)) := by
            simp [sub_eq_add_neg]
            ring
          rw [e, norm_mul, Real.norm_of_nonneg (hφ.nonneg t)]
          refine mul_le_mul_of_nonneg_left ?_ (hφ.nonneg t)
          rw [Real.norm_eq_abs]
          refine htay.trans ?_
          have : (0 : ℝ) ≤ L := L.coe_nonneg
          nlinarith [hrt]
    _ = L * r ^ 2 / 2 := by rw [integral_mul_const, hφ.integral_eq_one, one_mul]

/-- If `f` is constant on `ball x ρ` and the kernel has radius `r < ρ`, then the mollification
has vanishing gradient on `ball x (ρ - r)`. -/
theorem mvbeMollify_fderiv_eq_zero (hφ : MvbeMollifyKernel μ φ r) {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    {C0 C1 : ℝ} (hC0 : ∀ x, |f x| ≤ C0) (hC1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1) {x : E} {ρ : ℝ} {c : ℝ}
    (hc : ∀ y ∈ ball x ρ, f y = c) {x' : E} (hx' : x' ∈ ball x (ρ - r)) :
    fderiv ℝ (mvbeMollify μ φ f) x' = 0 := by
  rw [mvbeMollify_fderiv hφ hf hC0 hC1]
  have : ∀ t, φ t • fderiv ℝ f (x' - t) = 0 := by
    intro t
    by_cases h : φ t = 0
    · simp [h]
    · have hmem : x' - t ∈ ball x ρ := by
        rw [mem_ball, dist_eq_norm] at hx' ⊢
        have h1 := hφ.norm_le t h
        calc ‖x' - t - x‖ = ‖(x' - x) - t‖ := by congr 1; abel
          _ ≤ ‖x' - x‖ + ‖t‖ := norm_sub_le _ _
          _ < ρ := by linarith
      have hev : f =ᶠ[𝓝 (x' - t)] fun _ => c :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hmem) hc
      simp [hev.fderiv_eq]
  simp [this]


/-- **Mollification of a `C¹` function with Lipschitz gradient** (measure-explicit form).
See `mvbeMollify_exists` for the statement without a measure. -/
theorem mvbeMollify_exists_of_measure (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) {η : ℝ} (hη : 0 < η) :
    ∃ g : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ L) ∧ (∀ x, |g x - f x| ≤ L * η ^ 2) ∧
      (∀ x, (∃ c, ∀ y ∈ Metric.ball x η, f y = c) → iteratedFDeriv ℝ 2 g x = 0) := by
  obtain ⟨C0, hC0⟩ := hf0
  obtain ⟨C1, hC1⟩ := hf1
  obtain ⟨φ, hφ⟩ := mvbeMollifyKernel_exists μ (half_pos hη)
  have hfd := mvbeMollify_fderiv hφ hf hC0 hC1
  have hlip := mvbeMollify_fderiv_lipschitz hφ hf hC1 hL
  have hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 (mvbeMollify μ φ f) x‖ ≤ L := by
    intro x
    rw [mvbeMollify_norm_iteratedFDeriv_two_eq, hfd]
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  refine ⟨mvbeMollify μ φ f, mvbeMollify_contDiff hφ hf.continuous, ⟨C0, fun x => ?_⟩,
    ⟨C1, fun x => ?_⟩, ⟨L, hb2⟩, hb2, fun x => ?_, fun x hx => ?_⟩
  · have h := hφ.norm_integral_smul_comp_le (k := f) (C := C0) (fun y => by simpa using hC0 y) x
    rw [Real.norm_eq_abs] at h
    exact h
  · rw [hfd]
    exact hφ.norm_integral_smul_comp_le (k := fderiv ℝ f) (C := C1) hC1 x
  · refine (mvbeMollify_sub_le hφ hf hC0 hC1 hL x).trans ?_
    have : (0 : ℝ) ≤ L := L.coe_nonneg
    nlinarith [sq_nonneg η, mul_nonneg this (sq_nonneg η)]
  · obtain ⟨c, hc⟩ := hx
    have h0 : ∀ x' ∈ ball x (η / 2), fderiv ℝ (mvbeMollify μ φ f) x' = 0 := by
      intro x' hx'
      refine mvbeMollify_fderiv_eq_zero hφ hf hC0 hC1 hc ?_
      have : η - η / 2 = η / 2 := by ring
      rwa [this]
    have hev : fderiv ℝ (mvbeMollify μ φ f) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (half_pos hη))) h0
    have h1 : fderiv ℝ (fderiv ℝ (mvbeMollify μ φ f)) x = 0 := by
      rw [hev.fderiv_eq]
      simp
    exact mvbeMollify_iteratedFDeriv_two_eq_zero _ x h1

end Mollify

section Final

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Mollification of a `C¹` function with Lipschitz gradient (generic form).**
Let `f` be `C¹` on a finite-dimensional real normed space with `f` and `fderiv f` bounded and
`fderiv f` `L`-Lipschitz.  For every `η > 0` there is a `C^∞` function `g` (the convolution of `f`
with a smooth normalised bump supported in the ball of radius `η / 2`) with `g`, `fderiv g`,
`iteratedFDeriv ℝ 2 g` bounded (so `g` is `C²_b`), `‖D²g‖ ≤ L` everywhere,
`|g - f| ≤ L η²` (the proof gives `L η² / 8`), and `D²g x = 0` whenever `f` is constant on the
open ball `ball x η`. -/
theorem mvbeMollify_exists {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) {η : ℝ} (hη : 0 < η) :
    ∃ g : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ L) ∧ (∀ x, |g x - f x| ≤ L * η ^ 2) ∧
      (∀ x, (∃ c, ∀ y ∈ Metric.ball x η, f y = c) → iteratedFDeriv ℝ 2 g x = 0) := by
  borelize E
  exact mvbeMollify_exists_of_measure (Measure.addHaar : Measure E) hf hf0 hf1 hL hη

omit [FiniteDimensional ℝ E] in
/-- A `C^∞` function is `C²`. -/
theorem mvbeMollify_contDiff_two_of_contDiff_top {g : E → ℝ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) : ContDiff ℝ 2 g :=
  hg.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- **Mollification with prescribed constant regions.**  If `f = 1` on `S1` and `f = 0` on `S0`,
the mollification `g` of `mvbeMollify_exists` has vanishing second derivative at every `x` such that
the closed ball `closedBall x η` lies in `S1` or in `S0`. -/
theorem mvbeMollify_exists_of_sets {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) {η : ℝ} (hη : 0 < η) {S1 S0 : Set E}
    (h1 : ∀ y ∈ S1, f y = 1) (h0 : ∀ y ∈ S0, f y = 0) :
    ∃ g : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ L) ∧ (∀ x, |g x - f x| ≤ L * η ^ 2) ∧
      (∀ x, Metric.closedBall x η ⊆ S1 ∨ Metric.closedBall x η ⊆ S0 →
        iteratedFDeriv ℝ 2 g x = 0) := by
  obtain ⟨g, hg, hg0, hg1, hg2, hgL, hgf, hgd⟩ := mvbeMollify_exists hf hf0 hf1 hL hη
  refine ⟨g, hg, hg0, hg1, hg2, hgL, hgf, fun x hx => hgd x ?_⟩
  rcases hx with hx | hx
  · exact ⟨1, fun y hy => h1 y (hx (Metric.ball_subset_closedBall hy))⟩
  · exact ⟨0, fun y hy => h0 y (hx (Metric.ball_subset_closedBall hy))⟩

/-- The statement of `mvbeMollify_exists` on `EuclideanSpace ℝ (Fin m)`, with the closed-ball form
of the locally-constant clause. -/
theorem mvbeMollify_exists_euclidean {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) {η : ℝ} (hη : 0 < η) :
    ∃ g : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 2 g ∧ (∃ C, ∀ x, |g x| ≤ C) ∧
      (∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C) ∧ (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ L) ∧ (∀ x, |g x - f x| ≤ L * η ^ 2) ∧
      (∀ x, (∃ c, ∀ y ∈ Metric.closedBall x η, f y = c) → iteratedFDeriv ℝ 2 g x = 0) := by
  obtain ⟨g, hg, hg0, hg1, hg2, hgL, hgf, hgd⟩ := mvbeMollify_exists hf hf0 hf1 hL hη
  refine ⟨g, mvbeMollify_contDiff_two_of_contDiff_top hg, hg0, hg1, hg2, hgL, hgf, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hx
  exact hgd x ⟨c, fun y hy => hc y (Metric.ball_subset_closedBall hy)⟩

end Final

end LatticeProb
