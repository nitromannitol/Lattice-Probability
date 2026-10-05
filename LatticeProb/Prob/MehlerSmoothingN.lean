import Mathlib
import LatticeProb.Prob.MehlerSmoothing

/-!
# Mehler smoothing calculus in dimension `d` (packet P8a, report item L7)

For `E` a finite-dimensional real inner product space (in particular `E = EuclideanSpace ℝ (Fin d)`)
and `γ = stdGaussian E`,
`mehlerN a f w = ∫ f (cos a • w + sin a • z) dγ(z)`.

Main results, for `f` bounded Borel and `0 < sin a`:

* `mehlerN_iteratedDeriv_line`: for every `u : E` and `r : ℕ`,
  `(d/dt)^r mehlerN a f (w + t u) |_{t=0} = (cot a)^r ∫ f(cos a w + sin a z) mehlerNHerm r z u dγ`,
  with the homogeneous Hermite factor `mehlerNHerm r z u = ‖u‖^r He_r(⟪z,u⟫/‖u‖)`, and the bound
  `mehlerN_iteratedDeriv_line_bound` by `C |cot a|^r ‖u‖^r ∫ |He_r| dγ₁`.
* `mehlerN_lipschitz`, `mehlerN_hasFDerivAt`, `mehlerN_contDiff`: `mehlerN a f` is `C^∞`
  (`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, not analytic) with `fderiv` given by `mehlerNGrad`.
* `mehlerN_iteratedFDeriv_diag` and `mehlerN_iteratedFDeriv_diag_bound`: the same formula and bound
  for `iteratedFDeriv ℝ r (mehlerN a f) w (fun _ => u)`, every `r`.
* `mehlerN_iteratedFDeriv_three` (the bridge between the third line derivative and
  `iteratedFDeriv ℝ 3 _ w ![u, u, u]`), and its two evaluations
  `mehlerN_iteratedFDeriv_three_hermite` and `mehlerN_iteratedFDeriv_three_C2b`
  (the `C²_b` form, Raic (2.7)).

Route.  Directional derivatives: for a unit vector `v`, the splitting `z = σ v + (y - ⟪v,y⟫ v)`
(`mehlerN_split_map`: `γ = ((gaussianReal 0 1).prod γ).map mehlerNPsi`, proved with
`Measure.ext_of_charFun`) reduces the line `t ↦ mehlerN a f (w + t v)` to a `γ`-average over `y` of
one-dimensional Mehler smoothings of the slices `x ↦ f (q_y + x v)`, to which the one-dimensional
calculus of `MehlerCore` (`mehlerH_hasDerivAt`, uniform in the slice) applies; the `y`-integral is
differentiated under the sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
Smoothness: the line derivatives give a global Lipschitz bound, hence (Rademacher's lemma
`LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`) a Fréchet derivative; then the semigroup
property `mehlerN a f = mehlerN a' (mehlerN a'' f)` (`cos a = cos a' cos a''`, proved from
`Measure.ext_of_charFun`) lets one differentiate under the integral sign
(`mehlerN_hasFDerivAt_of_fderiv_bdd`) and induct on the smoothness order:
`∂_y (mehlerN a f) = cos a' · mehlerN a' (∂_y (mehlerN a'' f))`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

noncomputable section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Mehler smoothing in a finite-dimensional inner product space:
`mehlerN a f w = ∫ f (cos a • w + sin a • z) dγ(z)`, `γ = stdGaussian E`. -/
def mehlerN (a : ℝ) (f : E → ℝ) (w : E) : ℝ :=
  ∫ z, f (Real.cos a • w + Real.sin a • z) ∂(stdGaussian E)

/-- The homogeneous Hermite factor `‖u‖^r He_r(⟪z,u⟫/‖u‖)` (for `u = 0` it is `0^r He_r(0)`). -/
def mehlerNHerm (r : ℕ) (z u : E) : ℝ :=
  ‖u‖ ^ r * Polynomial.aeval (inner ℝ z u / ‖u‖) (Polynomial.hermite r)

/-- The splitting map `(σ, y) ↦ σ v + (y - ⟪v,y⟫ v)`. -/
def mehlerNPsi (v : E) (p : ℝ × E) : E := p.1 • v + (p.2 - inner ℝ v p.2 • v)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mehlerNPsi_continuous (v : E) : Continuous (mehlerNPsi v) := by
  unfold mehlerNPsi; fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mehlerNPsi_inner (v ξ : E) (p : ℝ × E) :
    inner ℝ (mehlerNPsi v p) ξ = p.1 * inner ℝ v ξ + inner ℝ p.2 (ξ - inner ℝ v ξ • v) := by
  unfold mehlerNPsi
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_sub_right, inner_smul_right,
    RCLike.conj_to_real, real_inner_comm v p.2]
  ring

theorem mehlerN_split_map {v : E} (hv : ‖v‖ = 1) :
    ((gaussianReal 0 1).prod (stdGaussian E)).map (mehlerNPsi v) = stdGaussian E := by
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_stdGaussian, charFun_apply, integral_map (mehlerNPsi_continuous v).aemeasurable
    (by fun_prop)]
  simp_rw [mehlerNPsi_inner]
  set ξ' : E := ξ - inner ℝ v ξ • v with hξ'
  have h1 : ∀ x : ℝ × E, Complex.exp (↑(x.1 * inner ℝ v ξ + inner ℝ x.2 ξ') * Complex.I)
      = Complex.exp (↑(inner ℝ v ξ) * ↑x.1 * Complex.I) *
        Complex.exp (↑(inner ℝ x.2 ξ') * Complex.I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h1]
  rw [integral_prod_mul (fun σ : ℝ => Complex.exp (↑(inner ℝ v ξ) * ↑σ * Complex.I))
    (fun y : E => Complex.exp (↑(inner ℝ y ξ') * Complex.I)),
    ← charFun_apply_real, ← charFun_apply, charFun_gaussianReal, charFun_stdGaussian]
  have hn : ‖ξ'‖ ^ 2 = ‖ξ‖ ^ 2 - inner ℝ v ξ ^ 2 := by
    rw [hξ', @norm_sub_sq_real, norm_smul, inner_smul_right, hv]
    simp [real_inner_comm v ξ]
    ring
  rw [← Complex.exp_add]
  congr 1
  have hnC : ((‖ξ'‖ : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 - ((inner ℝ v ξ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hn
  simp [hnC]
  ring


theorem mehlerN_split_integral {v : E} (hv : ‖v‖ = 1) {F : E → ℝ}
    (hF : Integrable F (stdGaussian E)) :
    ∫ z, F z ∂(stdGaussian E) =
      ∫ y, ∫ σ, F (mehlerNPsi v (σ, y)) ∂(gaussianReal 0 1) ∂(stdGaussian E) := by
  have hmap := mehlerN_split_map hv
  have hF2 : Integrable F (Measure.map (mehlerNPsi v)
      ((gaussianReal 0 1).prod (stdGaussian E))) := by rw [hmap]; exact hF
  have hF' := (integrable_map_measure (by rw [hmap]; exact hF.aestronglyMeasurable)
    (mehlerNPsi_continuous v).aemeasurable).1 hF2
  calc ∫ z, F z ∂(stdGaussian E)
      = ∫ z, F z ∂(Measure.map (mehlerNPsi v) ((gaussianReal 0 1).prod (stdGaussian E))) := by
        rw [hmap]
    _ = ∫ p, F (mehlerNPsi v p) ∂((gaussianReal 0 1).prod (stdGaussian E)) :=
        integral_map (mehlerNPsi_continuous v).aemeasurable
          (by rw [hmap]; exact hF.aestronglyMeasurable)
    _ = _ := integral_prod_symm (fun p => F (mehlerNPsi v p)) hF'

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_inner_Psi {v : E} (hv : ‖v‖ = 1) (σ : ℝ) (y : E) :
    inner ℝ (mehlerNPsi v (σ, y)) v = σ := by
  unfold mehlerNPsi
  simp only [inner_add_left, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq, hv, real_inner_comm v y]
  ring

theorem mehlerN_map_inner {v : E} (hv : ‖v‖ = 1) :
    (stdGaussian E).map (fun z => inner ℝ z v) = gaussianReal 0 1 := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ v)
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm,
    hv] at h
  have e : (fun z => inner ℝ z v) = ⇑(innerSL ℝ v) := by
    funext z; simp [real_inner_comm]
  rw [e, h]
  simp


/-- The one-dimensional slice of `f` through `cos a • w + sin a • P y` in the direction `v`. -/
def mehlerNSlice (a : ℝ) (f : E → ℝ) (w v y : E) (x : ℝ) : ℝ :=
  f (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) + x • v)

theorem mehlerNSlice_measurable_uncurry (a : ℝ) {f : E → ℝ} (hf : Measurable f) (w v : E) :
    Measurable (fun p : E × ℝ => mehlerNSlice a f w v p.1 p.2) := by
  unfold mehlerNSlice
  exact hf.comp (by fun_prop)

omit [FiniteDimensional ℝ E] in
theorem mehlerNSlice_measurable (a : ℝ) {f : E → ℝ} (hf : Measurable f) (w v y : E) :
    Measurable (mehlerNSlice a f w v y) := by
  unfold mehlerNSlice
  exact hf.comp (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerNSlice_abs_le (a : ℝ) {f : E → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (w v y : E)
    (x : ℝ) : |mehlerNSlice a f w v y x| ≤ C := hC _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_arg (a t lam σ : ℝ) (w v y : E) :
    Real.cos a • (w + t • (lam • v)) + Real.sin a • mehlerNPsi v (σ, y) =
      Real.cos a • w + Real.sin a • (y - inner ℝ v y • v)
        + ((t * lam) * Real.cos a + σ * Real.sin a) • v := by
  unfold mehlerNPsi
  module

theorem mehlerN_H_abs_le (a : ℝ) (g : ℝ → ℝ) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (r : ℕ) (x : ℝ) :
    |mehlerH a g r x| ≤
      C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  have hint : Integrable (fun z => |Polynomial.aeval z (Polynomial.hermite r)|)
      (gaussianReal 0 1) := (mehler_integrable_aeval_hermite_gaussian r).abs
  have hle : ‖∫ z, g (x * Real.cos a + z * Real.sin a)
      * Polynomial.aeval z (Polynomial.hermite r) ∂(gaussianReal 0 1)‖ ≤
      ∫ z, C * |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
    refine norm_integral_le_of_norm_le (hint.const_mul C) (ae_of_all _ fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((hC _)) (abs_nonneg _)
  rw [integral_const_mul] at hle
  rw [mehlerH_eq_integral]
  simpa [Real.norm_eq_abs] using hle


/-- The Hermite-weighted slice average along the line `t ↦ w + t (lam • v)`. -/
def mehlerNPhi (a : ℝ) (f : E → ℝ) (w v : E) (lam : ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  ∫ y, mehlerH a (mehlerNSlice a f w v y) r (t * lam) ∂(stdGaussian E)

theorem mehlerN_integrable_hermite_inner {v : E} (hv : ‖v‖ = 1) (r : ℕ) :
    Integrable (fun z : E => Polynomial.aeval (inner ℝ z v) (Polynomial.hermite r))
      (stdGaussian E) := by
  have h := mehler_integrable_aeval_hermite_gaussian r
  rw [← mehlerN_map_inner hv] at h
  exact (integrable_map_measure h.aestronglyMeasurable
    (by fun_prop : Measurable fun z : E => inner ℝ z v).aemeasurable).1 h

theorem mehlerNPhi_eq (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    {v : E} (hv : ‖v‖ = 1) (w : E) (lam : ℝ) (r : ℕ) (t : ℝ) :
    mehlerNPhi a f w v lam r t = ∫ z, f (Real.cos a • (w + t • (lam • v)) + Real.sin a • z)
      * Polynomial.aeval (inner ℝ z v) (Polynomial.hermite r) ∂(stdGaussian E) := by
  have hint : Integrable (fun z => f (Real.cos a • (w + t • (lam • v)) + Real.sin a • z)
      * Polynomial.aeval (inner ℝ z v) (Polynomial.hermite r)) (stdGaussian E) :=
    (mehlerN_integrable_hermite_inner hv r).bdd_mul (c := C)
      (hf.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun z => by simpa using hC _)
  rw [mehlerN_split_integral hv hint]
  unfold mehlerNPhi
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [mehlerH_eq_integral]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only [mehlerN_inner_Psi hv, mehlerN_arg]
  rfl


theorem mehlerN_H_stronglyMeasurable (a : ℝ) {f : E → ℝ} (hf : Measurable f) (w v : E)
    (k : ℕ) (τ : ℝ) :
    StronglyMeasurable (fun y => mehlerH a (mehlerNSlice a f w v y) k τ) := by
  have hm : Measurable (fun p : E × ℝ => mehlerNSlice a f w v p.1
      (τ * Real.cos a + p.2 * Real.sin a) * Polynomial.aeval p.2 (Polynomial.hermite k)) := by
    have hpair : Measurable (fun p : E × ℝ => (p.1, τ * Real.cos a + p.2 * Real.sin a)) := by
      fun_prop
    refine Measurable.mul ((mehlerNSlice_measurable_uncurry a hf w v).comp hpair) ?_
    exact ((Polynomial.hermite k).continuous_aeval (A := ℝ)).measurable.comp measurable_snd
  have := hm.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)
  convert this using 1
  funext y
  rw [mehlerH_eq_integral]

theorem mehlerNPhi_hasDerivAt (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w v : E) (lam : ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (mehlerNPhi a f w v lam r)
      (lam * (Real.cos a / Real.sin a) * mehlerNPhi a f w v lam (r + 1) t) t := by
  set K : ℝ := ∫ z, |Polynomial.aeval z (Polynomial.hermite (r + 1))| ∂(gaussianReal 0 1) with hK
  have hbd : ∀ (y : E) (x : ℝ), |mehlerH a (mehlerNSlice a f w v y) (r + 1) x| ≤ C * K :=
    fun y x => mehlerN_H_abs_le a _ (mehlerNSlice_abs_le a hC w v y) (r + 1) x
  have hbd0 : ∀ (y : E) (x : ℝ), |mehlerH a (mehlerNSlice a f w v y) r x| ≤
      C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) :=
    fun y x => mehlerN_H_abs_le a _ (mehlerNSlice_abs_le a hC w v y) r x
  have hmeas : ∀ (k : ℕ) (τ : ℝ), AEStronglyMeasurable
      (fun y => mehlerH a (mehlerNSlice a f w v y) k τ) (stdGaussian E) := fun k τ =>
    (mehlerN_H_stronglyMeasurable a hf w v k τ).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := stdGaussian E)
    (F := fun s y => mehlerH a (mehlerNSlice a f w v y) r (s * lam))
    (F' := fun s y => lam * (Real.cos a / Real.sin a *
      mehlerH a (mehlerNSlice a f w v y) (r + 1) (s * lam))) (x₀ := t)
    (s := Set.univ) (bound := fun _ => |lam| * (|Real.cos a / Real.sin a| * (C * K)))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun s => hmeas r (s * lam))
    (Integrable.of_bound (hmeas r (t * lam)) _ (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hbd0 y _))
    (((hmeas (r + 1) (t * lam)).const_mul _).const_mul _)
    (ae_of_all _ fun y s _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbd y _) (abs_nonneg _))
        (abs_nonneg _))
    (integrable_const _)
    (ae_of_all _ fun y s _ => by
      have h1 := mehlerH_hasDerivAt a (mehlerNSlice a f w v y)
        (mehlerNSlice_measurable a hf w v y) C (mehlerNSlice_abs_le a hC w v y) hs r (s * lam)
      have h2 : HasDerivAt (fun s : ℝ => s * lam) lam s := by
        simpa using (hasDerivAt_id s).mul_const lam
      have h3 := HasDerivAt.scomp s (by simpa using h1) h2
      refine h3.congr_deriv ?_
      simp only [smul_eq_mul])
  have h4 := h.2
  rw [integral_const_mul, integral_const_mul] at h4
  unfold mehlerNPhi
  refine h4.congr_deriv ?_
  ring


theorem mehlerNPhi_abs_le (a : ℝ) {f : E → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (w v : E)
    (lam : ℝ) (r : ℕ) (t : ℝ) :
    |mehlerNPhi a f w v lam r t| ≤
      C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  have := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun y => mehlerH a (mehlerNSlice a f w v y) r (t * lam))
    (C := C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1))
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact mehlerN_H_abs_le a _ (mehlerNSlice_abs_le a hC w v y) r _)
  simpa [mehlerNPhi, Measure.real] using this

theorem mehlerNPhi_zero (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C)
    {v : E} (hv : ‖v‖ = 1) (w : E) (lam t : ℝ) :
    mehlerNPhi a f w v lam 0 t = mehlerN a f (w + t • (lam • v)) := by
  rw [mehlerNPhi_eq a hf hC hv]
  simp [mehlerN]

theorem mehlerN_iteratedDeriv_unit (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) {v : E} (hv : ‖v‖ = 1) (w : E) (lam : ℝ)
    (r : ℕ) :
    iteratedDeriv r (fun t : ℝ => mehlerN a f (w + t • (lam • v))) =
      fun t => (lam * (Real.cos a / Real.sin a)) ^ r * mehlerNPhi a f w v lam r t := by
  induction r with
  | zero =>
    funext t
    simp [mehlerNPhi_zero a hf hC hv]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (((mehlerNPhi_hasDerivAt a hf hC hs w v lam r t).const_mul
      ((lam * (Real.cos a / Real.sin a)) ^ r)).deriv).trans (by ring)


theorem mehlerN_iteratedDeriv_line_at (a : ℝ) {f : E → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) (t : ℝ) :
    iteratedDeriv r (fun s : ℝ => mehlerN a f (w + s • u)) t =
      (Real.cos a / Real.sin a) ^ r *
        ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) * mehlerNHerm r z u
          ∂(stdGaussian E) := by
  obtain ⟨C, hC⟩ := hb
  by_cases hu : u = 0
  · subst hu
    simp only [smul_zero, add_zero, iteratedDeriv_const, mehlerNHerm, norm_zero, inner_zero_right,
      zero_div]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [mehlerN]
    · simp [hr.ne']
  · set lam : ℝ := ‖u‖ with hlam
    set v : E := ‖u‖⁻¹ • u with hvdef
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have huv : lam • v = u := by
      rw [hvdef, hlam, smul_smul, mul_inv_cancel₀ hu', one_smul]
    have h1 := congrFun (mehlerN_iteratedDeriv_unit a hf hC hs hv w lam r) t
    rw [huv] at h1
    rw [h1, mehlerNPhi_eq a hf hC hv, huv, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have hinner : inner ℝ z v = inner ℝ z u / ‖u‖ := by
      rw [hvdef, inner_smul_right, div_eq_inv_mul]
    simp only [mehlerNHerm, hinner, hlam]
    rw [mul_pow]
    ring

theorem mehlerN_iteratedDeriv_line (a : ℝ) {f : E → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) :
    iteratedDeriv r (fun t : ℝ => mehlerN a f (w + t • u)) 0 =
      (Real.cos a / Real.sin a) ^ r *
        ∫ z, f (Real.cos a • w + Real.sin a • z) * mehlerNHerm r z u ∂(stdGaussian E) := by
  simpa using mehlerN_iteratedDeriv_line_at a hf hb hs r w u 0


theorem mehlerN_abs_le (a : ℝ) {f : E → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (w : E) :
    |mehlerN a f w| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun z => f (Real.cos a • w + Real.sin a • z)) (C := C)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  simpa [mehlerN, Measure.real] using this

theorem mehlerN_iteratedDeriv_line_bound_at (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) (t : ℝ) :
    |iteratedDeriv r (fun s : ℝ => mehlerN a f (w + s • u)) t| ≤
      C * |Real.cos a / Real.sin a| ^ r * ‖u‖ ^ r *
        ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hu : u = 0
  · subst hu
    simp only [smul_zero, add_zero, iteratedDeriv_const, norm_zero]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using mehlerN_abs_le a hC w
    · have hKnn : 0 ≤ ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) :=
        integral_nonneg fun z => abs_nonneg _
      simp [hr.ne']
  · set lam : ℝ := ‖u‖ with hlam
    set v : E := ‖u‖⁻¹ • u with hvdef
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have huv : lam • v = u := by
      rw [hvdef, hlam, smul_smul, mul_inv_cancel₀ hu', one_smul]
    have h1 := congrFun (mehlerN_iteratedDeriv_unit a hf hC hs hv w lam r) t
    rw [huv] at h1
    rw [h1, abs_mul, abs_pow, abs_mul]
    have h2 := mehlerNPhi_abs_le a hC w v lam r t
    have habs : |lam| = ‖u‖ := by rw [hlam, abs_norm]
    rw [habs]
    calc (‖u‖ * |Real.cos a / Real.sin a|) ^ r * |mehlerNPhi a f w v lam r t|
        ≤ (‖u‖ * |Real.cos a / Real.sin a|) ^ r *
          (C * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1)) := by
          gcongr
      _ = _ := by rw [mul_pow]; ring

theorem mehlerN_iteratedDeriv_line_bound (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) :
    |iteratedDeriv r (fun t : ℝ => mehlerN a f (w + t • u)) 0| ≤
      C * |Real.cos a / Real.sin a| ^ r * ‖u‖ ^ r *
        ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) :=
  mehlerN_iteratedDeriv_line_bound_at a hf hC hs r w u 0


/-! ### First-order calculus: Lipschitz bound and Fréchet differentiability -/

theorem mehlerN_hasDerivAt_line (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => mehlerN a f (w + s • u))
      (Real.cos a / Real.sin a *
        ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) * inner ℝ z u ∂(stdGaussian E)) t := by
  by_cases hu : u = 0
  · subst hu
    simp only [smul_zero, add_zero, inner_zero_right, mul_zero, integral_zero]
    exact hasDerivAt_const t _
  · set lam : ℝ := ‖u‖ with hlam
    set v : E := ‖u‖⁻¹ • u with hvdef
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have huv : lam • v = u := by
      rw [hvdef, hlam, smul_smul, mul_inv_cancel₀ hu', one_smul]
    have h1 := mehlerNPhi_hasDerivAt a hf hC hs w v lam 0 t
    have h0 : mehlerNPhi a f w v lam 0 = fun s : ℝ => mehlerN a f (w + s • u) := by
      funext s
      rw [mehlerNPhi_zero a hf hC hv, huv]
    rw [h0] at h1
    refine h1.congr_deriv ?_
    rw [mehlerNPhi_eq a hf hC hv, huv]
    have : ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) *
        Polynomial.aeval (inner ℝ z v) (Polynomial.hermite (0 + 1)) ∂(stdGaussian E)
        = ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) * (inner ℝ z u / lam)
            ∂(stdGaussian E) := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      have hinner : inner ℝ z v = inner ℝ z u / ‖u‖ := by
        rw [hvdef, inner_smul_right, div_eq_inv_mul]
      simp [hinner, hlam]
    rw [this]
    have : ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) * (inner ℝ z u / lam)
            ∂(stdGaussian E) = lam⁻¹ * ∫ z, f (Real.cos a • (w + t • u) + Real.sin a • z) *
              inner ℝ z u ∂(stdGaussian E) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      ring
    rw [this]
    have hl : lam ≠ 0 := hu'
    field_simp


/-- The Lipschitz constant of `mehlerN a f` for `|f| ≤ C`. -/
def mehlerNLip (a C : ℝ) : NNReal :=
  Real.toNNReal (C * |Real.cos a / Real.sin a| *
    ∫ z, |Polynomial.aeval z (Polynomial.hermite 1)| ∂(gaussianReal 0 1))

theorem mehlerN_lipschitz (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) :
    LipschitzWith (mehlerNLip a C) (mehlerN a f) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hK : 0 ≤ ∫ z, |Polynomial.aeval z (Polynomial.hermite 1)| ∂(gaussianReal 0 1) :=
    integral_nonneg fun z => abs_nonneg _
  have hcoe : ((mehlerNLip a C : NNReal) : ℝ) = C * |Real.cos a / Real.sin a| *
      ∫ z, |Polynomial.aeval z (Polynomial.hermite 1)| ∂(gaussianReal 0 1) := by
    unfold mehlerNLip
    exact Real.coe_toNNReal _ (by positivity)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, hcoe, dist_comm x y, dist_eq_norm]
  set u : E := y - x with hu
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => mehlerN a f (x + s • u))
    (f' := fun s : ℝ => iteratedDeriv 1 (fun s : ℝ => mehlerN a f (x + s • u)) s)
    (C := C * |Real.cos a / Real.sin a| * ‖u‖ *
      ∫ z, |Polynomial.aeval z (Polynomial.hermite 1)| ∂(gaussianReal 0 1))
    (fun s _ => by
      have := mehlerN_hasDerivAt_line a hf hC hs x u s
      rw [iteratedDeriv_one, this.deriv]
      exact this.hasDerivWithinAt)
    (fun s _ => by
      have := mehlerN_iteratedDeriv_line_bound_at a hf hC hs 1 x u s
      rw [Real.norm_eq_abs]
      simpa using this)
    (Set.mem_univ 0) (Set.mem_univ 1)
  simp only [one_smul, zero_smul, add_zero, Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
  have : x + u = y := by rw [hu]; abel
  rw [this] at h
  calc |mehlerN a f x - mehlerN a f y| = |mehlerN a f y - mehlerN a f x| := abs_sub_comm _ _
    _ ≤ _ := h
    _ = _ := by ring


/-- The Fréchet derivative of `mehlerN a f` at `w`:
`u ↦ cot a ∫ f (cos a • w + sin a • z) ⟪z, u⟫ dγ(z)`. -/
def mehlerNGrad (a : ℝ) (f : E → ℝ) (w : E) : StrongDual ℝ E :=
  (Real.cos a / Real.sin a) •
    ∫ z, f (Real.cos a • w + Real.sin a • z) • innerSL ℝ z ∂(stdGaussian E)

theorem mehlerN_integrable_innerSL : Integrable (fun z : E => innerSL ℝ z) (stdGaussian E) :=
  (innerSL ℝ (E := E)).integrable_comp IsGaussian.integrable_id

theorem mehlerN_integrable_grad (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (w : E) :
    Integrable (fun z : E => f (Real.cos a • w + Real.sin a • z) • innerSL ℝ z)
      (stdGaussian E) :=
  mehlerN_integrable_innerSL.bdd_smul C (hf.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using hC _)

theorem mehlerNGrad_apply (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (w u : E) :
    mehlerNGrad a f w u = Real.cos a / Real.sin a *
      ∫ z, f (Real.cos a • w + Real.sin a • z) * inner ℝ z u ∂(stdGaussian E) := by
  unfold mehlerNGrad
  rw [smul_apply, ContinuousLinearMap.integral_apply
    (mehlerN_integrable_grad a hf hC w)]
  simp [smul_eq_mul]

theorem mehlerN_hasFDerivAt (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w : E) :
    HasFDerivAt (mehlerN a f) (mehlerNGrad a f w) w := by
  refine (mehlerN_lipschitz a hf hC hs).hasFDerivAt_of_hasLineDerivAt_of_closure
    (s := Set.univ) (by simp) fun u _ => ?_
  have := mehlerN_hasDerivAt_line a hf hC hs w u 0
  rw [mehlerNGrad_apply a hf hC]
  simpa [HasLineDerivAt] using this


/-! ### The semigroup property -/

theorem mehlerN_comp_map (α β : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map (fun p : E × E => α • p.1 + β • p.2)
      = (stdGaussian E).map (fun z => Real.sqrt (α ^ 2 + β ^ 2) • z) := by
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_map_smul, charFun_stdGaussian, charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ x : E × E, Complex.exp (↑(inner ℝ (α • x.1 + β • x.2) ξ) * Complex.I)
      = Complex.exp (↑(inner ℝ x.1 (α • ξ)) * Complex.I) *
        Complex.exp (↑(inner ℝ x.2 (β • ξ)) * Complex.I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_smul_right,
      inner_smul_right]
    push_cast
    ring
  simp_rw [h1]
  rw [integral_prod_mul (fun x : E => Complex.exp (↑(inner ℝ x (α • ξ)) * Complex.I))
    (fun x : E => Complex.exp (↑(inner ℝ x (β • ξ)) * Complex.I)),
    ← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have hreal : ‖α • ξ‖ ^ 2 + ‖β • ξ‖ ^ 2 = ‖Real.sqrt (α ^ 2 + β ^ 2) • ξ‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hC : ((‖α • ξ‖ : ℝ) : ℂ) ^ 2 + ((‖β • ξ‖ : ℝ) : ℂ) ^ 2
      = ((‖Real.sqrt (α ^ 2 + β ^ 2) • ξ‖ : ℝ) : ℂ) ^ 2 := by exact_mod_cast hreal
  linear_combination (-1 / 2 : ℂ) * hC


theorem mehlerN_comp (a a' a'' : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a)
    (hcos : Real.cos a = Real.cos a' * Real.cos a'') (w : E) :
    mehlerN a f w = mehlerN a' (mehlerN a'' f) w := by
  have hsq : (Real.cos a'' * Real.sin a') ^ 2 + (Real.sin a'') ^ 2 = Real.sin a ^ 2 := by
    have e1 := Real.sin_sq_add_cos_sq a
    have e2 := Real.sin_sq_add_cos_sq a'
    have e3 := Real.sin_sq_add_cos_sq a''
    linear_combination (Real.cos a'') ^ 2 * e2 + e3 - e1
      + (Real.cos a + Real.cos a' * Real.cos a'') * hcos
  have hsqrt : Real.sqrt ((Real.cos a'' * Real.sin a') ^ 2 + (Real.sin a'') ^ 2)
      = Real.sin a := by rw [hsq]; exact Real.sqrt_sq hs.le
  have hmeasf : Measurable (fun p : E × E => f (Real.cos a • w +
      ((Real.cos a'' * Real.sin a') • p.1 + (Real.sin a'') • p.2))) :=
    hf.comp (by fun_prop)
  have hint : Integrable (fun p : E × E => f (Real.cos a • w +
      ((Real.cos a'' * Real.sin a') • p.1 + (Real.sin a'') • p.2)))
      ((stdGaussian E).prod (stdGaussian E)) :=
    Integrable.of_bound hmeasf.aestronglyMeasurable C (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hC _)
  have hstep : mehlerN a' (mehlerN a'' f) w = ∫ z, ∫ z', f (Real.cos a • w +
      ((Real.cos a'' * Real.sin a') • z + (Real.sin a'') • z')) ∂(stdGaussian E)
        ∂(stdGaussian E) := by
    unfold mehlerN
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    refine integral_congr_ae (ae_of_all _ fun z' => ?_)
    dsimp only
    congr 1
    rw [hcos]
    module
  rw [hstep, integral_integral (f := fun z z' => f (Real.cos a • w +
      ((Real.cos a'' * Real.sin a') • z + (Real.sin a'') • z'))) hint]
  have hmeasq : Measurable (fun q : E => f (Real.cos a • w + q)) := hf.comp (by fun_prop)
  have h2 := integral_map (μ := (stdGaussian E).prod (stdGaussian E))
    (φ := fun p : E × E => (Real.cos a'' * Real.sin a') • p.1 + (Real.sin a'') • p.2)
    (by fun_prop) (f := fun q : E => f (Real.cos a • w + q)) hmeasq.aestronglyMeasurable
  rw [← h2, mehlerN_comp_map, integral_map (by fun_prop) hmeasq.aestronglyMeasurable, hsqrt]
  rfl


theorem mehlerN_aestronglyMeasurable_fderiv (a : ℝ) (g : E → ℝ) (w : E) :
    AEStronglyMeasurable
      (fun z : E => Real.cos a • fderiv ℝ g (Real.cos a • w + Real.sin a • z)) (stdGaussian E) := by
  have hm0 : Measurable (fun z : E => fderiv ℝ g (Real.cos a • w + Real.sin a • z)) :=
    (measurable_fderiv ℝ g).comp (by fun_prop :
      Continuous fun z : E => Real.cos a • w + Real.sin a • z).measurable
  exact (hm0.const_smul (Real.cos a)).aestronglyMeasurable

/-- Differentiation under the integral sign for a differentiable function with bounded
derivative. -/
theorem mehlerN_hasFDerivAt_of_fderiv_bdd (a : ℝ) {g : E → ℝ} (hg : Differentiable ℝ g)
    {C K : ℝ} (hC : ∀ x, |g x| ≤ C) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K) (w : E) :
    HasFDerivAt (mehlerN a g)
      (∫ z, Real.cos a • fderiv ℝ g (Real.cos a • w + Real.sin a • z) ∂(stdGaussian E)) w := by
  have hgc : Continuous g := hg.continuous
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := stdGaussian E) (𝕜 := ℝ)
    (F := fun w' z => g (Real.cos a • w' + Real.sin a • z))
    (F' := fun w' z => Real.cos a • fderiv ℝ g (Real.cos a • w' + Real.sin a • z))
    (x₀ := w) (s := Set.univ) (bound := fun _ => |Real.cos a| * K) Filter.univ_mem
    (Filter.Eventually.of_forall fun w' => (hgc.comp (by fun_prop)).aestronglyMeasurable)
    (Integrable.of_bound (hgc.comp (by fun_prop)).aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa using hC _))
    (mehlerN_aestronglyMeasurable_fderiv a g w)
    (ae_of_all _ fun z w' _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))
    (integrable_const _)
    (ae_of_all _ fun z w' _ => by
      have h2 : HasFDerivAt (fun w' : E => Real.cos a • w' + Real.sin a • z)
          (Real.cos a • ContinuousLinearMap.id ℝ E) w' := by
        simpa using ((hasFDerivAt_id w').const_smul (Real.cos a)).add_const (Real.sin a • z)
      have h3 := (hg (Real.cos a • w' + Real.sin a • z)).hasFDerivAt.comp w' h2
      refine h3.congr_fderiv ?_
      ext y
      simp)
  exact h


theorem mehlerN_fderiv_apply_of_fderiv_bdd (a : ℝ) {g : E → ℝ} (hg : Differentiable ℝ g)
    {C K : ℝ} (hC : ∀ x, |g x| ≤ C) (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K) (w y : E) :
    fderiv ℝ (mehlerN a g) w y = Real.cos a * mehlerN a (fun x => fderiv ℝ g x y) w := by
  rw [(mehlerN_hasFDerivAt_of_fderiv_bdd a hg hC hK w).fderiv,
    ContinuousLinearMap.integral_apply (Integrable.of_bound
      (mehlerN_aestronglyMeasurable_fderiv a g w) (|Real.cos a| * K)
      (ae_of_all _ fun z => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hK _) (abs_nonneg _))) y]
  simp [mehlerN, integral_const_mul]


theorem mehlerN_exists_split (a : ℝ) (hs : 0 < Real.sin a) :
    ∃ a' a'' : ℝ, 0 < Real.sin a' ∧ 0 < Real.sin a'' ∧
      Real.cos a = Real.cos a' * Real.cos a'' := by
  have hc : |Real.cos a| < 1 := by
    have h1 := Real.sin_sq_add_cos_sq a
    have h2 : Real.cos a ^ 2 < 1 := by nlinarith [sq_pos_of_pos hs]
    exact abs_lt.2 ⟨by nlinarith [sq_nonneg (Real.cos a + 1)],
      by nlinarith [sq_nonneg (Real.cos a - 1)]⟩
  set ρ : ℝ := (1 + |Real.cos a|) / 2 with hρ
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : |Real.cos a| < ρ := by rw [hρ]; linarith
  have hρpos : 0 < ρ := lt_of_le_of_lt (abs_nonneg _) hρ0
  have hq : |Real.cos a / ρ| < 1 := by
    rw [abs_div, abs_of_pos hρpos, div_lt_one hρpos]; exact hρ0
  have hsin : ∀ x : ℝ, |x| < 1 → 0 < Real.sin (Real.arccos x) := by
    intro x hx
    rw [Real.sin_arccos]
    apply Real.sqrt_pos.2
    nlinarith [abs_lt.1 hx, sq_abs x]
  refine ⟨Real.arccos (Real.cos a / ρ), Real.arccos ρ, hsin _ hq, hsin ρ ?_, ?_⟩
  · rw [abs_of_pos hρpos]; exact hρ1
  · rw [Real.cos_arccos (abs_lt.1 hq).1.le (abs_lt.1 hq).2.le,
      Real.cos_arccos (by linarith) hρ1.le]
    field_simp

theorem mehlerN_contDiff_nat (k : ℕ) : ∀ (a : ℝ) (f : E → ℝ), Measurable f →
    (∃ C, ∀ x, |f x| ≤ C) → 0 < Real.sin a → ContDiff ℝ k (mehlerN a f) := by
  induction k with
  | zero =>
    intro a f hf ⟨C, hC⟩ hs
    exact contDiff_zero.2 (mehlerN_lipschitz a hf hC hs).continuous
  | succ k ih =>
    intro a f hf ⟨C, hC⟩ hs
    obtain ⟨a', a'', hs', hs'', hcos⟩ := mehlerN_exists_split a hs
    have hgd : Differentiable ℝ (mehlerN a'' f) := fun w =>
      (mehlerN_hasFDerivAt a'' hf hC hs'' w).differentiableAt
    have hgC : ∀ x, |mehlerN a'' f x| ≤ C := fun x => mehlerN_abs_le a'' hC x
    have hgK : ∀ x, ‖fderiv ℝ (mehlerN a'' f) x‖ ≤ ((mehlerNLip a'' C : NNReal) : ℝ) :=
      fun x => norm_fderiv_le_of_lipschitz ℝ (mehlerN_lipschitz a'' hf hC hs'')
    have heq : mehlerN a f = mehlerN a' (mehlerN a'' f) :=
      funext (mehlerN_comp a a' a'' hf hC hs hcos)
    rw [heq]
    have : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [this, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun w => (mehlerN_hasFDerivAt_of_fderiv_bdd a' hgd hgC hgK w).differentiableAt,
      fun h => absurd h (by simp), fun y => ?_⟩
    have hfun : (fun w => fderiv ℝ (mehlerN a' (mehlerN a'' f)) w y) =
        fun w => Real.cos a' * mehlerN a' (fun x => fderiv ℝ (mehlerN a'' f) x y) w := by
      funext w
      exact mehlerN_fderiv_apply_of_fderiv_bdd a' hgd hgC hgK w y
    rw [hfun]
    refine contDiff_const.mul (ih a' (fun x => fderiv ℝ (mehlerN a'' f) x y) ?_
      ⟨((mehlerNLip a'' C : NNReal) : ℝ) * ‖y‖, fun x => ?_⟩ hs')
    · exact measurable_fderiv_apply_const ℝ (mehlerN a'' f) y
    · rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ y).trans
        (mul_le_mul_of_nonneg_right (hgK x) (norm_nonneg y))


/-- **Smoothness**: for a bounded Borel `f` and `0 < sin a`, `mehlerN a f` is `C^∞`
(`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`; the bare `⊤ : WithTop ℕ∞` would mean analytic). -/
theorem mehlerN_contDiff (a : ℝ) {f : E → ℝ} (hf : Measurable f) (hb : ∃ C, ∀ x, |f x| ≤ C)
    (hs : 0 < Real.sin a) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mehlerN a f) :=
  contDiff_infty.2 fun k => mehlerN_contDiff_nat k a f hf hb hs

/-! ### The bridge between line derivatives and iterated Fréchet derivatives -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_iteratedDeriv_line_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {n : ℕ} (hg : ContDiff ℝ n g) (x u : E) :
    iteratedDeriv n (fun t : ℝ => g (x + t • u)) 0 = iteratedFDeriv ℝ n g x (fun _ => u) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) u with hL
  have hG : ContDiff ℝ n (fun z : E => g (x + z)) := hg.comp (contDiff_const.add contDiff_id)
  have h1 : (fun t : ℝ => g (x + t • u)) = (fun z : E => g (x + z)) ∘ L := by
    funext t; simp [hL]
  have h2 := ContinuousLinearMap.iteratedFDeriv_comp_right L hG (0 : ℝ) (i := n) le_rfl
  rw [h1, iteratedDeriv_eq_iteratedFDeriv, h2]
  simp [hL, iteratedFDeriv_comp_add_left]

/-- **The bridge of the brief**: for `f` bounded Borel and `0 < sin a`,
`iteratedFDeriv ℝ 3 (mehlerN a f) w ![u, u, u]` is the third derivative along the line. -/
theorem mehlerN_iteratedFDeriv_three (a : ℝ) {f : E → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w u : E) :
    iteratedFDeriv ℝ 3 (mehlerN a f) w ![u, u, u] =
      iteratedDeriv 3 (fun t : ℝ => mehlerN a f (w + t • u)) 0 := by
  have h := mehlerN_iteratedDeriv_line_eq
    ((mehlerN_contDiff_nat 3 a f hf hb hs)) w u
  rw [h]
  congr 1
  funext i
  fin_cases i <;> rfl


/-! ### The `C²_b` form -/

/-- The second directional derivative `D² f (x) [u, u]`. -/
def mehlerND2 (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => f (x + t • u)) 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerND2_eq {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x u : E) :
    mehlerND2 f x u = iteratedFDeriv ℝ 2 f x (fun _ => u) :=
  mehlerN_iteratedDeriv_line_eq (n := 2) (by exact_mod_cast hf) x u

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerND2_eq_fderiv {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x u : E) :
    mehlerND2 f x u = fderiv ℝ (fderiv ℝ f) x u u := by
  rw [mehlerND2_eq hf, iteratedFDeriv_two_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerND2_smul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) (lam : ℝ) :
    mehlerND2 f x (lam • v) = lam ^ 2 * mehlerND2 f x v := by
  rw [mehlerND2_eq hf, mehlerND2_eq hf]
  have := (iteratedFDeriv ℝ 2 f x).map_smul_univ (fun _ : Fin 2 => lam) (fun _ => v)
  rw [this]
  simp [sq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerND2_continuous {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u : E) :
    Continuous (fun x => mehlerND2 f x u) := by
  have : (fun x => mehlerND2 f x u) = fun x => fderiv ℝ (fderiv ℝ f) x u u := by
    funext x; exact mehlerND2_eq_fderiv hf x u
  rw [this]
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) := h1.continuous_fderiv one_ne_zero
  exact (h2.clm_apply continuous_const).clm_apply continuous_const


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_slice_hasDerivAt {f : E → ℝ} (hf : ContDiff ℝ 2 f) (q v : E) (x : ℝ) :
    HasDerivAt (fun x : ℝ => f (q + x • v)) (fderiv ℝ f (q + x • v) v) x := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hp : HasDerivAt (fun x : ℝ => q + x • v) v x := by
    simpa using ((hasDerivAt_id x).smul_const v).const_add q
  exact (hd (q + x • v)).hasFDerivAt.comp_hasDerivAt x hp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_slice_deriv2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (q v : E) (x : ℝ) :
    deriv (deriv (fun x : ℝ => f (q + x • v))) x = mehlerND2 f (q + x • v) v := by
  have e : deriv (fun x : ℝ => f (q + x • v)) = fun x => fderiv ℝ f (q + x • v) v :=
    funext fun x => (mehlerN_slice_hasDerivAt hf q v x).deriv
  rw [e, mehlerND2_eq_fderiv hf]
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ f) := h1.differentiable one_ne_zero
  have hp : HasDerivAt (fun x : ℝ => q + x • v) v x := by
    simpa using ((hasDerivAt_id x).smul_const v).const_add q
  have h2 := (hd (q + x • v)).hasFDerivAt.comp_hasDerivAt x hp
  have h3 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt x h2
  exact h3.deriv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerN_slice_bounds {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C0 C1 C2 : ℝ}
    (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C2) {v : E} (hv : ‖v‖ = 1) (q : E) :
    ContDiff ℝ 2 (fun x : ℝ => f (q + x • v)) ∧
      (∃ C, ∀ x : ℝ, |f (q + x • v)| ≤ C) ∧
      (∃ C, ∀ x : ℝ, |deriv (fun x : ℝ => f (q + x • v)) x| ≤ C) ∧
      (∃ C, ∀ x : ℝ, |deriv (deriv (fun x : ℝ => f (q + x • v))) x| ≤ C) := by
  refine ⟨hf.comp (by fun_prop), ⟨C0, fun x => h0 _⟩, ⟨C1, fun x => ?_⟩, ⟨C2, fun x => ?_⟩⟩
  · rw [(mehlerN_slice_hasDerivAt hf q v x).deriv, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ f (q + x • v) v‖ ≤ ‖fderiv ℝ f (q + x • v)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C1 := by rw [hv, mul_one]; exact h1 _
  · rw [mehlerN_slice_deriv2 hf, mehlerND2_eq hf, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 f (q + x • v) (fun _ => v)‖
        ≤ ‖iteratedFDeriv ℝ 2 f (q + x • v)‖ * ∏ _i : Fin 2, ‖v‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C2 := by simp [hv, h2 (q + x • v)]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerND2_abs_le {f : E → ℝ} (hf : ContDiff ℝ 2 f) {C2 : ℝ}
    (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C2) {v : E} (hv : ‖v‖ = 1) (x : E) :
    |mehlerND2 f x v| ≤ C2 := by
  rw [mehlerND2_eq hf, ← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ 2 f x (fun _ => v)‖
      ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ∏ _i : Fin 2, ‖v‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C2 := by simp [hv, h2 x]

theorem mehlerN_iteratedDeriv_three_C2b_unit (a : ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {C0 C1 C2 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C2) (hs : 0 < Real.sin a) {v : E} (hv : ‖v‖ = 1)
    (w : E) (lam : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => mehlerN a f (w + t • (lam • v))) 0 =
      lam ^ 3 * (Real.cos a ^ 3 / Real.sin a *
        ∫ z, inner ℝ z v * mehlerND2 f (Real.cos a • w + Real.sin a • z) v
          ∂(stdGaussian E)) := by
  have hfm : Measurable f := hf.continuous.measurable
  have hmain : ∀ y : E, (lam * (Real.cos a / Real.sin a)) ^ 3 *
      mehlerH a (mehlerNSlice a f w v y) 3 (0 * lam) =
      lam ^ 3 * (Real.cos a ^ 3 / Real.sin a * ∫ σ, σ * mehlerND2 f
        (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) +
          ((0 * lam) * Real.cos a + σ * Real.sin a) • v) v ∂(gaussianReal 0 1)) := by
    intro y
    obtain ⟨hcd, hb0, hb1, hb2⟩ := mehlerN_slice_bounds hf h0 h1 h2 hv
      (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v))
    have e1 := mehlerSmooth_iteratedDeriv_three_C2b a (mehlerNSlice a f w v y) hcd hb0 hb1 hb2
      hs (0 * lam)
    have e2 := mehlerSmooth_iteratedDeriv_eq_mehlerH a (mehlerNSlice a f w v y)
      (mehlerNSlice_measurable a hfm w v y) C0 (fun x => h0 _) hs 3
    rw [e2] at e1
    simp only at e1
    have e3 : ∀ σ : ℝ, deriv (deriv (mehlerNSlice a f w v y))
        ((0 * lam) * Real.cos a + σ * Real.sin a)
        = mehlerND2 f (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) +
          ((0 * lam) * Real.cos a + σ * Real.sin a) • v) v := fun σ =>
      mehlerN_slice_deriv2 hf _ v _
    simp_rw [e3] at e1
    rw [mul_pow, mul_assoc, e1]
  have hI : Integrable (fun z : E => inner ℝ z v) (stdGaussian E) := by
    simpa using mehlerN_integrable_hermite_inner hv 1
  have hFint : Integrable (fun z : E => inner ℝ z v *
      mehlerND2 f (Real.cos a • w + Real.sin a • z) v) (stdGaussian E) := by
    have := hI.bdd_mul (c := C2)
      (f := fun z : E => mehlerND2 f (Real.cos a • w + Real.sin a • z) v)
      ((mehlerND2_continuous hf v).comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact mehlerND2_abs_le hf h2 hv _)
    exact this.congr (ae_of_all _ fun z => by simp [mul_comm])
  have h1' := congrFun (mehlerN_iteratedDeriv_unit a hfm (C := C0) h0 hs hv w lam 3) 0
  rw [h1']
  unfold mehlerNPhi
  rw [← integral_const_mul]
  calc ∫ y, (lam * (Real.cos a / Real.sin a)) ^ 3 *
        mehlerH a (mehlerNSlice a f w v y) 3 (0 * lam) ∂(stdGaussian E)
      = ∫ y, lam ^ 3 * (Real.cos a ^ 3 / Real.sin a * ∫ σ, σ * mehlerND2 f
        (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) +
          ((0 * lam) * Real.cos a + σ * Real.sin a) • v) v ∂(gaussianReal 0 1))
          ∂(stdGaussian E) := integral_congr_ae (ae_of_all _ hmain)
    _ = lam ^ 3 * (Real.cos a ^ 3 / Real.sin a * ∫ y, ∫ σ, σ * mehlerND2 f
        (Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) +
          ((0 * lam) * Real.cos a + σ * Real.sin a) • v) v ∂(gaussianReal 0 1)
          ∂(stdGaussian E)) := by
        rw [integral_const_mul, integral_const_mul]
    _ = _ := by
        congr 2
        rw [mehlerN_split_integral hv hFint]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        have harg : Real.cos a • w + Real.sin a • mehlerNPsi v (σ, y) =
            Real.cos a • w + Real.sin a • (y - inner ℝ v y • v) +
              ((0 * lam) * Real.cos a + σ * Real.sin a) • v := by
          unfold mehlerNPsi
          module
        simp only [mehlerN_inner_Psi hv, harg]


/-- **The `C²_b` form of the third derivative** (Raic (2.7)), in direction `u`:
`d³/dt³ U_a f (w + t u)|_{t=0} = cos³a / sin a · ∫ ⟪z,u⟫ D² f(cos a w + sin a z)[u,u] dγ(z)`. -/
theorem mehlerN_iteratedDeriv_three_C2b (a : ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (hs : 0 < Real.sin a) (w u : E) :
    iteratedDeriv 3 (fun t : ℝ => mehlerN a f (w + t • u)) 0 =
      Real.cos a ^ 3 / Real.sin a *
        ∫ z, inner ℝ z u * mehlerND2 f (Real.cos a • w + Real.sin a • z) u
          ∂(stdGaussian E) := by
  obtain ⟨C0, h0⟩ := h0
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  by_cases hu : u = 0
  · subst hu
    simp [iteratedDeriv_const]
  · set lam : ℝ := ‖u‖ with hlam
    set v : E := ‖u‖⁻¹ • u with hvdef
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have huv : lam • v = u := by
      rw [hvdef, hlam, smul_smul, mul_inv_cancel₀ hu', one_smul]
    have h := mehlerN_iteratedDeriv_three_C2b_unit a hf h0 h1 h2 hs hv w lam
    rw [huv] at h
    rw [h]
    have hint : ∀ z : E, inner ℝ z u * mehlerND2 f (Real.cos a • w + Real.sin a • z) u
        = lam ^ 3 * (inner ℝ z v * mehlerND2 f (Real.cos a • w + Real.sin a • z) v) := by
      intro z
      rw [← huv, inner_smul_right, mehlerND2_smul hf]
      ring
    simp_rw [hint]
    rw [integral_const_mul]
    ring


/-! ### Complements: conventions, marginal, Fréchet derivative formulas -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mehlerNHerm_zero (r : ℕ) (z : E) : mehlerNHerm r z 0 = 0 ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [mehlerNHerm]
  · simp [mehlerNHerm, hr.ne']

/-- The reduction of the Gaussian integral of the Hermite factor to dimension one. -/
theorem mehlerN_integral_abs_hermite_inner {v : E} (hv : ‖v‖ = 1) (r : ℕ) :
    ∫ z, |Polynomial.aeval (inner ℝ z v) (Polynomial.hermite r)| ∂(stdGaussian E) =
      ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  have hm : Measurable (fun z : E => inner ℝ z v) := by fun_prop
  have hHm : AEStronglyMeasurable (fun x : ℝ => |Polynomial.aeval x (Polynomial.hermite r)|)
      (Measure.map (fun z : E => inner ℝ z v) (stdGaussian E)) :=
    (((Polynomial.hermite r).continuous_aeval (A := ℝ)).abs).aestronglyMeasurable
  have := integral_map hm.aemeasurable hHm
  rw [mehlerN_map_inner hv] at this
  exact this.symm

theorem mehlerN_integral_abs_herm (r : ℕ) (u : E) :
    ∫ z, |mehlerNHerm r z u| ∂(stdGaussian E) =
      ‖u‖ ^ r * ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  by_cases hu : u = 0
  · subst hu
    simp only [mehlerNHerm_zero, norm_zero, abs_pow, abs_zero, integral_const]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · simp [hr.ne']
  · have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    set v : E := ‖u‖⁻¹ • u with hvdef
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
    have hinner : ∀ z : E, inner ℝ z v = inner ℝ z u / ‖u‖ := fun z => by
      rw [hvdef, inner_smul_right, div_eq_inv_mul]
    have : ∀ z : E, |mehlerNHerm r z u| =
        ‖u‖ ^ r * |Polynomial.aeval (inner ℝ z v) (Polynomial.hermite r)| := fun z => by
      rw [mehlerNHerm, hinner z, abs_mul, abs_pow, abs_norm]
    simp_rw [this]
    rw [integral_const_mul, mehlerN_integral_abs_hermite_inner hv]

theorem mehlerN_fderiv_apply (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w u : E) :
    fderiv ℝ (mehlerN a f) w u = Real.cos a / Real.sin a *
      ∫ z, f (Real.cos a • w + Real.sin a • z) * inner ℝ z u ∂(stdGaussian E) := by
  rw [(mehlerN_hasFDerivAt a hf hC hs w).fderiv, mehlerNGrad_apply a hf hC]

/-- The `r`-th Fréchet derivative on the diagonal `(u, …, u)`, in the Hermite form. -/
theorem mehlerN_iteratedFDeriv_diag (a : ℝ) {f : E → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) :
    iteratedFDeriv ℝ r (mehlerN a f) w (fun _ => u) =
      (Real.cos a / Real.sin a) ^ r *
        ∫ z, f (Real.cos a • w + Real.sin a • z) * mehlerNHerm r z u ∂(stdGaussian E) := by
  rw [← mehlerN_iteratedDeriv_line_eq (mehlerN_contDiff_nat r a f hf hb hs) w u,
    mehlerN_iteratedDeriv_line a hf hb hs]

/-- The bound for the `r`-th Fréchet derivative on the diagonal `(u, …, u)`. -/
theorem mehlerN_iteratedFDeriv_diag_bound (a : ℝ) {f : E → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (r : ℕ) (w u : E) :
    |iteratedFDeriv ℝ r (mehlerN a f) w (fun _ => u)| ≤
      C * |Real.cos a / Real.sin a| ^ r * ‖u‖ ^ r *
        ∫ z, |Polynomial.aeval z (Polynomial.hermite r)| ∂(gaussianReal 0 1) := by
  rw [← mehlerN_iteratedDeriv_line_eq (mehlerN_contDiff_nat r a f hf ⟨C, hC⟩ hs) w u]
  exact mehlerN_iteratedDeriv_line_bound a hf hC hs r w u

/-- The third Fréchet derivative along `(u, u, u)`, in the Hermite form. -/
theorem mehlerN_iteratedFDeriv_three_hermite (a : ℝ) {f : E → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ x, |f x| ≤ C) (hs : 0 < Real.sin a) (w u : E) :
    iteratedFDeriv ℝ 3 (mehlerN a f) w ![u, u, u] =
      (Real.cos a / Real.sin a) ^ 3 *
        ∫ z, f (Real.cos a • w + Real.sin a • z) * mehlerNHerm 3 z u ∂(stdGaussian E) := by
  rw [mehlerN_iteratedFDeriv_three a hf hb hs, mehlerN_iteratedDeriv_line a hf hb hs]

/-- The third Fréchet derivative along `(u, u, u)`, in the `C²_b` form (Raic (2.7)). -/
theorem mehlerN_iteratedFDeriv_three_C2b (a : ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (hs : 0 < Real.sin a) (w u : E) :
    iteratedFDeriv ℝ 3 (mehlerN a f) w ![u, u, u] =
      Real.cos a ^ 3 / Real.sin a *
        ∫ z, inner ℝ z u * mehlerND2 f (Real.cos a • w + Real.sin a • z) u
          ∂(stdGaussian E) := by
  rw [mehlerN_iteratedFDeriv_three a hf.continuous.measurable h0 hs,
    mehlerN_iteratedDeriv_three_C2b a hf h0 h1 h2 hs]


/-! ### Consistency with the one-dimensional calculus (`d = 1`) -/

/-- The unit vector of `EuclideanSpace ℝ (Fin 1)`. -/
def mehlerNe0 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem mehlerNe0_norm : ‖mehlerNe0‖ = 1 := by
  simp [mehlerNe0]

/-- For `d = 1`, `mehlerN` on the line `ℝ e₀` is the one-dimensional `mehlerSmooth` of the trace. -/
theorem mehlerN_fin_one (a : ℝ) {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (t : ℝ) :
    mehlerN a f (t • mehlerNe0) = mehlerSmooth a (fun x : ℝ => f (x • mehlerNe0)) t := by
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 1) =>
      f (Real.cos a • (t • mehlerNe0) + Real.sin a • z)) (stdGaussian _) :=
    Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC _)
  unfold mehlerN
  rw [mehlerN_split_integral mehlerNe0_norm hint]
  have hP : ∀ y : EuclideanSpace ℝ (Fin 1), y - inner ℝ mehlerNe0 y • mehlerNe0 = 0 := by
    intro y
    ext i
    fin_cases i
    simp [mehlerNe0, EuclideanSpace.inner_single_left]
  have : ∀ y : EuclideanSpace ℝ (Fin 1), ∫ σ, f (Real.cos a • (t • mehlerNe0) +
      Real.sin a • mehlerNPsi mehlerNe0 (σ, y)) ∂(gaussianReal 0 1) =
      mehlerSmooth a (fun x : ℝ => f (x • mehlerNe0)) t := by
    intro y
    unfold mehlerSmooth mehlerNPsi
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp only [hP y, add_zero]
    congr 1
    module
  simp_rw [this]
  simp

end

end LatticeProb
