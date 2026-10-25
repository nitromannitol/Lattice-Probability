module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGDimension/Gaussian/SteinIBP.lean.
-/
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Gaussian integration by parts (Stein's lemma)

For a standard Gaussian vector `x` of a finite-dimensional real inner product space `E`, a
direction `a : E`, and a bounded continuous function `G : E → ℝ` with a bounded continuous
gradient `G'` (given through the derivatives of `G` along lines), we prove

  `E[⟪a, x⟫ G(x)] = E[⟪G'(x), a⟫]`   (`LatticeProb.GaussConc.integral_inner_mul_stdGaussian`).

The proof reduces, through an orthonormal basis and Fubini, to the one-dimensional identity
`E[x g(x)] = E[g'(x)]` for `x ∼ N(0,1)`, which is integration by parts against the density
`φ` of `N(0,1)`, using `φ' = -x φ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LatticeProb

namespace GaussConc

/-! ### One-dimensional Stein identity -/

/-- The derivative of the standard Gaussian density is `-x φ(x)`. -/
lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun y : ℝ => -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-x) x := by
    have := (((hasDerivAt_id x).sub_const 0).pow 2).neg.div_const (2 * ((1 : ℝ≥0) : ℝ))
    exact this.congr_deriv (by norm_num; ring)
  have h2 := h.exp.const_mul (√(2 * π * ((1 : ℝ≥0) : ℝ)))⁻¹
  rw [gaussianPDFReal_def]
  refine h2.congr_deriv ?_
  beta_reduce
  ring

/-- Integrability against `N(0,1)` is integrability of the product with the density. -/
lemma integrable_gaussianReal_std_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [toReal_gaussianPDF]

/-- **One-dimensional Stein identity**: for `x ∼ N(0,1)` and `g` differentiable with `g` and
`g'` bounded, `E[x g(x)] = E[g'(x)]`. -/
theorem integral_mul_gaussianReal_std {g g' : ℝ → ℝ} {C C' : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg_bdd : ∀ x, |g x| ≤ C) (hg'_bdd : ∀ x, |g' x| ≤ C') :
    ∫ x, x * g x ∂(gaussianReal 0 1) = ∫ x, g' x ∂(gaussianReal 0 1) := by
  have hg'_eq : g' = deriv g := funext fun x => (hg x).deriv.symm
  have hg'_meas : Measurable g' := hg'_eq ▸ measurable_deriv g
  have hg_cont : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_fun_id
  have h1 : Integrable (fun x => x * g x) (gaussianReal 0 1) :=
    hid.mul_bdd hg_cont.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hg_bdd x)
  have h2 : Integrable g' (gaussianReal 0 1) :=
    Integrable.of_bound hg'_meas.aestronglyMeasurable C'
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hg'_bdd x)
  have h3 : Integrable g (gaussianReal 0 1) :=
    Integrable.of_bound hg_cont.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hg_bdd x)
  rw [integrable_gaussianReal_std_iff] at h1 h2 h3
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g)
    (v := gaussianPDFReal 0 1) (u' := g') (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hg x) (fun x _ => hasDerivAt_gaussianPDFReal_std x) ?_ ?_ ?_
  · simp only [smul_eq_mul]
    have e1 : (fun x => gaussianPDFReal 0 1 x * (x * g x)) =
        fun x => -(g x * (-x * gaussianPDFReal 0 1 x)) := by
      funext x; ring
    rw [e1, integral_neg, ibp, neg_neg]
    congr 1; funext x; ring
  · have e : (g * fun x => -x * gaussianPDFReal 0 1 x) =
        fun x => -(gaussianPDFReal 0 1 x * (x * g x)) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h1.neg
  · have e : (g' * gaussianPDFReal 0 1) = fun x => gaussianPDFReal 0 1 x * g' x := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h2
  · have e : (g * gaussianPDFReal 0 1) = fun x => gaussianPDFReal 0 1 x * g x := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [e]; exact h3

/-! ### One coordinate of a standard Gaussian vector of `ℝⁿ` -/

/-- Inserting a value into a coordinate of a vector splits off the inserted value as a
multiple of a standard basis vector. -/
lemma insertNth_eq_add_smul_single {n : ℕ} (k : Fin (n + 1)) (t : ℝ) (r : Fin n → ℝ) :
    (Fin.insertNth k t r : Fin (n + 1) → ℝ) = Fin.insertNth k 0 r + t • Pi.single k 1 := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩
  · simp
  · simp [Fin.insertNth_apply_succAbove]

/-- **Stein identity in one coordinate** of a standard Gaussian vector of `ℝ^{n+1}`. -/
theorem integral_coord_mul_pi_succ {n : ℕ} (k : Fin (n + 1)) {h h' : (Fin (n + 1) → ℝ) → ℝ}
    {C C' : ℝ}
    (hh : ∀ c t, HasDerivAt (fun s : ℝ => h (c + s • Pi.single k 1))
      (h' (c + t • Pi.single k 1)) t)
    (hh_cont : Continuous h) (hh'_meas : Measurable h')
    (hh_bdd : ∀ c, |h c| ≤ C) (hh'_bdd : ∀ c, |h' c| ≤ C') :
    ∫ c, c k * h c ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, h' c ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  have hmp :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) k).symm
  have hint1 : Integrable (fun c : Fin (n + 1) → ℝ => c k * h c)
      (Measure.pi fun _ => gaussianReal 0 1) :=
    (integrable_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1) (i := k)
      IsGaussian.integrable_id).mul_bdd hh_cont.aestronglyMeasurable
      (ae_of_all _ fun c => by simpa [Real.norm_eq_abs] using hh_bdd c)
  have hint2 : Integrable h' (Measure.pi fun _ => gaussianReal 0 1) :=
    Integrable.of_bound hh'_meas.aestronglyMeasurable C'
      (ae_of_all _ fun c => by simpa [Real.norm_eq_abs] using hh'_bdd c)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k with he
  have hint1' : Integrable (fun x : ℝ × (Fin n → ℝ) => e.symm x k * h (e.symm x))
      ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)) :=
    hmp.integrable_comp_of_integrable hint1
  have hint2' : Integrable (fun x : ℝ × (Fin n → ℝ) => h' (e.symm x))
      ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)) :=
    hmp.integrable_comp_of_integrable hint2
  rw [← hmp.integral_comp' (fun c => c k * h c), ← hmp.integral_comp' h',
    integral_prod_symm _ hint1', integral_prod_symm _ hint2']
  congr 1
  funext r
  simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same]
  refine integral_mul_gaussianReal_std (g := fun t => h (Fin.insertNth k t r))
    (g' := fun t => h' (Fin.insertNth k t r)) (C := C) (C' := C') (fun t => ?_)
    (fun t => hh_bdd _) (fun t => hh'_bdd _)
  have := hh (Fin.insertNth k 0 r) t
  simp only [← insertNth_eq_add_smul_single] at this
  exact this

/-- **Stein identity in one coordinate** of a standard Gaussian vector of `ℝᴺ`. -/
theorem integral_coord_mul_pi {N : ℕ} (k : Fin N) {h h' : (Fin N → ℝ) → ℝ} {C C' : ℝ}
    (hh : ∀ c t, HasDerivAt (fun s : ℝ => h (c + s • Pi.single k 1))
      (h' (c + t • Pi.single k 1)) t)
    (hh_cont : Continuous h) (hh'_meas : Measurable h')
    (hh_bdd : ∀ c, |h c| ≤ C) (hh'_bdd : ∀ c, |h' c| ≤ C') :
    ∫ c, c k * h c ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, h' c ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  cases N with
  | zero => exact k.elim0
  | succ n => exact integral_coord_mul_pi_succ k hh hh_cont hh'_meas hh_bdd hh'_bdd

/-! ### Stein's lemma for the standard Gaussian of an inner product space -/

/-- The linear map `c ↦ ∑ i, c i • B i`. -/
def coordSum {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ} (B : Fin N → E)
    (c : Fin N → ℝ) : E :=
  ∑ i, c i • B i

/-- Shifting a coordinate vector by `s` times a standard basis vector shifts its image by
`s` times the corresponding vector. -/
lemma coordSum_add_smul_single {E : Type*} [AddCommGroup E] [Module ℝ E] {N : ℕ}
    (B : Fin N → E) (c : Fin N → ℝ) (k : Fin N) (s : ℝ) :
    coordSum B (c + s • Pi.single k 1) = coordSum B c + s • B k := by
  simp [coordSum, Pi.single_apply, add_smul, Finset.sum_add_distrib, ite_smul]

/-- The linear map `coordSum B` is continuous. -/
lemma continuous_coordSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (B : Fin N → E) : Continuous (coordSum B) := by
  unfold coordSum
  fun_prop

/-- **Stein's lemma (Gaussian integration by parts).**  Let `x` be a standard Gaussian vector
of `E`, `a : E`, and `G : E → ℝ` bounded and continuous, whose derivative along every line
`s ↦ x + s • e` is `⟪G' (x + s • e), e⟫` for a bounded continuous gradient `G'`.  Then
`E[⟪a, x⟫ G(x)] = E[⟪G'(x), a⟫]`. -/
theorem integral_inner_mul_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {G : E → ℝ} {G' : E → E} {C C' : ℝ}
    (hG : ∀ x e t, HasDerivAt (fun s : ℝ => G (x + s • e)) ⟪G' (x + t • e), e⟫ t)
    (hG_cont : Continuous G) (hG'_cont : Continuous G')
    (hG_bdd : ∀ x, |G x| ≤ C) (hG'_bdd : ∀ x, ‖G' x‖ ≤ C') (a : E) :
    ∫ x, ⟪a, x⟫ * G x ∂(stdGaussian E) = ∫ x, ⟪G' x, a⟫ ∂(stdGaussian E) := by
  set B := stdOrthonormalBasis ℝ E with hB
  have hT : Continuous (coordSum (N := Module.finrank ℝ E) B) := continuous_coordSum _
  have hk : ∀ k, ∫ c, c k * G (coordSum B c) ∂(Measure.pi fun _ => gaussianReal 0 1) =
      ∫ c, ⟪G' (coordSum B c), B k⟫ ∂(Measure.pi fun _ => gaussianReal 0 1) := by
    intro k
    refine integral_coord_mul_pi k (h := fun c => G (coordSum B c))
      (h' := fun c => ⟪G' (coordSum B c), B k⟫)
      (C := C) (C' := C' * ‖B k‖) (fun c t => ?_) (hG_cont.comp hT)
      ((hG'_cont.comp hT).inner continuous_const).measurable (fun c => hG_bdd _) (fun c => ?_)
    · simp only [coordSum_add_smul_single]
      exact hG (coordSum B c) (B k) t
    · calc |⟪G' (coordSum B c), B k⟫| ≤ ‖G' (coordSum B c)‖ * ‖B k‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ C' * ‖B k‖ := by gcongr; exact hG'_bdd _
  have hPi : stdGaussian E =
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1).map (coordSum B) := rfl
  rw [hPi, integral_map (f := fun x : E => ⟪a, x⟫ * G x) hT.aemeasurable
      ((continuous_const.inner continuous_id).mul hG_cont).aestronglyMeasurable,
    integral_map (f := fun x : E => ⟪G' x, a⟫) hT.aemeasurable
      (hG'_cont.inner continuous_const).aestronglyMeasurable]
  have e1 : ∀ c, ⟪a, coordSum B c⟫ * G (coordSum B c) =
      ∑ k, ⟪a, B k⟫ * (c k * G (coordSum B c)) := by
    intro c
    simp only [coordSum, inner_sum, real_inner_smul_right, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ c, ⟪G' (coordSum B c), a⟫ = ∑ k, ⟪a, B k⟫ * ⟪G' (coordSum B c), B k⟫ := by
    intro c
    rw [← B.sum_inner_mul_inner (G' (coordSum B c)) a]
    exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm a (B k)]; ring
  simp only [e1, e2]
  rw [integral_finsetSum _ fun k _ => ?_, integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul, hk k]
  · refine Integrable.of_bound
      ((continuous_const.mul ((hG'_cont.comp hT).inner continuous_const)).aestronglyMeasurable)
      (|⟪a, B k⟫| * (C' * ‖B k‖)) (ae_of_all _ fun c => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    gcongr
    calc |⟪G' (coordSum B c), B k⟫| ≤ ‖G' (coordSum B c)‖ * ‖B k‖ := abs_real_inner_le_norm _ _
      _ ≤ C' * ‖B k‖ := by gcongr; exact hG'_bdd _
  · exact ((integrable_eval (μ := fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) (i := k)
      IsGaussian.integrable_id).mul_bdd (hG_cont.comp hT).aestronglyMeasurable
      (ae_of_all _ fun c => by simpa [Real.norm_eq_abs] using hG_bdd (coordSum B c))).const_mul _

/-! ### Nonvacuity examples -/

namespace GaussSteinIBPExample

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

/-- **Stein's identity for `sin`**: for `X ∼ N(0,1)`, `E[X sin X] = E[cos X]`. -/
theorem stein_sin :
    ∫ x, x * sin x ∂(gaussianReal 0 1) = ∫ x, cos x ∂(gaussianReal 0 1) :=
  LatticeProb.GaussConc.integral_mul_gaussianReal_std (g := sin) (g' := cos)
    (fun x => hasDerivAt_sin x) (fun x => abs_sin_le_one x) (fun x => abs_cos_le_one x)

/-- **Stein's lemma on `EuclideanSpace ℝ (Fin 2)` for `x ↦ sin ⟪v, x⟫`**, whose gradient is
`x ↦ cos ⟪v, x⟫ • v`: `E[⟪a, X⟫ sin ⟪v, X⟫] = E[⟪cos ⟪v, X⟫ • v, a⟫]`. -/
theorem inner_stdGaussian_sin (a v : EuclideanSpace ℝ (Fin 2)) :
    ∫ x, ⟪a, x⟫ * sin ⟪v, x⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      ∫ x, ⟪cos ⟪v, x⟫ • v, a⟫ ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  have hG : ∀ (x e : EuclideanSpace ℝ (Fin 2)) (t : ℝ),
      HasDerivAt (fun s : ℝ => sin ⟪v, x + s • e⟫) ⟪cos ⟪v, x + t • e⟫ • v, e⟫ t := by
    intro x e t
    have hf : (fun s : ℝ => ⟪v, x + s • e⟫) = fun s => ⟪v, x⟫ + s * ⟪v, e⟫ := by
      funext s; simp [inner_add_right, real_inner_smul_right]
    have h1 : HasDerivAt (fun s : ℝ => ⟪v, x + s • e⟫) ⟪v, e⟫ t := by
      rw [hf]
      simpa using ((hasDerivAt_id t).mul_const ⟪v, e⟫).const_add ⟪v, x⟫
    convert h1.sin using 1
    rw [real_inner_smul_left]
  exact LatticeProb.GaussConc.integral_inner_mul_stdGaussian
    (G := fun x => sin ⟪v, x⟫) (G' := fun x => cos ⟪v, x⟫ • v) (C := 1) (C' := ‖v‖)
    hG (by fun_prop) (by fun_prop) (fun x => abs_sin_le_one _)
    (fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg v) (abs_cos_le_one _)) a

end GaussSteinIBPExample

end GaussConc

end LatticeProb
