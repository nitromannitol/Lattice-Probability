import Mathlib
import LatticeProb.Prob.MehlerSmoothing
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeClassLayer
import LatticeProb.Prob.MvbeKeyEstimate
import LatticeProb.Prob.MvbeLargeAngle

/-!
# Raic's Lemma 2.7, the small-angle case (paper (2.14)-(2.17)); packet P15

Notation: `E = EuclideanSpace ℝ (Fin m)`, `U_a f = mehlerN a f`, `C : MvbeRegularClass m κ`,
`(Ω, P)` a probability space, `W : Ω → E` measurable, `μ : E`, `S` a covariance matrix (the paper's
`Σ`; `Σ` is a reserved token in Lean), `γ = stdGaussian E`.

* `mvbeH a f u P W = E ⟨∇³ U_a f (W), u⊗3⟩` (the paper's `H_a(u)`, (2.13)); defined in
  `MvbeLargeAngle` (packet P16) and imported here.
* `mvbe_class_deviation` (paper (2.16)): under the hypothesis (2.10) in the form
  `hD : ∀ B ∈ C.cls ∪ {∅, univ}, |P(W ∈ B) - N(μ,S)(B)| ≤ D`, for `0 < a < π/2`, `y : E` and
  `B1 ⊆ B2` in `C.cls ∪ {∅, univ}`:
  `|P(cos a W + sin a y ∈ B2 \ B1) - N(cos a μ + sin a y, cos² a S)(B2 \ B1)| ≤ 2 D`.
  The proof uses (A1) only (the preimage of a class set under `w ↦ cos a w + sin a y` stays in
  the class, `mvbe_affine_preimage_mem` of `MvbeLargeAngle`) and the
  push-forward identity `N(μ,S) ∘ (w ↦ c w + v)⁻¹ = N(c μ + v, c² S)`
  (`mvbe_sa_map_affine_multivariateGaussian`, valid for every matrix `S`).
* `mvbe_small_angle_bound` (paper (2.14), (2.16), (2.17) up to the layer width): for `f` of
  class `C²` with bounded `f`, `∇f`, `∇²f`, a second-derivative bound
  `‖∇²f‖ ≤ Λ 1_{B2 \ B1}` **Lebesgue-almost everywhere** (this is the only form available for the
  Bentkus smoothing: `MvbeRegularClass.ae_norm_iteratedFDeriv_two_smoothOuter_le`; the pointwise
  form is the special case, `mvbe_small_angle_bound_of_pointwise`) and a layer-mass bound
  `N(cos a μ + sin a y, cos² a S)(B2 \ B1) ≤ M0` uniform in `y`,
  `|H_a(u)| ≤ Λ c₁ (cos³ a / sin a) (M0 + 2 D)` for `‖u‖ ≤ 1`, `c₁ = mvbeHermiteConst 1`.
  Route: formula (2.7) (`mehlerN_iteratedFDeriv_three_C2b`), Fubini over `P ⊗ γ`
  (`mvbe_sa_H_eq_integral`), the a.e.-transfer from Lebesgue to `P ⊗ γ`
  (`mvbe_sa_ae_affine_stdGaussian`, `Measure.ae_ae_comm`), the bound
  `|F_a(z)| ≤ Λ P(cos a W + sin a z ∈ B2 \ B1)` (`mvbe_sa_abs_integral_D2_le`), (2.16), and
  Lemma 2.5 with `r = 1` (`mvbe_sa_gaussian_inner_integral_le`).
* `mvbe_small_angle_corollary`: with `Λ = 4 (1 + κ) / ε²` and `M0 = γ* ε / (σ cos a)`,
  `|H_a(u)| ≤ 4 (1 + κ) c₁ cos² a / (ε sin a) (γ*/σ + 2 D / ε)` (paper (2.17)).

The hypothesis `0 ≤ M0` (resp. `0 ≤ γ*`) is added to the layer-mass bound: for `M0 < 0` the
hypothesis `N ≤ ofReal M0` says only `N = 0` and the conclusion would be false.  The hypotheses
`σ • 1 ≤ √S`, `0 < σ ≤ 1` of the paper are used only through the layer-mass hypothesis
(to be discharged by `mvbe_gaussian_layer_diff_le_of_le_sqrt` at the width of the layer).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace LatticeProb

section SmallAngle

/-- Square root of a scalar multiple: `√(c² S) = c √S` for `S ⪰ 0`, `c ≥ 0`. -/
theorem mvbe_sa_sqrt_smul_sq {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : CFC.sqrt ((c ^ 2) • S) = c • CFC.sqrt S := by
  refine CFC.sqrt_unique ?_ (smul_nonneg hc (CFC.sqrt_nonneg S))
  rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self S hS.nonneg, sq]

/-- **Push-forward of a Gaussian under an affine map.**  For `c > 0`,
`(w ↦ c w + v)_# N(μ, S) = N(c μ + v, c² S)`, for every matrix `S` (for non-positive-semidefinite
`S` both sides are Dirac masses). -/
theorem mvbe_sa_map_affine_multivariateGaussian {d : ℕ} (μ v : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) {c : ℝ} (hc : 0 < c) :
    (multivariateGaussian μ S).map (fun w => c • w + v)
      = multivariateGaussian (c • μ + v) ((c ^ 2) • S) := by
  by_cases hS : S.PosSemidef
  · have hm : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
        μ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := by fun_prop
    unfold multivariateGaussian
    rw [Measure.map_map (by fun_prop) hm, mvbe_sa_sqrt_smul_sq hS hc.le]
    congr 1
    funext x
    simp [map_smul, smul_add]
    abel
  · have hS' : ¬ ((c ^ 2) • S).PosSemidef := by
      intro h
      apply hS
      have := h.smul (inv_nonneg.mpr (sq_nonneg c))
      rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this
    rw [multivariateGaussian_of_not_posSemidef _ hS, multivariateGaussian_of_not_posSemidef _ hS',
      Measure.map_dirac' (f := fun w : EuclideanSpace ℝ (Fin d) => c • w + v) (by fun_prop)]

section ClassLevel

variable {m : ℕ} {κ : ℝ}

/-- Members of `C.cls ∪ {∅, univ}` are measurable. -/
theorem mvbe_sa_measurableSet_of_mem_union (C : MvbeRegularClass m κ)
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : B ∈ C.cls ∪ {∅, Set.univ}) :
    MeasurableSet B := by
  rcases hB with hB | hB
  · exact C.measurableSet_mem B hB
  · rcases hB with rfl | hB
    · exact MeasurableSet.empty
    · rw [Set.mem_singleton_iff.mp hB]
      exact MeasurableSet.univ

/-- **Class-level deviation lemma** (Raic (2.16)).  From the hypothesis (2.10) on the class
(`hD`, which also covers `∅` and `univ`), for `0 < a < π/2`, `y : E` and `B1 ⊆ B2` in
`C.cls ∪ {∅, univ}`:
`|P(cos a W + sin a y ∈ B2 \ B1) - N(cos a μ + sin a y, cos² a S)(B2 \ B1)| ≤ 2 D`. -/
theorem mvbe_class_deviation (C : MvbeRegularClass m κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W)
    (μ : EuclideanSpace ℝ (Fin m)) (S : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (y : EuclideanSpace ℝ (Fin m))
    {B1 B2 : Set (EuclideanSpace ℝ (Fin m))} (h1 : B1 ∈ C.cls ∪ {∅, Set.univ})
    (h2 : B2 ∈ C.cls ∪ {∅, Set.univ}) (hsub : B1 ⊆ B2) :
    |(P {ω | Real.cos a • W ω + Real.sin a • y ∈ B2 \ B1}).toReal
      - (multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S)
          (B2 \ B1)).toReal| ≤ 2 * D := by
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, ha1⟩
  set g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun w => Real.cos a • w + Real.sin a • y with hg
  have hgm : Measurable g := by fun_prop
  have hB1' : g ⁻¹' B1 ∈ C.cls ∪ {∅, Set.univ} := mvbe_affine_preimage_mem C h1 ha0 ha1 y
  have hB2' : g ⁻¹' B2 ∈ C.cls ∪ {∅, Set.univ} := mvbe_affine_preimage_mem C h2 ha0 ha1 y
  have hm1 : MeasurableSet (g ⁻¹' B1) := hgm (mvbe_sa_measurableSet_of_mem_union C h1)
  have hm2 : MeasurableSet (g ⁻¹' B2) := hgm (mvbe_sa_measurableSet_of_mem_union C h2)
  have hsub' : g ⁻¹' B1 ⊆ g ⁻¹' B2 := Set.preimage_mono hsub
  have hset : {ω | Real.cos a • W ω + Real.sin a • y ∈ B2 \ B1}
      = W ⁻¹' (g ⁻¹' B2) \ W ⁻¹' (g ⁻¹' B1) := by
    ext ω; simp [hg]
  have hP : (P {ω | Real.cos a • W ω + Real.sin a • y ∈ B2 \ B1}).toReal
      = (P (W ⁻¹' (g ⁻¹' B2))).toReal - (P (W ⁻¹' (g ⁻¹' B1))).toReal := by
    rw [hset]
    have := measureReal_sdiff (μ := P) (Set.preimage_mono hsub') (hW hm1)
    simpa [Measure.real] using this
  have hN : (multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S)
          (B2 \ B1)).toReal
      = (multivariateGaussian μ S (g ⁻¹' B2)).toReal
        - (multivariateGaussian μ S (g ⁻¹' B1)).toReal := by
    rw [← mvbe_sa_map_affine_multivariateGaussian μ (Real.sin a • y) S hc0,
      Measure.map_apply hgm ((mvbe_sa_measurableSet_of_mem_union C h2).diff
        (mvbe_sa_measurableSet_of_mem_union C h1)), Set.preimage_sdiff]
    have := measureReal_sdiff (μ := multivariateGaussian μ S) hsub' hm1
    simpa [Measure.real] using this
  rw [hP, hN]
  have e1 := hD _ hB1'
  have e2 := hD _ hB2'
  calc _ = |((P (W ⁻¹' (g ⁻¹' B2))).toReal - (multivariateGaussian μ S (g ⁻¹' B2)).toReal)
        - ((P (W ⁻¹' (g ⁻¹' B1))).toReal - (multivariateGaussian μ S (g ⁻¹' B1)).toReal)| := by
          congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

end ClassLevel

section Third

variable {m : ℕ}

/-- The Fréchet third derivative of the Mehler smoothing, on the diagonal, in the `C²_b` form. -/
theorem mvbe_sa_iteratedFDeriv_three_diag (a : ℝ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ContDiff ℝ 2 f) (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (hs : 0 < Real.sin a)
    (w u : EuclideanSpace ℝ (Fin m)) :
    iteratedFDeriv ℝ 3 (mehlerN a f) w (fun _ => u) =
      Real.cos a ^ 3 / Real.sin a *
        ∫ z, inner ℝ z u * mehlerND2 f (Real.cos a • w + Real.sin a • z) u
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have : (fun _ : Fin 3 => u) = ![u, u, u] := by
    funext i; fin_cases i <;> rfl
  rw [this]
  exact mehlerN_iteratedFDeriv_three_C2b a hf h0 h1 h2 hs w u

/-- `|D² f(x)[u,u]| ≤ ‖D² f(x)‖ ‖u‖²`. -/
theorem mvbe_sa_abs_D2_le {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 2 f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    |mehlerND2 f x u| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖u‖ ^ 2 := by
  rw [mehlerND2_eq hf, ← Real.norm_eq_abs]
  calc ‖iteratedFDeriv ℝ 2 f x (fun _ => u)‖
      ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ∏ _i : Fin 2, ‖u‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = _ := by simp

/-- `z ↦ ⟪z, u⟫` is `γ`-integrable. -/
theorem mvbe_sa_integrable_inner (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m) => inner ℝ z u)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have := IsGaussian.integrable_dual (stdGaussian (EuclideanSpace ℝ (Fin m))) (innerSL ℝ u)
  refine this.congr (ae_of_all _ fun z => ?_)
  simp [real_inner_comm]

/-- **Fubini form of `H_a(u)`** (Raic (2.7) integrated over `W`):
`H_a(u) = (cos³ a / sin a) ∫ ⟪z, u⟫ F_a(z) dγ(z)`, `F_a(z) = E D² f(cos a W + sin a z)[u, u]`. -/
theorem mvbe_sa_H_eq_integral (a : ℝ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ContDiff ℝ 2 f) (h0 : ∃ C, ∀ x, |f x| ≤ C) (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C) (hs : 0 < Real.sin a)
    (u : EuclideanSpace ℝ (Fin m)) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) :
    mvbeH a f u P W = Real.cos a ^ 3 / Real.sin a *
      ∫ z, inner ℝ z u * (∫ ω, mehlerND2 f (Real.cos a • W ω + Real.sin a • z) u ∂P)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  obtain ⟨C2, hC2⟩ := h2
  unfold mvbeH
  simp_rw [mvbe_sa_iteratedFDeriv_three_diag a hf h0 h1 ⟨C2, hC2⟩ hs]
  rw [integral_const_mul]
  congr 1
  have hx : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin m) =>
      Real.cos a • W p.1 + Real.sin a • p.2) := by fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (ω : Ω)
      (z : EuclideanSpace ℝ (Fin m)) =>
        inner ℝ z u * mehlerND2 f (Real.cos a • W ω + Real.sin a • z) u)
      (P.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have h3 : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin m) =>
        mehlerND2 f (Real.cos a • W p.1 + Real.sin a • p.2) u) :=
      (mehlerND2_continuous hf u).measurable.comp hx
    have h4 : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin m) => inner ℝ p.2 u) := by
      fun_prop
    exact h4.mul h3
  have hbd : Integrable (fun p : Ω × EuclideanSpace ℝ (Fin m) =>
      (fun _ : Ω => (1 : ℝ)) p.1 * (fun z : EuclideanSpace ℝ (Fin m) =>
        C2 * ‖u‖ ^ 2 * |inner ℝ z u|) p.2)
      (P.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) :=
    (integrable_const (1 : ℝ)).mul_prod ((mvbe_sa_integrable_inner u).abs.const_mul (C2 * ‖u‖ ^ 2))
  have hint : Integrable (Function.uncurry fun (ω : Ω) (z : EuclideanSpace ℝ (Fin m)) =>
        inner ℝ z u * mehlerND2 f (Real.cos a • W ω + Real.sin a • z) u)
      (P.prod (stdGaussian (EuclideanSpace ℝ (Fin m)))) := by
    refine Integrable.mono' hbd hmeas (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs, one_mul]
    rw [mul_comm]
    calc |mehlerND2 f (Real.cos a • W p.1 + Real.sin a • p.2) u| * |inner ℝ p.2 u|
        ≤ (C2 * ‖u‖ ^ 2) * |inner ℝ p.2 u| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact (mvbe_sa_abs_D2_le hf _ u).trans
            (mul_le_mul_of_nonneg_right (hC2 _) (by positivity))
      _ = _ := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [integral_const_mul]

/-- Almost-everywhere statements for Lebesgue measure transfer to the standard Gaussian along an
invertible affine map `z ↦ b + s • z`. -/
theorem mvbe_sa_ae_affine_stdGaussian {p : EuclideanSpace ℝ (Fin m) → Prop}
    (hp : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))), p x) {s : ℝ} (hs : s ≠ 0)
    (b : EuclideanSpace ℝ (Fin m)) :
    ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin m))), p (b + s • z) := by
  have hac : stdGaussian (EuclideanSpace ℝ (Fin m))
      ≪ (volume : Measure (EuclideanSpace ℝ (Fin m))) := by
    rw [mvbe_stdGaussian_eq_withDensity m]
    exact withDensity_absolutelyContinuous _ _
  have h2 : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin m))), p (b + s • z) := by
    rw [ae_iff] at hp ⊢
    have : {z : EuclideanSpace ℝ (Fin m) | ¬ p (b + s • z)}
        = (fun z => s • z) ⁻¹' ((fun x => b + x) ⁻¹' {x | ¬ p x}) := rfl
    rw [this, Measure.addHaar_preimage_smul volume hs, measure_preimage_add, hp, mul_zero]
  exact hac.ae_le h2

/-- **Lemma 2.5 for `r = 1`, almost-everywhere bounded integrand**:
`|∫ ⟪z,u⟫ F(z) dγ| ≤ c₁ M ‖u‖` if `|F| ≤ M` a.e. -/
theorem mvbe_sa_gaussian_inner_integral_le (u : EuclideanSpace ℝ (Fin m))
    {F : EuclideanSpace ℝ (Fin m) → ℝ} (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFM : ∀ᵐ z ∂(stdGaussian (EuclideanSpace ℝ (Fin m))), |F z| ≤ M) :
    |∫ z, inner ℝ z u * F z ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))|
      ≤ mvbeHermiteConst 1 * M * ‖u‖ := by
  by_cases hu : u = 0
  · subst hu
    simp only [inner_zero_right, zero_mul, integral_zero, abs_zero, norm_zero, mul_zero]
    exact le_rfl
  · have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
    set G : EuclideanSpace ℝ (Fin m) → ℝ := fun z => max (-M) (min M (F z)) with hG
    have hGm : Measurable G := measurable_const.max (measurable_const.min hF)
    have hGM : ∀ z, |G z - 0| ≤ M := by
      intro z
      rw [sub_zero, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hFG : (fun z => inner ℝ z u * F z) =ᵐ[stdGaussian (EuclideanSpace ℝ (Fin m))]
        fun z => inner ℝ z u * G z := by
      filter_upwards [hFM] with z hz
      have h := abs_le.1 hz
      simp only [hG, min_eq_right h.2, max_eq_right h.1]
    rw [integral_congr_ae hFG]
    have key := mvbe_gaussian_hermite_integral_le_scaled (d := m) (r := 1) le_rfl (by norm_num)
      u G hGm 0 M hGM
    have hform : ∫ z, G z * (Polynomial.aeval (inner ℝ z u / ‖u‖)) (Polynomial.hermite 1)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))
        = ‖u‖⁻¹ * ∫ z, inner ℝ z u * G z ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [mvbe_aeval_hermite_one]
      ring
    rw [hform, abs_mul, abs_of_pos (inv_pos.2 hun), pow_one] at key
    have : |∫ z, inner ℝ z u * G z ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))|
        = ‖u‖ * (‖u‖⁻¹ * |∫ z, inner ℝ z u * G z ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))|) := by
      field_simp
    rw [this]
    nlinarith [key]

/-- Per-`z` bound for `F_a(z) = E D² f (cos a W + sin a z)[u,u]` in terms of the layer
probability (Raic (2.14)): if `‖D² f‖ ≤ Λ 1_{B2 \ B1}` holds `P`-a.e. along the translate
`ω ↦ cos a W ω + sin a z`, then `|F_a(z)| ≤ Λ P(cos a W + sin a z ∈ B2 \ B1)` for `‖u‖ ≤ 1`. -/
theorem mvbe_sa_abs_integral_D2_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 2 f)
    {B1 B2 : Set (EuclideanSpace ℝ (Fin m))} (hB1 : MeasurableSet B1) (hB2 : MeasurableSet B2)
    {Λ : ℝ} (a : ℝ) {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1)
    (z : EuclideanSpace ℝ (Fin m))
    (hz : ∀ᵐ ω ∂P, ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖
      ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) (Real.cos a • W ω + Real.sin a • z)) :
    |∫ ω, mehlerND2 f (Real.cos a • W ω + Real.sin a • z) u ∂P|
      ≤ Λ * (P {ω | Real.cos a • W ω + Real.sin a • z ∈ B2 \ B1}).toReal := by
  set S : Set Ω := {ω | Real.cos a • W ω + Real.sin a • z ∈ B2 \ B1} with hS
  have hSm : MeasurableSet S := by
    have : Measurable fun ω => Real.cos a • W ω + Real.sin a • z := by fun_prop
    exact this (hB2.diff hB1)
  have hind : ∀ ω, (B2 \ B1).indicator (fun _ => (1 : ℝ)) (Real.cos a • W ω + Real.sin a • z)
      = S.indicator (fun _ => (1 : ℝ)) ω := fun ω => by
    by_cases h : Real.cos a • W ω + Real.sin a • z ∈ B2 \ B1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show ω ∈ S from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show ω ∉ S from h)]
  have hint : Integrable (fun ω => Λ * S.indicator (fun _ => (1 : ℝ)) ω) P :=
    ((integrable_const (1 : ℝ)).indicator hSm).const_mul Λ
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [hz] with ω hω
    rw [Real.norm_eq_abs]
    refine (mvbe_sa_abs_D2_le hf _ u).trans ?_
    calc ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖ * ‖u‖ ^ 2
        ≤ ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hu) (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; rw [hind] at hω; exact hω
  · rw [integral_const_mul, integral_indicator_const _ hSm, smul_eq_mul, mul_one]
    exact le_rfl

end Third

section SmallAngleBound

variable {m : ℕ} {κ : ℝ}

/-- **The bound for `H_a(u)` in the small-angle range** (Raic (2.14)-(2.17)).  The second
derivative hypothesis `hΛf` is Lebesgue-a.e. (the form proved for the Bentkus smoothing); the layer
mass hypothesis `hlayer` is uniform in the centre `y`. -/
theorem mvbe_small_angle_bound (C : MvbeRegularClass m κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 2 f) (h0 : ∃ C, ∀ x, |f x| ≤ C)
    (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    {B1 B2 : Set (EuclideanSpace ℝ (Fin m))} (hB1 : B1 ∈ C.cls ∪ {∅, Set.univ})
    (hB2 : B2 ∈ C.cls ∪ {∅, Set.univ}) (hsub : B1 ⊆ B2) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hΛf : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) x)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hlayer : ∀ y : EuclideanSpace ℝ (Fin m),
      multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S) (B2 \ B1)
        ≤ ENNReal.ofReal M0)
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a f u P W|
      ≤ Λ * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a) * (M0 + 2 * D) := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD ∅ (Or.inr (Or.inl rfl)))
  have hB1m := mvbe_sa_measurableSet_of_mem_union C hB1
  have hB2m := mvbe_sa_measurableSet_of_mem_union C hB2
  rw [mvbe_sa_H_eq_integral a hf h0 h1 h2 hs u P hW]
  set γ := stdGaussian (EuclideanSpace ℝ (Fin m)) with hγ
  set M : ℝ := Λ * (M0 + 2 * D) with hMdef
  have hM : 0 ≤ M := by positivity
  set F : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun z => ∫ ω, mehlerND2 f (Real.cos a • W ω + Real.sin a • z) u ∂P with hF
  have hx : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin m) =>
      Real.cos a • W p.1 + Real.sin a • p.2) := by fun_prop
  have hFm : Measurable F := by
    have h3 : Measurable (fun p : Ω × EuclideanSpace ℝ (Fin m) =>
        mehlerND2 f (Real.cos a • W p.1 + Real.sin a • p.2) u) :=
      (mehlerND2_continuous hf u).measurable.comp hx
    exact (h3.stronglyMeasurable.integral_prod_left' (μ := P)).measurable
  have hqm : MeasurableSet {x : EuclideanSpace ℝ (Fin m) |
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) x} := by
    have hc : Continuous fun x : EuclideanSpace ℝ (Fin m) => ‖iteratedFDeriv ℝ 2 f x‖ :=
      (hf.continuous_iteratedFDeriv (by norm_num)).norm
    exact measurableSet_le hc.measurable
      (((measurable_const.indicator (hB2m.diff hB1m))).const_mul Λ)
  have hae : ∀ᵐ z ∂γ, ∀ᵐ ω ∂P, ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖
      ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) (Real.cos a • W ω + Real.sin a • z) := by
    have h1' : ∀ᵐ ω ∂P, ∀ᵐ z ∂γ, ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖
        ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) (Real.cos a • W ω + Real.sin a • z) :=
      ae_of_all _ fun ω => mvbe_sa_ae_affine_stdGaussian hΛf hs.ne' (Real.cos a • W ω)
    exact (Measure.ae_ae_comm (p := fun (ω : Ω) (z : EuclideanSpace ℝ (Fin m)) =>
      ‖iteratedFDeriv ℝ 2 f (Real.cos a • W ω + Real.sin a • z)‖
        ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) (Real.cos a • W ω + Real.sin a • z))
      (hx hqm)).1 h1'
  have hFM : ∀ᵐ z ∂γ, |F z| ≤ M := by
    filter_upwards [hae] with z hz
    have e1 := mvbe_sa_abs_integral_D2_le P hW hf hB1m hB2m a hu z hz
    have e2 := mvbe_class_deviation C P hW μ S hD ha0 ha1 z hB1 hB2 hsub
    have e3 : (multivariateGaussian (Real.cos a • μ + Real.sin a • z) ((Real.cos a) ^ 2 • S)
        (B2 \ B1)).toReal ≤ M0 := ENNReal.toReal_le_of_le_ofReal hM0 (hlayer z)
    refine e1.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 e2).2]) hΛ
  have hI := mvbe_sa_gaussian_inner_integral_le u hFm hM hFM
  have hc1 : 0 ≤ mvbeHermiteConst 1 := mvbeHermiteConst_nonneg 1
  have hpos : 0 ≤ Real.cos a ^ 3 / Real.sin a := by positivity
  rw [abs_mul, abs_of_nonneg hpos]
  calc Real.cos a ^ 3 / Real.sin a * |∫ z, inner ℝ z u * F z ∂γ|
      ≤ Real.cos a ^ 3 / Real.sin a * (mvbeHermiteConst 1 * M * 1) := by
        refine mul_le_mul_of_nonneg_left (hI.trans ?_) hpos
        exact mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by rw [hMdef]; ring

/-- The small-angle bound with the second-derivative hypothesis in its pointwise form
`∀ x, ‖D² f(x)‖ ≤ Λ 1_{B2 \ B1}(x)` (a special case of `mvbe_small_angle_bound`). -/
theorem mvbe_small_angle_bound_of_pointwise (C : MvbeRegularClass m κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 2 f) (h0 : ∃ C, ∀ x, |f x| ≤ C)
    (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    {B1 B2 : Set (EuclideanSpace ℝ (Fin m))} (hB1 : B1 ∈ C.cls ∪ {∅, Set.univ})
    (hB2 : B2 ∈ C.cls ∪ {∅, Set.univ}) (hsub : B1 ⊆ B2) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hΛf : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ Λ * (B2 \ B1).indicator (fun _ => (1 : ℝ)) x)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hlayer : ∀ y : EuclideanSpace ℝ (Fin m),
      multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S) (B2 \ B1)
        ≤ ENNReal.ofReal M0)
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a f u P W|
      ≤ Λ * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a) * (M0 + 2 * D) :=
  mvbe_small_angle_bound C P hW μ S hD hf h0 h1 h2 hB1 hB2 hsub hΛ
    (Filter.Eventually.of_forall hΛf) ha0 ha1 hM0 hlayer hu

/-- **Raic (2.17), in the paper's shape.**  With `Λ = 4 (1 + κ) / ε²` (the Bentkus bound on
`∇²f`) and the layer mass `M0 = γ* ε / (σ cos a)` (`γ*` a nonnegative real, the Gaussian perimeter
of the class, entering only through this hypothesis),
`|H_a(u)| ≤ 4 (1 + κ) c₁ cos² a / (ε sin a) · (γ*/σ + 2 D / ε)` for `‖u‖ ≤ 1`.  Compared with
`mvbe_small_angle_bound` this uses `cos³ a ≤ cos² a` on the `D`-term. -/
theorem mvbe_small_angle_corollary (C : MvbeRegularClass m κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → EuclideanSpace ℝ (Fin m)} (hW : Measurable W) (μ : EuclideanSpace ℝ (Fin m))
    (S : Matrix (Fin m) (Fin m) ℝ) {D : ℝ}
    (hD : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(P (W ⁻¹' B)).toReal - (multivariateGaussian μ S B).toReal| ≤ D)
    {f : EuclideanSpace ℝ (Fin m) → ℝ} (hf : ContDiff ℝ 2 f) (h0 : ∃ C, ∀ x, |f x| ≤ C)
    (h1 : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) (h2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C)
    {B1 B2 : Set (EuclideanSpace ℝ (Fin m))} (hB1 : B1 ∈ C.cls ∪ {∅, Set.univ})
    (hB2 : B2 ∈ C.cls ∪ {∅, Set.univ}) (hsub : B1 ⊆ B2) {ε : ℝ} (hε : 0 < ε)
    (hΛf : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ 4 * (1 + κ) / ε ^ 2 * (B2 \ B1).indicator (fun _ => (1 : ℝ)) x)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) {σ γs : ℝ} (hσ : 0 < σ) (hγs : 0 ≤ γs)
    (hlayer : ∀ y : EuclideanSpace ℝ (Fin m),
      multivariateGaussian (Real.cos a • μ + Real.sin a • y) ((Real.cos a) ^ 2 • S) (B2 \ B1)
        ≤ ENNReal.ofReal (γs * ε / (σ * Real.cos a)))
    {u : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ ≤ 1) :
    |mvbeH a f u P W|
      ≤ 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * (γs / σ + 2 * D / ε) := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hc1 : Real.cos a ≤ 1 := Real.cos_le_one a
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD ∅ (Or.inr (Or.inl rfl)))
  have hκ := C.kappa_nonneg
  have hk : 0 ≤ 4 * (1 + κ) / ε ^ 2 := by positivity
  have hM0 : 0 ≤ γs * ε / (σ * Real.cos a) := by positivity
  have hb := mvbe_small_angle_bound C P hW μ S hD hf h0 h1 h2 hB1 hB2 hsub hk hΛf ha0 ha1 hM0
    hlayer hu
  have hcc : 0 ≤ mvbeHermiteConst 1 := mvbeHermiteConst_nonneg 1
  refine hb.trans ?_
  have hdiff : 4 * (1 + κ) * mvbeHermiteConst 1 * Real.cos a ^ 2 / (ε * Real.sin a)
        * (γs / σ + 2 * D / ε)
      - 4 * (1 + κ) / ε ^ 2 * mvbeHermiteConst 1 * (Real.cos a ^ 3 / Real.sin a)
        * (γs * ε / (σ * Real.cos a) + 2 * D)
      = 8 * (1 + κ) * mvbeHermiteConst 1 * D * Real.cos a ^ 2 * (1 - Real.cos a)
        / (ε ^ 2 * Real.sin a) := by
    field_simp
    ring
  have hnn : 0 ≤ 8 * (1 + κ) * mvbeHermiteConst 1 * D * Real.cos a ^ 2 * (1 - Real.cos a)
      / (ε ^ 2 * Real.sin a) := by
    have : 0 ≤ 1 - Real.cos a := by linarith
    positivity
  linarith

end SmallAngleBound

end SmallAngle

end LatticeProb
