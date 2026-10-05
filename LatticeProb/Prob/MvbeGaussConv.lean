import Mathlib
import LatticeProb.Gauss.MultivariateDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder Pointwise

namespace LatticeProb

/-! ### (1) Convolution of Gaussians -/

/-- **Convolution of Gaussians.**  For positive semidefinite `S`, `T`, the convolution of
`N(μ, S)` and `N(ν, T)` is `N(μ + ν, S + T)`.  Proof: equality of characteristic functions
(`Measure.ext_of_charFun`), `charFun_conv` and `charFun_multivariateGaussian`. -/
theorem mvbe_multivariateGaussian_add {d : ℕ}
    (μ ν : EuclideanSpace ℝ (Fin d)) {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    (multivariateGaussian μ S) ∗ (multivariateGaussian ν T)
      = multivariateGaussian (μ + ν) (S + T) := by
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [charFun_conv, charFun_multivariateGaussian hS, charFun_multivariateGaussian hT,
    charFun_multivariateGaussian (hS.add hT), ← Complex.exp_add]
  congr 1
  simp [inner_add_right, add_mulVec, dotProduct_add]
  ring

/-- **Law of a sum of independent Gaussians.**  If `X ~ N(μ, S)` and `Y ~ N(ν, T)` are
independent under a finite measure `P`, then the law of `X + Y` is `N(μ + ν, S + T)`. -/
theorem mvbe_law_add_multivariateGaussian {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → EuclideanSpace ℝ (Fin d)} (hX : Measurable X) (hY : Measurable Y)
    (hXY : X ⟂ᵢ[P] Y) (μ ν : EuclideanSpace ℝ (Fin d)) {S T : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef)
    (hXlaw : P.map X = multivariateGaussian μ S) (hYlaw : P.map Y = multivariateGaussian ν T) :
    P.map (X + Y) = multivariateGaussian (μ + ν) (S + T) := by
  rw [hXY.map_add_eq_map_conv_map₀ hX.aemeasurable hY.aemeasurable, hXlaw, hYlaw,
    mvbe_multivariateGaussian_add μ ν hS hT]

/-! ### (2) Decomposition -/

/-- The square root of a scalar matrix: `√(σ² • 1) = σ • 1` for `σ ≥ 0`. -/
theorem mvbe_sqrt_smul_one {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    CFC.sqrt ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
      = σ • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hb : (0 : Matrix (Fin d) (Fin d) ℝ) ≤ σ • (1 : Matrix (Fin d) (Fin d) ℝ) :=
    smul_nonneg hσ zero_le_one
  refine CFC.sqrt_unique ?_ hb
  simp [smul_smul, sq]

/-- `σ² • 1` is positive semidefinite. -/
theorem mvbe_posSemidef_smul_one (d : ℕ) (σ : ℝ) :
    ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (sq_nonneg σ)

/-- **The isotropic Gaussian as a scaled standard Gaussian, with mean.**
`N(μ, σ² 1) = (μ + σ ·)_# γ` for `σ ≥ 0`. -/
theorem mvbe_multivariateGaussian_smul_one {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) {σ : ℝ}
    (hσ : 0 ≤ σ) :
    multivariateGaussian μ ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
      = (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => μ + σ • z) := by
  simp only [multivariateGaussian, mvbe_sqrt_smul_one hσ]
  congr 1
  ext z i
  simp

/-- **Scaling of the standard Gaussian.**  `(σ ·)_# γ = N(0, σ² 1)` for `σ ≥ 0`. -/
theorem mvbe_stdGaussian_map_smul {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => σ • z)
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  rw [multivariateGaussian_eq_map, mvbe_sqrt_smul_one hσ]
  congr 1
  ext z i
  simp

/-- **Gaussian decomposition** (Raic, Lemma 2.2, Gaussian core).  If `σ ≥ 0` and
`S - σ² 1` is positive semidefinite, then
`N(μ, S) = (μ + σ ·)_# γ ∗ N(0, S - σ² 1)`:
a Gaussian of covariance `S` is a standard Gaussian of scale `σ` (centred at `μ`) plus an
independent centred Gaussian of covariance `S - σ² 1`. -/
theorem mvbe_gaussian_decomp {d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 ≤ σ)
    {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) :
    multivariateGaussian μ S
      = ((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => μ + σ • z))
          ∗ multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  rw [← mvbe_multivariateGaussian_smul_one μ hσ,
    mvbe_multivariateGaussian_add μ 0 (mvbe_posSemidef_smul_one d σ) hS]
  simp

/-! ### (3) Layer probabilities of a convolution -/

section Layer

variable {E : Type*} [MeasurableSpace E]

/-- **Fubini form of the convolution.**  For s-finite `μ`, `κ` and measurable `B`,
`(μ ∗ κ) B = ∫⁻ r, μ ({x | x + r ∈ B}) ∂κ`, i.e. the integral over `κ` of the `μ`-mass of the
translate `B - r = (· + r)⁻¹' B`. -/
theorem mvbe_conv_apply_eq_lintegral [AddCommMonoid E] [MeasurableAdd₂ E]
    (μ κ : Measure E) [SFinite μ] [SFinite κ] {B : Set E} (hB : MeasurableSet B) :
    (μ ∗ κ) B = ∫⁻ r, μ ((fun x => x + r) ⁻¹' B) ∂κ := by
  rw [Measure.conv, Measure.map_apply measurable_add hB,
    Measure.prod_apply_symm (measurable_add hB)]
  rfl

/-- **Pushforward under a scalar dilation.**  For `σ ≠ 0` and measurable `A`,
`(ρ.map (σ • ·)) A = ρ (σ⁻¹ • A)`. -/
theorem mvbe_map_smul_apply [AddCommMonoid E] [Module ℝ E] [MeasurableConstSMul ℝ E]
    (ρ : Measure E) {σ : ℝ} (hσ : σ ≠ 0) {A : Set E} (hA : MeasurableSet A) :
    (ρ.map (fun x => σ • x)) A = ρ (σ⁻¹ • A) := by
  rw [Measure.map_apply (measurable_const_smul σ) hA, Set.preimage_smul₀ hσ]

omit [MeasurableSpace E] in
/-- The translate `(· + r)⁻¹' B` is `B - r`, the image of `B` under `· - r`. -/
theorem mvbe_preimage_add_const_eq_image_sub [AddCommGroup E] (B : Set E) (r : E) :
    (fun x => x + r) ⁻¹' B = (fun b => b - r) '' B := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro h
    exact ⟨x + r, h, by simp⟩
  · rintro ⟨b, hb, rfl⟩
    simpa using hb

/-- **Layer probability of a convolution with a scaled measure** (the Fubini step used verbatim
in the layer estimate).  For `σ ≠ 0`, s-finite `ρ`, `κ` and measurable `B`,
`((ρ.map (σ • ·)) ∗ κ) B = ∫⁻ r, ρ (σ⁻¹ • (B - r)) ∂κ`,
where `B - r = (· + r)⁻¹' B`. -/
theorem mvbe_layer_of_conv [AddCommMonoid E] [Module ℝ E] [MeasurableAdd₂ E]
    [MeasurableConstSMul ℝ E] (ρ κ : Measure E) [SFinite ρ] [SFinite κ] {σ : ℝ} (hσ : σ ≠ 0)
    {B : Set E} (hB : MeasurableSet B) :
    ((ρ.map (fun x => σ • x)) ∗ κ) B
      = ∫⁻ r, ρ (σ⁻¹ • ((fun x => x + r) ⁻¹' B)) ∂κ := by
  rw [mvbe_conv_apply_eq_lintegral _ κ hB]
  refine lintegral_congr fun r => ?_
  exact mvbe_map_smul_apply ρ hσ (measurable_add_const r hB)

end Layer

section GaussianLayer

variable {d : ℕ}

/-- **Gaussian layer formula.**  For `σ ≥ 0` with `S - σ² 1` positive semidefinite and `B`
measurable,
`N(μ, S) B = ∫⁻ r, γ {z | μ + σ z + r ∈ B} ∂N(0, S - σ² 1)(r)`. -/
theorem mvbe_gaussian_layer (μ : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 ≤ σ)
    {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    multivariateGaussian μ S B
      = ∫⁻ r, stdGaussian (EuclideanSpace ℝ (Fin d))
          ((fun z => μ + σ • z + r) ⁻¹' B)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  rw [mvbe_gaussian_decomp μ hσ hS, mvbe_conv_apply_eq_lintegral _ _ hB]
  refine lintegral_congr fun r => ?_
  have hf : Measurable fun z : EuclideanSpace ℝ (Fin d) => μ + σ • z := by fun_prop
  rw [Measure.map_apply hf (measurable_add_const r hB)]
  rfl

/-- **Gaussian layer formula, dilation form.**  For `σ > 0`,
`N(μ, S) B = ∫⁻ r, γ (σ⁻¹ • (B - (μ + r))) ∂N(0, S - σ² 1)(r)`,
where `B - (μ + r) = (· + (μ + r))⁻¹' B`. -/
theorem mvbe_gaussian_layer_smul (μ : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ)
    {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    multivariateGaussian μ S B
      = ∫⁻ r, stdGaussian (EuclideanSpace ℝ (Fin d))
          (σ⁻¹ • ((fun x => x + (μ + r)) ⁻¹' B))
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (S - (σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  rw [mvbe_gaussian_layer μ hσ.le hS hB]
  refine lintegral_congr fun r => ?_
  rw [← Set.preimage_smul₀ hσ.ne']
  congr 1
  ext z
  simp only [Set.mem_preimage]
  rw [show μ + σ • z + r = σ • z + (μ + r) by abel]

/-- The Fubini layer formula specialised to the standard Gaussian: for `σ ≠ 0`,
`((γ.map (σ • ·)) ∗ κ) B = ∫⁻ r, γ (σ⁻¹ • (B - r)) ∂κ`. -/
theorem mvbe_layer_stdGaussian (κ : Measure (EuclideanSpace ℝ (Fin d))) [SFinite κ] {σ : ℝ}
    (hσ : σ ≠ 0) {B : Set (EuclideanSpace ℝ (Fin d))} (hB : MeasurableSet B) :
    (((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => σ • x)) ∗ κ) B
      = ∫⁻ r, stdGaussian (EuclideanSpace ℝ (Fin d))
          (σ⁻¹ • ((fun x => x + r) ⁻¹' B)) ∂κ :=
  mvbe_layer_of_conv _ κ hσ hB

end GaussianLayer

end LatticeProb
