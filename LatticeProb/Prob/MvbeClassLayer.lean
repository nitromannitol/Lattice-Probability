import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeGaussConv

/-!
# Gaussian layer estimate under a general covariance (Raic, Lemma 2.2)

Packet P10 of the staged formalisation of Raic's Theorem 1.3 (arXiv:1802.06475).

For a regular class `C : MvbeRegularClass m κ`, `A ∈ C.cls`, `ε > 0`, `0 < σ ≤ 1` and a matrix
`S` with `S - σ² 1` positive semidefinite (equivalently `S ⪰ σ² 1`, equivalently
`σ 1 ≤ √S` for `S ⪰ 0`):
`N(μ, S)(A^{ε|ρ} \ A) ≤ γ*(C | ρ) · ε/σ`  and  `N(μ, S)(A \ A^{-ε|ρ}) ≤ γ*(C | ρ) · ε/σ`,
where `γ* = C.gammaStar (stdGaussian _)` is the Gaussian perimeter of the class.

Route (Raic): `N(μ, S) = (μ + σ ·)_# γ ∗ N(0, S - σ² 1)` (`mvbe_gaussian_decomp`), Fubini over the
independent part (`mvbe_gaussian_layer_smul`), and for each translate `B := σ⁻¹ (A - v)`:
`B ∈ C.cls` by (A1), the translated layer is the layer of the translate by (A5), and
`σ⁻¹ (A^{ε|ρ} \ A - v) ⊆ B^{ε/σ|ρ} \ B` by (A4) and (A6) (for the difference `B^{ε|ρ} \ B`
the sign condition (A4) `ρ_B ≥ 0` off `B` makes (A6) applicable, and similarly `ρ_B ≤ 0` on `B`
for the inner layer; (A6) alone does not control `ρ_{qB}(qx)` from above for `x` deep inside `B`).

Fields of `MvbeRegularClass` used: `a1_translate`, `a1_scale`, `a4_nonpos`, `a4_nonneg`, `a5`,
`a6`, `measurableSet_mem`, `measurable_rho`.  No extra hypothesis is needed.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder Pointwise

namespace LatticeProb

section ClassLayer

variable {m : ℕ} {κ : ℝ}

/-- The preimage of `A` under `x ↦ x + v` is the translate `A + (-v)` of `A`. -/
theorem mvbe_preimage_add_eq_image_add_neg (A : Set (EuclideanSpace ℝ (Fin m)))
    (v : EuclideanSpace ℝ (Fin m)) :
    (fun x => x + v) ⁻¹' A = (fun z => z + (-v)) '' A := by
  ext x
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro h
    exact ⟨x + v, h, by simp⟩
  · rintro ⟨b, hb, rfl⟩
    simpa using hb

/-- Translation covariance of `ρ` in the form used for preimages: by (A5),
`ρ_{A + (-v)}(x) = ρ_A(x + v)`. -/
theorem mvbe_rho_translate_neg (C : MvbeRegularClass m κ) {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA : A ∈ C.cls) (v x : EuclideanSpace ℝ (Fin m)) :
    C.rho ((fun z => z + (-v)) '' A) x = C.rho A (x + v) := by
  have h := C.a5 A hA (-v) (x + v)
  rwa [show x + v + -v = x by abel] at h

/-- The preimage of the layer `A^{t|ρ}` under `x ↦ x + v` is the layer of the translate
`A + (-v)` (by (A5)). -/
theorem mvbe_preimage_layer_translate (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) (v : EuclideanSpace ℝ (Fin m))
    (t : ℝ) :
    (fun x => x + v) ⁻¹' mvbeLayer C.rho A t
      = mvbeLayer C.rho ((fun z => z + (-v)) '' A) t := by
  ext x
  simp only [Set.mem_preimage, mvbeLayer, Set.mem_setOf_eq, mvbe_rho_translate_neg C hA]

/-- Closure of the class under dilations by factors `q ≥ 1` ((A1), with `q = 1` trivial). -/
theorem mvbe_scale_mem (C : MvbeRegularClass m κ) {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : B ∈ C.cls) {q : ℝ} (hq : 1 ≤ q) : (fun x => q • x) '' B ∈ C.cls := by
  rcases hq.eq_or_lt with rfl | hlt
  · simpa using hB
  · exact C.a1_scale B hB q hlt

/-- **Outer layer under dilation** ((A4) and (A6)).  For `B` in the class and `q ≥ 1`,
`q (B^{ε|ρ} \ B) ⊆ (qB)^{qε|ρ} \ qB`. -/
theorem mvbe_scale_layer_diff_subset (C : MvbeRegularClass m κ)
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : B ∈ C.cls) {q : ℝ} (hq : 1 ≤ q) (ε : ℝ) :
    (fun x => q • x) '' (mvbeLayer C.rho B ε \ B)
      ⊆ mvbeLayer C.rho ((fun x => q • x) '' B) (q * ε) \ (fun x => q • x) '' B := by
  have hq0 : q ≠ 0 := by positivity
  rintro _ ⟨x, ⟨hxL, hxB⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have h0 : 0 ≤ C.rho B x := C.a4_nonneg B hB x hxB
    have h6 := C.a6 B hB q hq x
    rw [abs_of_nonneg h0] at h6
    have hxL' : C.rho B x ≤ ε := hxL
    exact (le_abs_self _).trans (h6.trans (mul_le_mul_of_nonneg_left hxL' (by linarith)))
  · rintro ⟨y, hy, hyx⟩
    exact hxB (smul_right_injective _ hq0 hyx ▸ hy)

/-- **Inner layer under dilation** ((A4) and (A6)).  For `B` in the class and `q ≥ 1`,
`q (B \ B^{-ε|ρ}) ⊆ qB \ (qB)^{-qε|ρ}`. -/
theorem mvbe_scale_diff_layer_subset (C : MvbeRegularClass m κ)
    {B : Set (EuclideanSpace ℝ (Fin m))} (hB : B ∈ C.cls) {q : ℝ} (hq : 1 ≤ q) (ε : ℝ) :
    (fun x => q • x) '' (B \ mvbeLayer C.rho B (-ε))
      ⊆ (fun x => q • x) '' B \ mvbeLayer C.rho ((fun x => q • x) '' B) (-(q * ε)) := by
  rintro _ ⟨x, ⟨hxB, hxL⟩, rfl⟩
  refine ⟨⟨x, hxB, rfl⟩, ?_⟩
  intro hL
  have h1 : C.rho B x ≤ 0 := C.a4_nonpos B hB x hxB
  have h2 : -ε < C.rho B x := not_le.mp hxL
  have h6 := C.a6 B hB q hq x
  rw [abs_of_nonpos h1] at h6
  have hL' : C.rho ((fun x => q • x) '' B) (q • x) ≤ -(q * ε) := hL
  have h3 : q * ε ≤ |C.rho ((fun x => q • x) '' B) (q • x)| :=
    by linarith [neg_le_abs (C.rho ((fun x => q • x) '' B) (q • x))]
  have h4 : q * (-C.rho B x) < q * ε :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  linarith

/-- Translation of the outer layer difference: `(· + v)⁻¹' (A^{t|ρ} \ A) = (A + (-v))^{t|ρ} \
(A + (-v))`. -/
theorem mvbe_preimage_layer_diff_translate (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) (v : EuclideanSpace ℝ (Fin m))
    (t : ℝ) :
    (fun x => x + v) ⁻¹' (mvbeLayer C.rho A t \ A)
      = mvbeLayer C.rho ((fun z => z + (-v)) '' A) t \ (fun z => z + (-v)) '' A := by
  rw [Set.preimage_sdiff, mvbe_preimage_layer_translate C hA v t,
    mvbe_preimage_add_eq_image_add_neg]

/-- Translation of the inner layer difference. -/
theorem mvbe_preimage_diff_layer_translate (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) (v : EuclideanSpace ℝ (Fin m))
    (t : ℝ) :
    (fun x => x + v) ⁻¹' (A \ mvbeLayer C.rho A t)
      = (fun z => z + (-v)) '' A \ mvbeLayer C.rho ((fun z => z + (-v)) '' A) t := by
  rw [Set.preimage_sdiff, mvbe_preimage_layer_translate C hA v t,
    mvbe_preimage_add_eq_image_add_neg]

/-- Outer layer estimate for a dilated set, for an arbitrary measure `γ`:
`γ(q (B^{ε|ρ} \ B)) ≤ qε γ*`. -/
theorem mvbe_measure_scale_layer_diff_le (C : MvbeRegularClass m κ)
    (γ : Measure (EuclideanSpace ℝ (Fin m))) {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : B ∈ C.cls) {q : ℝ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    γ (q • (mvbeLayer C.rho B ε \ B)) ≤ C.gammaStar γ * ENNReal.ofReal (q * ε) := by
  rw [← Set.image_smul, mul_comm]
  exact (measure_mono (mvbe_scale_layer_diff_subset C hB hq ε)).trans
    (mvbe_layer_diff_le γ C.cls C.rho (mvbe_scale_mem C hB hq) (by positivity))

/-- Inner layer estimate for a dilated set, for an arbitrary measure `γ`:
`γ(q (B \ B^{-ε|ρ})) ≤ qε γ*`. -/
theorem mvbe_measure_scale_diff_layer_le (C : MvbeRegularClass m κ)
    (γ : Measure (EuclideanSpace ℝ (Fin m))) {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : B ∈ C.cls) {q : ℝ} (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    γ (q • (B \ mvbeLayer C.rho B (-ε))) ≤ C.gammaStar γ * ENNReal.ofReal (q * ε) := by
  rw [← Set.image_smul, mul_comm]
  exact (measure_mono (mvbe_scale_diff_layer_subset C hB hq ε)).trans
    (mvbe_diff_layer_le γ C.cls C.rho (mvbe_scale_mem C hB hq) (by positivity))

/-- The outer layer `A^{ε|ρ} \ A` of a class member is measurable. -/
theorem mvbe_measurableSet_layer_diff (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) (t : ℝ) :
    MeasurableSet (mvbeLayer C.rho A t \ A) :=
  ((C.measurable_rho A hA) measurableSet_Iic).diff (C.measurableSet_mem A hA)

/-- The inner layer `A \ A^{-ε|ρ}` of a class member is measurable. -/
theorem mvbe_measurableSet_diff_layer (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) (t : ℝ) :
    MeasurableSet (A \ mvbeLayer C.rho A t) :=
  (C.measurableSet_mem A hA).diff ((C.measurable_rho A hA) measurableSet_Iic)

/-- **Gaussian layer under general covariance, outer form** (Raic, Lemma 2.2).
For a regular class `C`, `A ∈ C`, `ε > 0`, `0 < σ ≤ 1`, and `S - σ² 1` positive semidefinite,
`N(μ, S)(A^{ε|ρ} \ A) ≤ γ*(C) · ε/σ`.  Uses only `a1_translate`, `a1_scale`, `a4_nonpos`,
`a4_nonneg`, `a5`, `a6`, `measurableSet_mem`, `measurable_rho`. -/
theorem mvbe_gaussian_layer_diff_le (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) :
    (multivariateGaussian μ S) (mvbeLayer C.rho A ε \ A)
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) := by
  have hq : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ1
  rw [mvbe_gaussian_layer_smul μ hσ hS (mvbe_measurableSet_layer_diff C hA ε)]
  calc _ ≤ ∫⁻ _r, C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))) := by
        refine lintegral_mono fun r => ?_
        rw [mvbe_preimage_layer_diff_translate C hA (μ + r) ε]
        have h := mvbe_measure_scale_layer_diff_le C (stdGaussian (EuclideanSpace ℝ (Fin m)))
          (C.a1_translate A hA (-(μ + r))) hq hε
        rwa [← div_eq_inv_mul] at h
    _ = _ := by simp

/-- **Gaussian layer under general covariance, inner form** (Raic, Lemma 2.2).
`N(μ, S)(A \ A^{-ε|ρ}) ≤ γ*(C) · ε/σ`, under the same hypotheses as
`mvbe_gaussian_layer_diff_le`. -/
theorem mvbe_gaussian_diff_layer_le (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) :
    (multivariateGaussian μ S) (A \ mvbeLayer C.rho A (-ε))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) := by
  have hq : 1 ≤ σ⁻¹ := (one_le_inv₀ hσ).mpr hσ1
  rw [mvbe_gaussian_layer_smul μ hσ hS (mvbe_measurableSet_diff_layer C hA (-ε))]
  calc _ ≤ ∫⁻ _r, C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ))) := by
        refine lintegral_mono fun r => ?_
        rw [mvbe_preimage_diff_layer_translate C hA (μ + r) (-ε)]
        have h := mvbe_measure_scale_diff_layer_le C (stdGaussian (EuclideanSpace ℝ (Fin m)))
          (C.a1_translate A hA (-(μ + r))) hq hε
        rwa [← div_eq_inv_mul] at h
    _ = _ := by simp



/-! ### Bridge between the hypotheses on `S` -/



/-- For real matrices, Hermitian and symmetric coincide. -/
theorem mvbe_isHermitian_iff_isSymm {S : Matrix (Fin m) (Fin m) ℝ} :
    S.IsHermitian ↔ S.IsSymm := by
  simp [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial]

theorem mvbe_posSemidef_sub_smul_one_iff_dotProduct {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.IsHermitian) (c : ℝ) :
    (S - c • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef ↔
      ∀ x : Fin m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x) := by
  have hH : (S - c • (1 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian :=
    hS.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all c))
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [hH, true_and, star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, sub_nonneg]

/-- The Euclidean quadratic form `⟪S v, v⟫` in terms of `dotProduct`. -/
theorem mvbe_inner_toLp_mulVec (S : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (WithLp.toLp 2 (S *ᵥ WithLp.ofLp v)) v
      = WithLp.ofLp v ⬝ᵥ (S *ᵥ WithLp.ofLp v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- `‖v‖² = v ⬝ᵥ v` in `EuclideanSpace`. -/
theorem mvbe_norm_sq_eq_dotProduct (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ^ 2 = WithLp.ofLp v ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- **Bridge lemma.**  For a symmetric matrix `S`, Raic's lower bound `S ⪰ σ² I` in the form
`∀ v, σ² ‖v‖² ≤ ⟪S v, v⟫` is equivalent to `(S - σ² 1).PosSemidef`. -/
theorem mvbe_posSemidef_sub_sq_smul_one_iff {S : Matrix (Fin m) (Fin m) ℝ}
    (hS : S.IsHermitian) (σ : ℝ) :
    (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef ↔
      ∀ v : EuclideanSpace ℝ (Fin m),
        σ ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (WithLp.toLp 2 (S *ᵥ WithLp.ofLp v)) v := by
  rw [mvbe_posSemidef_sub_smul_one_iff_dotProduct hS]
  simp only [mvbe_inner_toLp_mulVec, mvbe_norm_sq_eq_dotProduct]
  constructor
  · intro h v
    exact h _
  · intro h x
    simpa using h (WithLp.toLp 2 x)

/-- `σ 1 ≤ √S` implies `S - σ² 1 ⪰ 0` for `S ⪰ 0`, `σ ≥ 0`. -/
theorem mvbe_posSemidef_sub_sq_of_le_sqrt {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef)
    {σ : ℝ} (hσ : 0 ≤ σ) (h : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S) :
    (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  have hTT : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
  have h0 : 0 ≤ CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ) := sub_nonneg.mpr h
  have hsq : S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)
      = (CFC.sqrt S - σ • 1) * (CFC.sqrt S - σ • 1)
        + (2 * σ) • (CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    conv_lhs => rw [← hTT]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul,
      smul_sub]
    module
  rw [hsq, ← Matrix.nonneg_iff_posSemidef]
  exact add_nonneg (h0.isSelfAdjoint.mul_self_nonneg) (smul_nonneg (by positivity) h0)

/-- Converse: for `S ⪰ 0` and `σ ≥ 0`, `S - σ² 1 ⪰ 0` implies `σ 1 ≤ √S`.  Proof by an
eigenvector `w` of `√S - σ 1` with eigenvalue `μ`: `⟪√S w, w⟫ = μ + σ ≥ 0` and
`⟪(S - σ² 1) w, w⟫ = μ (μ + 2σ) ≥ 0`, hence `μ ≥ 0`. -/
theorem mvbe_le_sqrt_of_posSemidef_sub_sq {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef)
    {σ : ℝ} (h : (S - (σ ^ 2) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) :
    σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S := by
  have hT : (CFC.sqrt S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hTT : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
  have hM : (CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ)).IsHermitian :=
    hT.isHermitian.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all σ))
  have key : ∀ (w : Fin m → ℝ) (μ : ℝ),
      (CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ w = μ • w → w ⬝ᵥ w = 1 → 0 ≤ μ := by
    intro w μ hw hww
    have hTw : CFC.sqrt S *ᵥ w = (μ + σ) • w := by
      have h1 : CFC.sqrt S *ᵥ w
          = (CFC.sqrt S - σ • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ w + σ • w := by
        simp [sub_mulVec, smul_mulVec]
      rw [h1, hw, add_smul]
    have hSw : S *ᵥ w = ((μ + σ) ^ 2) • w := by
      rw [← hTT, ← mulVec_mulVec, hTw, mulVec_smul, hTw, smul_smul, sq]
    have h1 := hT.dotProduct_mulVec_nonneg w
    have h2 := h.dotProduct_mulVec_nonneg w
    simp only [star_trivial, hTw, sub_mulVec, hSw, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, hww, smul_eq_mul, mul_one] at h1 h2
    nlinarith
  rw [Matrix.le_iff, hM.posSemidef_iff_eigenvalues_nonneg]
  intro i
  refine key (WithLp.ofLp (hM.eigenvectorBasis i)) (hM.eigenvalues i)
    (hM.mulVec_eigenvectorBasis i) ?_
  rw [← mvbe_norm_sq_eq_dotProduct, (hM.eigenvectorBasis.orthonormal.1 i)]
  norm_num

/-- **Gaussian layer under general covariance, outer form, quadratic-form hypothesis.**
Raic's formulation: `S` symmetric with `σ² ‖v‖² ≤ ⟪S v, v⟫` for all `v`. -/
theorem mvbe_gaussian_layer_diff_le_of_quadForm (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsSymm)
    (hlow : ∀ v : EuclideanSpace ℝ (Fin m),
      σ ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (WithLp.toLp 2 (S *ᵥ WithLp.ofLp v)) v) :
    (multivariateGaussian μ S) (mvbeLayer C.rho A ε \ A)
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) :=
  mvbe_gaussian_layer_diff_le C hA hε μ hσ hσ1
    ((mvbe_posSemidef_sub_sq_smul_one_iff (mvbe_isHermitian_iff_isSymm.mpr hS) σ).mpr hlow)

/-- **Gaussian layer under general covariance, inner form, quadratic-form hypothesis.** -/
theorem mvbe_gaussian_diff_layer_le_of_quadForm (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsSymm)
    (hlow : ∀ v : EuclideanSpace ℝ (Fin m),
      σ ^ 2 * ‖v‖ ^ 2 ≤ inner ℝ (WithLp.toLp 2 (S *ᵥ WithLp.ofLp v)) v) :
    (multivariateGaussian μ S) (A \ mvbeLayer C.rho A (-ε))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) :=
  mvbe_gaussian_diff_layer_le C hA hε μ hσ hσ1
    ((mvbe_posSemidef_sub_sq_smul_one_iff (mvbe_isHermitian_iff_isSymm.mpr hS) σ).mpr hlow)

/-- **Gaussian layer under general covariance, outer form, `σ I ≤ Σ^{1/2}` hypothesis**
(the form in which Raic states the assumption on `Σ`). -/
theorem mvbe_gaussian_layer_diff_le_of_le_sqrt (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S) :
    (multivariateGaussian μ S) (mvbeLayer C.rho A ε \ A)
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) :=
  mvbe_gaussian_layer_diff_le C hA hε μ hσ hσ1
    (mvbe_posSemidef_sub_sq_of_le_sqrt hS hσ.le hsqrt)

/-- **Gaussian layer under general covariance, inner form, `σ I ≤ Σ^{1/2}` hypothesis.** -/
theorem mvbe_gaussian_diff_layer_le_of_le_sqrt (C : MvbeRegularClass m κ)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    (μ : EuclideanSpace ℝ (Fin m)) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {S : Matrix (Fin m) (Fin m) ℝ} (hS : S.PosSemidef)
    (hsqrt : σ • (1 : Matrix (Fin m) (Fin m) ℝ) ≤ CFC.sqrt S) :
    (multivariateGaussian μ S) (A \ mvbeLayer C.rho A (-ε))
      ≤ C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin m))) * ENNReal.ofReal (ε / σ) :=
  mvbe_gaussian_diff_layer_le C hA hε μ hσ hσ1
    (mvbe_posSemidef_sub_sq_of_le_sqrt hS hσ.le hsqrt)

end ClassLayer

end LatticeProb
