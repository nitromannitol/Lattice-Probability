import Mathlib

/-!
# Whitening: from the frozen multivariate Berry-Esseen shape to an identity-covariance bound

Packet P6 (item L14) of the staged formalisation of Raic, "A multivariate Berry-Esseen theorem
with explicit constants" (arXiv:1802.06475, Thm 1.3), orthant case.

## Statement

* `MvbeFrozenShape F`: the frozen `Sandpile.External.MultivariateBerryEsseen` with the factor
  `m ^ (1/4)` replaced by `F m` (vocabulary `gram`, `coeffNorm`, `quadForm` copied as `mvbeGram`,
  `mvbeCoeffNorm`, `mvbeQuadForm`).  `MvbeFrozenQuarter` is the frozen statement itself.
* `MvbeWhitenedBound F`: the abstract identity-covariance input.  For independent mean-zero
  `μ_i` on `ℝ^m` with `∑ Cov μ_i = I` and finite third moments, and for the set
  `A_{L,h} = {x | ∀ j, (L⁻¹ x) j ≤ h j} = L (O_h)`,
  `|P(∑ ω_i ∈ A_{L,h}) - γ(A_{L,h})| ≤ K F(m) ∑ E‖X_i‖³`.
  **Decision on the spectral condition.**  `L` is a parameter, restricted by exactly what the
  whitening `L = (√G)⁻¹` produces and what the image-class lemma needs: `L` positive definite
  (so symmetric and invertible), `‖L v‖² ≤ (1 - δ)⁻¹ ‖v‖²` and `‖L⁻¹ v‖² ≤ (1 + δ) ‖v‖²`
  (i.e. `‖L‖ ≤ (1-δ)^{-1/2}`, `‖L⁻¹‖ ≤ (1+δ)^{1/2}`).  The constant `K` depends on `δ` only.

## Proof (all steps are public lemmas)

(i) `mvbeGram_posDef`, `mvbe_sqrt_posDef`, `mvbe_sqrtInv_*`: spectral facts on `G`, `√G`,
`L = (√G)⁻¹`; (ii) `mvbeLaw_*`, `mvbe_cov_sum`, `mvbe_sum_third_moment_le`: the summands
`X_i = ξ_i • L a_i` (mean zero, covariance sum `L G L = I`, third moments); (iii) `mvbe_pi_map`,
`mvbe_pi_apply`, `mvbe_event_eq`: `Measure.pi ν` pushes forward to the law of the sum and the
events match; (iv) `mvbe_multivariateGaussian_orthant(_eq)`: `N(0,G){y ≤ h} = γ(A_{L,h})`;
(v) `mvbe_frozenShape_of_whitenedBound`: assembly, with `C = K M (√((1-δ)⁻¹))³`.
`mvbe_nonneg_of_whitenedBound` shows `0 ≤ F m` is forced by `MvbeWhitenedBound F`
(Rademacher witness), so the main theorem needs no sign hypothesis on `F`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder ENNReal

namespace LatticeProb

/-! ### Vocabulary (copied verbatim from the frozen file) -/

/-- The covariance matrix of the linear forms `Y_j = ∑_i a_i(j) ξ_i` (copy of `gram`). -/
noncomputable def mvbeGram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- The Euclidean norm of the `i`-th coefficient vector (copy of `coeffNorm`). -/
noncomputable def mvbeCoeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix (copy of `quadForm`). -/
noncomputable def mvbeQuadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

/-! ### The frozen shape and the whitened input -/

/-- **The frozen multivariate Berry-Esseen shape**, with the dimension factor `m ^ (1/4)` of
`Sandpile.External.MultivariateBerryEsseen` replaced by an abstract `F m`; everything else is the
frozen statement with the vocabulary `gram`, `coeffNorm`, `quadForm` renamed to `mvbe...`. -/
def MvbeFrozenShape (F : ℕ → ℝ) : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  mvbeQuadForm (mvbeGram ν a) v ∧
                mvbeQuadForm (mvbeGram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (mvbeGram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * F m * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, mvbeCoeffNorm a i ^ 3

/-- The frozen statement itself (`C * m ^ (1/4)`), in the vocabulary of this file: textually the
frozen `Sandpile.External.MultivariateBerryEsseen` with `gram`, `coeffNorm`, `quadForm` renamed
to `mvbeGram`, `mvbeCoeffNorm`, `mvbeQuadForm`. -/
def MvbeFrozenQuarter : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  mvbeQuadForm (mvbeGram ν a) v ∧
                mvbeQuadForm (mvbeGram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (mvbeGram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, mvbeCoeffNorm a i ^ 3

/-- `MvbeFrozenQuarter` is `MvbeFrozenShape` at `F m = m ^ (1/4)`. -/
theorem mvbeFrozenQuarter_iff :
    MvbeFrozenQuarter ↔ MvbeFrozenShape (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4)) :=
  Iff.rfl

/-- The image `A_{L,h} = L (O_h)` of the orthant `O_h = {y | ∀ j, y j ≤ h j}` under an invertible
matrix `L`, written as the preimage `{x | ∀ j, (L⁻¹ x) j ≤ h j}`. -/
def mvbeOrthantImage {m : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) (h : Fin m → ℝ) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∀ j, (L⁻¹ *ᵥ x.ofLp) j ≤ h j}

/-- **The abstract whitened input.**  A Berry-Esseen bound for sums `W = ∑ X_i` of independent
mean-zero vectors in `ℝ^m` with identity covariance, over the sets `A_{L,h} = L (O_h)`, with
the linear dependence `K * F m * ∑ E‖X_i‖³` on the third moments.  The matrix `L` is the
whitening matrix `(√G)⁻¹` of a Gram matrix with spectral window `[1 - δ, 1 + δ]`; this enters
through its exact consequences: `L` is symmetric positive definite, `‖L v‖² ≤ (1 - δ)⁻¹ ‖v‖²`
and `‖L⁻¹ v‖² ≤ (1 + δ) ‖v‖²`. -/
def MvbeWhitenedBound (F : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ K : ℝ, 0 < K ∧
      ∀ (m n : ℕ), 1 ≤ m →
        ∀ (μ : Fin n → Measure (EuclideanSpace ℝ (Fin m)))
          [∀ i, IsProbabilityMeasure (μ i)],
          (∀ i, Integrable (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖ ^ 3) (μ i)) →
          (∀ i, ∫ x, x ∂μ i = 0) →
          (∀ u v : EuclideanSpace ℝ (Fin m),
            ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂μ i = inner ℝ u v) →
          ∀ L : Matrix (Fin m) (Fin m) ℝ, L.PosDef →
            (∀ v : Fin m → ℝ, ∑ j, (L *ᵥ v) j ^ 2 ≤ (1 - δ)⁻¹ * ∑ j, v j ^ 2) →
            (∀ v : Fin m → ℝ, ∑ j, (L⁻¹ *ᵥ v) j ^ 2 ≤ (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi μ) {ω | (∑ i, ω i) ∈ mvbeOrthantImage L h}).toReal -
                  (stdGaussian (EuclideanSpace ℝ (Fin m)) (mvbeOrthantImage L h)).toReal| ≤
                K * F m * ∑ i, ∫ x, ‖x‖ ^ 3 ∂μ i

/-! ### Part (i): the spectral bounds on `G`, `√G` and `L = (√G)⁻¹` -/

section Spectral

variable {m : ℕ}

/-- The quadratic form is `v ⬝ᵥ S *ᵥ v`. -/
theorem mvbeQuadForm_eq_dotProduct (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    mvbeQuadForm S v = v ⬝ᵥ (S *ᵥ v) := by
  unfold mvbeQuadForm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The sum of squares `∑ j, v j ^ 2` is `v ⬝ᵥ v`. -/
theorem mvbe_sum_sq_eq_dotProduct (v : Fin m → ℝ) : ∑ j, v j ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

/-- The Gram matrix is symmetric. -/
theorem mvbeGram_transpose {N : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    (mvbeGram ν a)ᵀ = mvbeGram ν a := by
  ext j k
  simp only [mvbeGram, transpose_apply, Matrix.of_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A symmetric matrix whose quadratic form is bounded below by `(1 - δ) ‖v‖²`, `δ < 1`, is
positive definite. -/
theorem mvbe_posDef_of_quadForm_lower {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hGt : Gᵀ = G)
    (hlow : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v) : G.PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · show Gᴴ = G
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hGt
  · have h1 := hlow v
    rw [mvbeQuadForm_eq_dotProduct] at h1
    have hpos : 0 < ∑ j, v j ^ 2 := by
      rw [mvbe_sum_sq_eq_dotProduct]
      exact lt_of_le_of_ne (dotProduct_self_star_nonneg v) (fun h => hv (by
        simpa [dotProduct_self_eq_zero] using h.symm))
    have h2 : 0 < (1 - δ) * ∑ j, v j ^ 2 := mul_pos (by linarith) hpos
    simpa using lt_of_lt_of_le h2 h1

/-- The Gram matrix of a one-site law with the frozen quadratic-form bounds is positive
definite (only the lower bound is used). -/
theorem mvbeGram_posDef {N : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) {δ : ℝ} (hδ : δ < 1)
    (hlow : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm (mvbeGram ν a) v) :
    (mvbeGram ν a).PosDef :=
  mvbe_posDef_of_quadForm_lower hδ (mvbeGram_transpose ν a) hlow

/-- The square root of a positive semidefinite matrix is symmetric. -/
theorem mvbe_sqrt_transpose {G : Matrix (Fin m) (Fin m) ℝ} :
    (CFC.sqrt G)ᵀ = CFC.sqrt G := by
  have hher : (CFC.sqrt G).IsHermitian := (CFC.sqrt_nonneg G).isSelfAdjoint.isHermitian
  ext i j
  have h := congr_fun (congr_fun hher i) j
  simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h

/-- `‖√G v‖² = v ⬝ᵥ G v` for positive semidefinite `G`. -/
theorem mvbe_sqrt_mulVec_sq {G : Matrix (Fin m) (Fin m) ℝ} (hG : G.PosSemidef)
    (v : Fin m → ℝ) :
    ∑ j, (CFC.sqrt G *ᵥ v) j ^ 2 = v ⬝ᵥ (G *ᵥ v) := by
  rw [mvbe_sum_sq_eq_dotProduct]
  have h1 : (CFC.sqrt G *ᵥ v) ⬝ᵥ (CFC.sqrt G *ᵥ v) = (G *ᵥ v) ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mvbe_sqrt_transpose, mulVec_mulVec,
      CFC.sqrt_mul_sqrt_self G hG.nonneg]
  rw [h1, dotProduct_comm]

/-- Two-sided quadratic-form bounds on `G` transfer to `‖√G v‖²`. -/
theorem mvbe_sqrt_sq_bounds {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) (v : Fin m → ℝ) :
    (1 - δ) * ∑ j, v j ^ 2 ≤ ∑ j, (CFC.sqrt G *ᵥ v) j ^ 2 ∧
      ∑ j, (CFC.sqrt G *ᵥ v) j ^ 2 ≤ (1 + δ) * ∑ j, v j ^ 2 := by
  rw [mvbe_sqrt_mulVec_sq hG]
  have := hq v
  rwa [mvbeQuadForm_eq_dotProduct] at this

/-- Under the frozen quadratic-form bounds, `√G` is positive definite. -/
theorem mvbe_sqrt_posDef {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) : (CFC.sqrt G).PosDef := by
  have hS : (CFC.sqrt G).PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hS.isHermitian, fun v hv => ?_⟩
  refine lt_of_le_of_ne (hS.dotProduct_mulVec_nonneg v) (fun h0 => ?_)
  have hz : CFC.sqrt G *ᵥ v = 0 := (hS.dotProduct_mulVec_zero_iff v).1 h0.symm
  have h1 := (mvbe_sqrt_sq_bounds hG hq v).1
  have h2 : ∑ j, (CFC.sqrt G *ᵥ v) j ^ 2 = 0 := by simp [hz]
  have hpos : 0 < ∑ j, v j ^ 2 := by
    rw [mvbe_sum_sq_eq_dotProduct]
    exact lt_of_le_of_ne (dotProduct_self_star_nonneg v) (fun h => hv (by
      simpa [dotProduct_self_eq_zero] using h.symm))
  have h3 : 0 < (1 - δ) * ∑ j, v j ^ 2 := mul_pos (by linarith) hpos
  linarith

/-- The whitening matrix `L = (√G)⁻¹` is positive definite. -/
theorem mvbe_sqrtInv_posDef {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) : (CFC.sqrt G)⁻¹.PosDef :=
  (mvbe_sqrt_posDef hδ hG hq).inv

/-- The inverse of the whitening matrix is `√G`. -/
theorem mvbe_sqrtInv_inv {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) : (CFC.sqrt G)⁻¹⁻¹ = CFC.sqrt G :=
  nonsing_inv_nonsing_inv _
    ((isUnit_iff_isUnit_det _).1 (mvbe_sqrt_posDef hδ hG hq).isUnit)

/-- `‖L v‖² ≤ (1 - δ)⁻¹ ‖v‖²` for `L = (√G)⁻¹`: the operator-norm bound on the whitening
matrix. -/
theorem mvbe_sqrtInv_sq_le {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) (v : Fin m → ℝ) :
    ∑ j, ((CFC.sqrt G)⁻¹ *ᵥ v) j ^ 2 ≤ (1 - δ)⁻¹ * ∑ j, v j ^ 2 := by
  have hdet : IsUnit (CFC.sqrt G).det :=
    (isUnit_iff_isUnit_det _).1 (mvbe_sqrt_posDef hδ hG hq).isUnit
  have hv : CFC.sqrt G *ᵥ ((CFC.sqrt G)⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have h := (mvbe_sqrt_sq_bounds hG hq ((CFC.sqrt G)⁻¹ *ᵥ v)).1
  rw [hv] at h
  exact (le_inv_mul_iff₀ (by linarith)).2 h

/-- `‖L⁻¹ v‖² ≤ (1 + δ) ‖v‖²` for `L = (√G)⁻¹`. -/
theorem mvbe_sqrtInv_inv_sq_le {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) (v : Fin m → ℝ) :
    ∑ j, ((CFC.sqrt G)⁻¹⁻¹ *ᵥ v) j ^ 2 ≤ (1 + δ) * ∑ j, v j ^ 2 := by
  rw [mvbe_sqrtInv_inv hδ hG hq]
  exact (mvbe_sqrt_sq_bounds hG hq v).2

/-- The whitening identity `L G L = 1` for `L = (√G)⁻¹`. -/
theorem mvbe_sqrtInv_mul_mul {G : Matrix (Fin m) (Fin m) ℝ} {δ : ℝ} (hδ : δ < 1)
    (hG : G.PosSemidef)
    (hq : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm G v ∧
      mvbeQuadForm G v ≤ (1 + δ) * ∑ j, v j ^ 2) :
    (CFC.sqrt G)⁻¹ * G * (CFC.sqrt G)⁻¹ = 1 := by
  have hdet : IsUnit (CFC.sqrt G).det :=
    (isUnit_iff_isUnit_det _).1 (mvbe_sqrt_posDef hδ hG hq).isUnit
  have hGS : CFC.sqrt G * CFC.sqrt G = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  calc (CFC.sqrt G)⁻¹ * G * (CFC.sqrt G)⁻¹
      = (CFC.sqrt G)⁻¹ * (CFC.sqrt G * CFC.sqrt G) * (CFC.sqrt G)⁻¹ := by rw [hGS]
    _ = ((CFC.sqrt G)⁻¹ * CFC.sqrt G) * (CFC.sqrt G * (CFC.sqrt G)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul _ hdet, mul_nonsing_inv _ hdet, Matrix.mul_one]

end Spectral

/-! ### Part (ii): the whitened summand laws `μ_i = ν.map (z ↦ z • b_i)` -/

section Law

variable {m : ℕ}

/-- The inner product on `EuclideanSpace ℝ (Fin m)` is the dot product of coordinates. -/
theorem mvbe_inner_eq (x y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The law of `ξ • b` when `ξ ∼ ν`: the pushforward of a one-site law along `z ↦ z • b`. -/
noncomputable def mvbeLaw (ν : Measure ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    Measure (EuclideanSpace ℝ (Fin m)) :=
  ν.map (fun z : ℝ => z • b)

theorem measurable_mvbe_smul (b : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun z : ℝ => z • b) :=
  (continuous_id.smul continuous_const).measurable

instance mvbeLaw_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (b : EuclideanSpace ℝ (Fin m)) : IsProbabilityMeasure (mvbeLaw ν b) :=
  Measure.isProbabilityMeasure_map (measurable_mvbe_smul b).aemeasurable

/-- The summand `ξ • b` has mean zero when `ξ` does. -/
theorem mvbeLaw_integral_id (ν : Measure ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hmean : ∫ z, z ∂ν = 0) : ∫ x, x ∂(mvbeLaw ν b) = 0 := by
  unfold mvbeLaw
  rw [integral_map (f := fun x : EuclideanSpace ℝ (Fin m) => x)
    (measurable_mvbe_smul b).aemeasurable aestronglyMeasurable_id]
  rw [integral_smul_const, hmean, zero_smul]

/-- The third absolute moment of `ξ • b` is `E|ξ|³ ‖b‖³`. -/
theorem mvbeLaw_integral_norm_cube (ν : Measure ℝ) (b : EuclideanSpace ℝ (Fin m)) :
    ∫ x, ‖x‖ ^ 3 ∂(mvbeLaw ν b) = (∫ z, |z| ^ 3 ∂ν) * ‖b‖ ^ 3 := by
  unfold mvbeLaw
  rw [integral_map (measurable_mvbe_smul b).aemeasurable (by fun_prop)]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [norm_smul, mul_pow]

/-- The summand `ξ • b` has an integrable third moment when `ξ` does. -/
theorem mvbeLaw_integrable_norm_cube (ν : Measure ℝ) (b : EuclideanSpace ℝ (Fin m))
    (hint : Integrable (fun z : ℝ => |z| ^ 3) ν) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖ ^ 3) (mvbeLaw ν b) := by
  unfold mvbeLaw
  rw [integrable_map_measure (by fun_prop) (measurable_mvbe_smul b).aemeasurable]
  have : ((fun x : EuclideanSpace ℝ (Fin m) => ‖x‖ ^ 3) ∘ fun z : ℝ => z • b)
      = fun z : ℝ => |z| ^ 3 * ‖b‖ ^ 3 := by
    funext z
    simp [norm_smul, mul_pow]
  rw [this]
  exact hint.mul_const _

/-- The second moments of `ξ • b`: `E⟨ξ b, u⟩⟨ξ b, v⟩ = E ξ² ⟨b, u⟩⟨b, v⟩`. -/
theorem mvbeLaw_integral_inner_mul (ν : Measure ℝ) (b u v : EuclideanSpace ℝ (Fin m)) :
    ∫ x, inner ℝ x u * inner ℝ x v ∂(mvbeLaw ν b)
      = (∫ z, z ^ 2 ∂ν) * (inner ℝ b u * inner ℝ b v) := by
  unfold mvbeLaw
  rw [integral_map (measurable_mvbe_smul b).aemeasurable (by fun_prop)]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [real_inner_smul_left]
  ring

/-- The whitened coefficient vector `L a_i`, as a point of `EuclideanSpace ℝ (Fin m)`. -/
noncomputable def mvbeVec {N : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) (a : Fin N → Fin m → ℝ)
    (i : Fin N) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (L *ᵥ a i)

/-- For a symmetric matrix `L`, `⟨Lx, y⟩ = ⟨x, Ly⟩` in dot-product form. -/
theorem mvbe_dotProduct_mulVec_symm {L : Matrix (Fin m) (Fin m) ℝ} (hL : Lᵀ = L)
    (x y : Fin m → ℝ) : (L *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (L *ᵥ y) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hL]

/-- The Gram quadratic form as a sum over the coordinates:
`p ⬝ᵥ G q = Var ν ∑_i ⟨a_i, p⟩⟨a_i, q⟩`. -/
theorem mvbe_dotProduct_gram_mulVec {N : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ)
    (p q : Fin m → ℝ) :
    p ⬝ᵥ (mvbeGram ν a *ᵥ q) = ∑ i, variance id ν * ((a i ⬝ᵥ p) * (a i ⬝ᵥ q)) := by
  have h1 : p ⬝ᵥ (mvbeGram ν a *ᵥ q)
      = ∑ j, ∑ k, ∑ i, variance id ν * ((a i j * p j) * (a i k * q k)) := by
    simp only [dotProduct, Matrix.mulVec, mvbeGram, Matrix.of_apply, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∑ i, variance id ν * ((a i ⬝ᵥ p) * (a i ⬝ᵥ q))
      = ∑ i, ∑ j, ∑ k, variance id ν * ((a i j * p j) * (a i k * q k)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dotProduct]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  rw [h1, h2]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_comm

/-- The covariance sum of the whitened summands: if `L G L = 1`, `L` symmetric, `G` the Gram
matrix of `ν` and `a`, then `∑_i E⟨X_i,u⟩⟨X_i,v⟩ = ⟨u,v⟩` for `X_i = ξ_i • L a_i`. -/
theorem mvbe_cov_sum {N : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hLt : Lᵀ = L) (hLGL : L * mvbeGram ν a * L = 1)
    (hvar : ∫ z, z ^ 2 ∂ν = variance id ν) (u v : EuclideanSpace ℝ (Fin m)) :
    ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂(mvbeLaw ν (mvbeVec L a i))
      = inner ℝ u v := by
  simp_rw [mvbeLaw_integral_inner_mul, hvar]
  have key : ∀ (i : Fin N) (w : EuclideanSpace ℝ (Fin m)),
      inner ℝ (mvbeVec L a i) w = a i ⬝ᵥ (L *ᵥ w.ofLp) := by
    intro i w
    rw [mvbe_inner_eq]
    exact mvbe_dotProduct_mulVec_symm hLt _ _
  simp_rw [key]
  rw [← mvbe_dotProduct_gram_mulVec, mvbe_dotProduct_mulVec_symm hLt, mulVec_mulVec,
    mulVec_mulVec, hLGL, one_mulVec, mvbe_inner_eq]

/-- The Euclidean norm of a vector of coordinates. -/
theorem mvbe_whiten_norm_toLp (y : Fin m → ℝ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin m))‖ = Real.sqrt (∑ j, y j ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The whitened coefficient vector satisfies `‖L a_i‖ ≤ √c₀ |a_i|`. -/
theorem mvbe_norm_mvbeVec_le {N : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) (a : Fin N → Fin m → ℝ)
    {c0 : ℝ} (hc0 : 0 ≤ c0) (hL : ∀ v : Fin m → ℝ, ∑ j, (L *ᵥ v) j ^ 2 ≤ c0 * ∑ j, v j ^ 2)
    (i : Fin N) : ‖mvbeVec L a i‖ ≤ Real.sqrt c0 * mvbeCoeffNorm a i := by
  unfold mvbeVec mvbeCoeffNorm
  rw [mvbe_whiten_norm_toLp, ← Real.sqrt_mul hc0]
  exact Real.sqrt_le_sqrt (hL (a i))

/-- The total third moment of the whitened summands is at most
`B (√c₀)³ ∑_i |a_i|³` when `E|ξ|³ ≤ B`. -/
theorem mvbe_sum_third_moment_le {N : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ)
    (L : Matrix (Fin m) (Fin m) ℝ) {c0 B : ℝ} (hc0 : 0 ≤ c0)
    (hL : ∀ v : Fin m → ℝ, ∑ j, (L *ᵥ v) j ^ 2 ≤ c0 * ∑ j, v j ^ 2)
    (hB : ∫ z, |z| ^ 3 ∂ν ≤ B) :
    ∑ i, ∫ x, ‖x‖ ^ 3 ∂(mvbeLaw ν (mvbeVec L a i))
      ≤ B * Real.sqrt c0 ^ 3 * ∑ i, mvbeCoeffNorm a i ^ 3 := by
  have hI : 0 ≤ ∫ z, |z| ^ 3 ∂ν := integral_nonneg fun z => by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mvbeLaw_integral_norm_cube]
  have h1 : ‖mvbeVec L a i‖ ^ 3 ≤ (Real.sqrt c0 * mvbeCoeffNorm a i) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) (mvbe_norm_mvbeVec_le L a hc0 hL i) 3
  calc (∫ z, |z| ^ 3 ∂ν) * ‖mvbeVec L a i‖ ^ 3
      ≤ B * (Real.sqrt c0 * mvbeCoeffNorm a i) ^ 3 :=
        mul_le_mul hB h1 (by positivity) (hI.trans hB)
    _ = B * Real.sqrt c0 ^ 3 * mvbeCoeffNorm a i ^ 3 := by ring

end Law

/-! ### Part (iii): the product measure pushes forward to the product of the whitened laws -/

section Pushforward

variable {m N : ℕ}

/-- `Measure.pi ν` pushes forward, along `ξ ↦ (ξ_i • b_i)_i`, to the product of the laws
`ν.map (· • b_i)`. -/
theorem mvbe_pi_map (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (b : Fin N → EuclideanSpace ℝ (Fin m)) :
    (Measure.pi fun _ : Fin N => ν).map (fun (ξ : Fin N → ℝ) i => ξ i • b i)
      = Measure.pi fun i => mvbeLaw ν (b i) := by
  haveI : ∀ i, SigmaFinite (ν.map (fun z : ℝ => z • b i)) := fun i =>
    (inferInstance : SigmaFinite (mvbeLaw ν (b i)))
  exact Measure.pi_map_pi (μ := fun _ : Fin N => ν) (f := fun i (z : ℝ) => z • b i)
    (fun i => (measurable_mvbe_smul (b i)).aemeasurable)

/-- Probabilities of events of the sum under `Measure.pi` of the whitened laws are probabilities
of the corresponding events of the coordinate vector `ξ` under `Measure.pi ν`. -/
theorem mvbe_pi_apply (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (b : Fin N → EuclideanSpace ℝ (Fin m)) {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA : MeasurableSet A) :
    (Measure.pi fun i => mvbeLaw ν (b i)) {ω | (∑ i, ω i) ∈ A}
      = (Measure.pi fun _ : Fin N => ν) {ξ | (∑ i, ξ i • b i) ∈ A} := by
  rw [← mvbe_pi_map ν b]
  have hmeas : Measurable (fun (ξ : Fin N → ℝ) i => ξ i • b i) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).smul_const (b i)
  have hS : MeasurableSet {ω : Fin N → EuclideanSpace ℝ (Fin m) | (∑ i, ω i) ∈ A} :=
    hA.preimage (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  rw [Measure.map_apply hmeas hS]
  rfl

end Pushforward

/-! ### Part (iii'): the events correspond; part (iv): the Gaussian side -/

section Events

variable {m N : ℕ}

/-- The set `A_{L,h}` is closed, hence measurable. -/
theorem measurableSet_mvbeOrthantImage (L : Matrix (Fin m) (Fin m) ℝ) (h : Fin m → ℝ) :
    MeasurableSet (mvbeOrthantImage L h) := by
  unfold mvbeOrthantImage
  rw [Set.setOf_forall]
  refine MeasurableSet.iInter fun j => ?_
  refine measurableSet_le ?_ measurable_const
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

/-- For invertible `L`, `A_{L,h}` is the image `L (O_h)` of the orthant. -/
theorem mvbeOrthantImage_eq_image {L : Matrix (Fin m) (Fin m) ℝ} (hL : IsUnit L.det)
    (h : Fin m → ℝ) :
    mvbeOrthantImage L h
      = (fun y => toEuclideanCLM (𝕜 := ℝ) L y) ''
          {y : EuclideanSpace ℝ (Fin m) | ∀ j, y j ≤ h j} := by
  ext x
  constructor
  · intro hx
    refine ⟨toEuclideanCLM (𝕜 := ℝ) L⁻¹ x, fun j => hx j, ?_⟩
    apply WithLp.ofLp_injective
    simp [mulVec_mulVec, mul_nonsing_inv _ hL]
  · rintro ⟨y, hy, rfl⟩ j
    simpa [mulVec_mulVec, nonsing_inv_mul _ hL] using hy j

/-- The event `{∑ ξ_i L a_i ∈ A_{L,h}}` is the event `{∀ j, ∑ a_i(j) ξ_i ≤ h_j}`. -/
theorem mvbe_event_eq (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det)
    (a : Fin N → Fin m → ℝ) (h : Fin m → ℝ) (ξ : Fin N → ℝ) :
    (∑ i, ξ i • mvbeVec L a i) ∈ mvbeOrthantImage L h ↔ ∀ j, ∑ i, a i j * ξ i ≤ h j := by
  have hsum : L⁻¹ *ᵥ (∑ i, ξ i • mvbeVec L a i).ofLp = ∑ i, ξ i • a i := by
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, mvbeVec, mulVec_sum,
      mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hL, one_mulVec]
  unfold mvbeOrthantImage
  simp only [Set.mem_setOf_eq, hsum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine forall_congr' fun j => ?_
  simp only [mul_comm]

/-- **The Gaussian side**: `N(0, S)` of the orthant is the standard Gaussian of the pullback
`{x | ∀ j, (√S x) j ≤ h j}`. -/
theorem mvbe_multivariateGaussian_orthant (S : Matrix (Fin m) (Fin m) ℝ) (h : Fin m → ℝ) :
    multivariateGaussian 0 S {y | ∀ j, y j ≤ h j}
      = stdGaussian (EuclideanSpace ℝ (Fin m)) {x | ∀ j, (CFC.sqrt S *ᵥ x.ofLp) j ≤ h j} := by
  have hmap : multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
      = (stdGaussian (EuclideanSpace ℝ (Fin m))).map
          (fun x => toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) := by
    simp [multivariateGaussian]
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin m) =>
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) :=
    (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).continuous.measurable
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | ∀ j, y j ≤ h j} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  rw [hmap, Measure.map_apply hmeas hS]
  rfl

/-- The Gaussian side in the notation of `MvbeWhitenedBound`: for `L = (√G)⁻¹`,
`N(0, G){y ≤ h} = γ(A_{L,h})`. -/
theorem mvbe_multivariateGaussian_orthant_eq {G : Matrix (Fin m) (Fin m) ℝ}
    (hdet : IsUnit (CFC.sqrt G).det) (h : Fin m → ℝ) :
    multivariateGaussian 0 G {y | ∀ j, y j ≤ h j}
      = stdGaussian (EuclideanSpace ℝ (Fin m)) (mvbeOrthantImage (CFC.sqrt G)⁻¹ h) := by
  rw [mvbe_multivariateGaussian_orthant, mvbeOrthantImage, nonsing_inv_nonsing_inv _ hdet]

end Events

/-! ### The sign of `F` is forced by the whitened bound -/

section Sign

/-- The symmetric Bernoulli law on `{1, -1}` (used only to exhibit one admissible family of
summands, to extract `0 ≤ F m` from `MvbeWhitenedBound F`). -/
noncomputable def mvbeRademacher : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

instance mvbeRademacher_isProbabilityMeasure : IsProbabilityMeasure mvbeRademacher :=
  ⟨by
    simp only [mvbeRademacher, Measure.smul_apply, Measure.add_apply, MeasurableSet.univ,
      Measure.dirac_apply', Set.indicator_univ, Pi.one_apply, smul_eq_mul]
    rw [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

theorem mvbeRademacher_integrable (f : ℝ → ℝ) : Integrable f mvbeRademacher := by
  unfold mvbeRademacher
  refine Integrable.smul_measure (Integrable.add_measure ?_ ?_) (by norm_num)
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

theorem mvbeRademacher_integral (f : ℝ → ℝ) :
    ∫ x, f x ∂mvbeRademacher = (f 1 + f (-1)) / 2 := by
  unfold mvbeRademacher
  rw [integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- The identity matrix is positive definite. -/
theorem mvbe_posDef_one (m : ℕ) : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef := by
  have := Matrix.PosDef.diagonal (n := Fin m) (d := fun _ => (1 : ℝ)) (fun _ => one_pos)
  simpa using this

/-- **The sign of `F` is forced.**  If `MvbeWhitenedBound F` holds then `F m ≥ 0` for `m ≥ 1`:
the Rademacher summands `ξ_i e_i` (`i < m`) are admissible and have total third moment `m > 0`,
while the left side of the bound is non-negative. -/
theorem mvbe_nonneg_of_whitenedBound (F : ℕ → ℝ) (hW : MvbeWhitenedBound F) (m : ℕ)
    (hm : 1 ≤ m) : 0 ≤ F m := by
  obtain ⟨K, hK, hKb⟩ := hW (1 / 2) (by norm_num) (by norm_num)
  have hI2 : ∫ z, z ^ 2 ∂mvbeRademacher = 1 := by
    rw [mvbeRademacher_integral]; norm_num
  have hI3 : ∫ z, |z| ^ 3 ∂mvbeRademacher = 1 := by
    rw [mvbeRademacher_integral]; norm_num
  have hI1 : ∫ z, z ∂mvbeRademacher = 0 := by
    rw [mvbeRademacher_integral]; norm_num
  have hbound := hKb m m hm (fun i => mvbeLaw mvbeRademacher (EuclideanSpace.single i (1 : ℝ)))
    (fun i => mvbeLaw_integrable_norm_cube _ _ (mvbeRademacher_integrable _))
    (fun i => mvbeLaw_integral_id _ _ hI1)
    (fun u v => by
      simp_rw [mvbeLaw_integral_inner_mul, hI2, EuclideanSpace.inner_single_left]
      simp only [one_mul, map_one, mvbe_inner_eq, dotProduct])
    1 (mvbe_posDef_one m)
    (fun v => by
      have : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      simp only [Matrix.one_mulVec]
      have h2 : (1 - 1 / 2 : ℝ)⁻¹ = 2 := by norm_num
      rw [h2]
      linarith)
    (fun v => by
      have : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      simp only [inv_one, Matrix.one_mulVec]
      linarith)
    (fun _ => 0)
  have hT : ∑ i : Fin m, ∫ x, ‖x‖ ^ 3 ∂(mvbeLaw mvbeRademacher (EuclideanSpace.single i (1 : ℝ)))
      = (m : ℝ) := by
    simp [mvbeLaw_integral_norm_cube, hI3]
  rw [hT] at hbound
  have h0 : 0 ≤ K * F m * (m : ℝ) := le_trans (abs_nonneg _) hbound
  by_contra hneg0
  have hneg : F m < 0 := not_le.mp hneg0
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have : K * F m * (m : ℝ) < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hK hneg) hm0
  linarith

end Sign

/-! ### Part (v): assembly -/

section Assembly

/-- **Whitening reduction, conditional on the sign of `F`.** The whitened identity-covariance
bound `MvbeWhitenedBound F` implies the frozen shape `MvbeFrozenShape F`, with
`C = K M (√((1 - δ)⁻¹))³`, provided `F m ≥ 0` for `m ≥ 1`. -/
theorem mvbe_frozenShape_of_whitenedBound_of_nonneg (F : ℕ → ℝ) (hF : ∀ m, 1 ≤ m → 0 ≤ F m)
    (hW : MvbeWhitenedBound F) : MvbeFrozenShape F := by
  intro M δ hM hδ0 hδ1
  obtain ⟨K, hK, hKb⟩ := hW δ hδ0 hδ1
  have hc0 : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.2 (by linarith)
  refine ⟨K * M * Real.sqrt ((1 - δ)⁻¹) ^ 3, by positivity, ?_⟩
  intro N m hm ν hνprob hmean hvar hint hmom a hq h
  haveI := hνprob
  have hlow : ∀ v : Fin m → ℝ, (1 - δ) * ∑ j, v j ^ 2 ≤ mvbeQuadForm (mvbeGram ν a) v :=
    fun v => (hq v).1
  have hGpd : (mvbeGram ν a).PosDef := mvbeGram_posDef ν a hδ1 hlow
  have hGps : (mvbeGram ν a).PosSemidef := hGpd.posSemidef
  have hSpd : (CFC.sqrt (mvbeGram ν a)).PosDef := mvbe_sqrt_posDef hδ1 hGps hq
  have hdetS : IsUnit (CFC.sqrt (mvbeGram ν a)).det :=
    (isUnit_iff_isUnit_det _).1 hSpd.isUnit
  have hLpd : (CFC.sqrt (mvbeGram ν a))⁻¹.PosDef := hSpd.inv
  have hLt : ((CFC.sqrt (mvbeGram ν a))⁻¹)ᵀ = (CFC.sqrt (mvbeGram ν a))⁻¹ :=
    hLpd.isHermitian.eq
  have hdetL : IsUnit ((CFC.sqrt (mvbeGram ν a))⁻¹).det :=
    (isUnit_iff_isUnit_det _).1 hLpd.isUnit
  have hvar' : ∫ z, z ^ 2 ∂ν = variance id ν :=
    (variance_of_integral_eq_zero (X := id) aemeasurable_id hmean).symm
  have hbound := hKb m N hm (fun i => mvbeLaw ν (mvbeVec (CFC.sqrt (mvbeGram ν a))⁻¹ a i))
    (fun i => mvbeLaw_integrable_norm_cube ν _ hint)
    (fun i => mvbeLaw_integral_id ν _ hmean)
    (fun u v => mvbe_cov_sum ν a _ hLt (mvbe_sqrtInv_mul_mul hδ1 hGps hq) hvar' u v)
    (CFC.sqrt (mvbeGram ν a))⁻¹ hLpd (mvbe_sqrtInv_sq_le hδ1 hGps hq)
    (mvbe_sqrtInv_inv_sq_le hδ1 hGps hq) h
  have hP : ((Measure.pi fun i => mvbeLaw ν (mvbeVec (CFC.sqrt (mvbeGram ν a))⁻¹ a i))
        {ω | (∑ i, ω i) ∈ mvbeOrthantImage (CFC.sqrt (mvbeGram ν a))⁻¹ h})
      = (Measure.pi fun _ : Fin N => ν) {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j} := by
    rw [mvbe_pi_apply ν _ (measurableSet_mvbeOrthantImage _ h)]
    congr 1
    ext ξ
    exact mvbe_event_eq _ hdetL a h ξ
  rw [hP, ← mvbe_multivariateGaussian_orthant_eq hdetS h] at hbound
  refine hbound.trans ?_
  have hmom' := mvbe_sum_third_moment_le ν a (CFC.sqrt (mvbeGram ν a))⁻¹ hc0
    (mvbe_sqrtInv_sq_le hδ1 hGps hq) hmom
  have hKF : 0 ≤ K * F m := mul_nonneg hK.le (hF m hm)
  calc K * F m * ∑ i, ∫ x, ‖x‖ ^ 3 ∂(mvbeLaw ν (mvbeVec (CFC.sqrt (mvbeGram ν a))⁻¹ a i))
      ≤ K * F m * (M * variance id ν ^ ((3 : ℝ) / 2) * Real.sqrt ((1 - δ)⁻¹) ^ 3 *
          ∑ i, mvbeCoeffNorm a i ^ 3) := mul_le_mul_of_nonneg_left hmom' hKF
    _ = K * M * Real.sqrt ((1 - δ)⁻¹) ^ 3 * F m * variance id ν ^ ((3 : ℝ) / 2) *
          ∑ i, mvbeCoeffNorm a i ^ 3 := by ring

/-- **Main theorem (item L14).**  The whitened identity-covariance bound with dimension factor
`F` implies the frozen multivariate Berry-Esseen shape with the same `F`; the constant is
`C = K M (√((1 - δ)⁻¹))³`, where `K = K(δ)` comes from the whitened bound.  No sign hypothesis on
`F` is needed: `0 ≤ F m` (`m ≥ 1`) is itself a consequence of the whitened bound
(`mvbe_nonneg_of_whitenedBound`). -/
theorem mvbe_frozenShape_of_whitenedBound (F : ℕ → ℝ) (h : MvbeWhitenedBound F) :
    MvbeFrozenShape F :=
  mvbe_frozenShape_of_whitenedBound_of_nonneg F (mvbe_nonneg_of_whitenedBound F h) h

/-- The whitened bound with `F m = m ^ (1/4)` gives the frozen shape with `C * m ^ (1/4)`. -/
theorem mvbe_frozenShape_quarter_of_whitenedBound
    (h : MvbeWhitenedBound (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4))) :
    MvbeFrozenShape (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4)) :=
  mvbe_frozenShape_of_whitenedBound _ h

/-- The whitened bound with `F m = m ^ (1/4)` gives the frozen statement itself (in the
vocabulary of this file): `Sandpile.External.MultivariateBerryEsseen`. -/
theorem mvbe_frozenQuarter_of_whitenedBound
    (h : MvbeWhitenedBound (fun m : ℕ => (m : ℝ) ^ ((1 : ℝ) / 4))) : MvbeFrozenQuarter :=
  mvbe_frozenShape_of_whitenedBound _ h

/-- The whitened bound with `F m = m` (the linear-in-dimension Stage 1 form) gives the frozen
shape with `C * m`. -/
theorem mvbe_frozenShape_linear_of_whitenedBound
    (h : MvbeWhitenedBound (fun m : ℕ => (m : ℝ))) :
    MvbeFrozenShape (fun m : ℕ => (m : ℝ)) :=
  mvbe_frozenShape_of_whitenedBound _ h

end Assembly

end LatticeProb
