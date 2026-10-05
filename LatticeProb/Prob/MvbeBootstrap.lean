import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeClassLayer
import LatticeProb.Prob.MvbeSteinExpectation
import LatticeProb.Prob.MehlerSmoothing
import LatticeProb.Prob.MehlerInterpolation
import LatticeProb.Prob.MvbeSmoothing
import LatticeProb.Prob.MvbeImageClass
import LatticeProb.Prob.MvbeImageNegOpen
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.MvbeKeyLemmaProved

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-!
# Raic's Theorem 1.3 (form (1.4)): the bootstrapping argument

Packet P13 of the staged formalisation of Raic, *A multivariate Berry-Esseen theorem with explicit
constants* (arXiv:1802.06475), report item L13.  This file fixes the interfaces between the verified
pieces and the key estimate (Lemma 2.7), proves the bootstrapping argument (the end of Section 2 of
the paper), and combines it with the proved Lemma 2.7 into the unconditional

`mvbe_thmR : MvbeThmR`

(and the conditional form `mvbe_thmR_of_keyLemma : MvbeKeyLemma → MvbeThmR`).

## Statements

* `MvbeThmR` : Theorem 1.3, form (1.4), with existential absolute constants `c0`, `c1`.  It is
  stated for every regular class `C` with `MvbeNegOpen C` (the extra hypothesis that Lemma 2.1
  needs, see `MvbeSmoothing.lean`) and every sum of independent centred summands with identity
  covariance (`Measure.pi ν`, `Fin n`-indexed).
* `mvbeK d κ β0 γ0` : Raic's `K(β0, γ0)` (2.30), a real `sSup` over all sums, all classes with
  parameter `κ` and `MvbeNegOpen`, and all sets of the class.  `mvbeK_le_inv` : `K ≤ 1/(β0 γ0)`.
* `MvbeKeyLemmaWith ca cb` / `MvbeKeyLemma` : Lemma 2.7 in the form the bootstrapping consumes: for
  the smoothing functions `f_A^{±ε}`, a probability measure `μW` (the law of `W`), `Σ ⪰ σ² I`, and
  the hypothesis (2.10), the `α`-integral of `|E ∇³ U_α f (W)|_∨ tan α` (the injective norm being
  the diagonal supremum, Proposition 2.1) is at most
  `ca/σ³ + cb √(1+κ) (γ*/σ + 4D/ε)`.

## Proved here (concrete theorems)

* `mvbe_smoothingFacts` (Lemma 2.1, from packet P9), `mvbe_imageClassFacts` (Lemma 2.3, from P12),
  `mvbe_mehlerInterp` (Raic (2.5) for `C^{1,1}` functions, from the verified C² interpolation),
  `mvbe_mehlerI_smooth`, `mvbe_mehlerI_D3_formula` (smoothness and bounds of `U_α f`, from P8a),
  `mvbe_cond_dev` (the estimate of `D_{i,A}` by the definition of `K`), `mvbe_sandwich` (2.23),
  `mvbe_slepian_stein` (interpolation + Stein expectation + conditioning + Hölder),
  `mvbe_key_ineq` (`K ≤ K/2 + c`), `mvbeK_le_bound`, `mvbe_thmR_of_keyLemma`,
  `mvbe_keyLemmaWith` (Lemma 2.7, from `mvbe_keyLemma_proved`), `mvbe_thmR`.
-/

namespace LatticeProb

/-! ## Data: summands, deviation, the quantity `K(β₀, γ₀)` -/

section Defs

/-- The data of a sum of independent centred random vectors with identity total covariance. -/
structure MvbeSummands (d : ℕ) where
  n : ℕ
  ν : Fin n → Measure (EuclideanSpace ℝ (Fin d))
  prob : ∀ i, IsProbabilityMeasure (ν i)
  mom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)
  mean : ∀ i, ∫ x, x ∂ν i = 0
  cov : ∀ u v : EuclideanSpace ℝ (Fin d),
    ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v

attribute [instance] MvbeSummands.prob

/-- `β = ∑ᵢ E‖Xᵢ‖³`. -/
noncomputable def MvbeSummands.beta {d : ℕ} (S : MvbeSummands d) : ℝ :=
  ∑ i, ∫ x, ‖x‖ ^ 3 ∂S.ν i

/-- `|P(W ∈ A) - N(0, I){A}|`. -/
noncomputable def MvbeSummands.dev {d : ℕ} (S : MvbeSummands d)
    (A : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  |((Measure.pi S.ν) {ω | ∑ i, ω i ∈ A}).toReal
    - (stdGaussian (EuclideanSpace ℝ (Fin d)) A).toReal|

/-- The set of quotients defining Raic's `K(β₀, γ₀)` (2.30). -/
def mvbeKSet (d : ℕ) (κ β0 γ0 : ℝ) : Set ℝ :=
  {r | ∃ (S : MvbeSummands d) (C : MvbeRegularClass d κ), MvbeNegOpen C ∧
    C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤ ∧ ∃ A ∈ C.cls,
      r = S.dev A / (max S.beta β0 *
        max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0)}

/-- Raic's `K(β₀, γ₀)` (2.30). -/
noncomputable def mvbeK (d : ℕ) (κ β0 γ0 : ℝ) : ℝ := sSup (mvbeKSet d κ β0 γ0)

/-- The covariance of the complement `W_i = W - X_i`: `Σ_i = I - E[X_i X_iᵀ]`. -/
noncomputable def mvbeSigma {d : ℕ} (S : MvbeSummands d) (i : Fin S.n) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun p q => (if p = q then (1 : ℝ) else 0) - ∫ x, x p * x q ∂S.ν i

/-- The law of `W_i + m`, where `W_i = ∑_{j ≠ i} ω j` under `Measure.pi S.ν`. -/
noncomputable def mvbeCondLaw {d : ℕ} (S : MvbeSummands d) (i : Fin S.n)
    (m : EuclideanSpace ℝ (Fin d)) : Measure (EuclideanSpace ℝ (Fin d)) :=
  ((Measure.pi S.ν).map (mvbeWithout i)).map (fun w => w + m)

/-- Raic's `|E ∇³ g(W)|_∨` for `W ∼ μ`, in the form `sup_{‖u‖≤1} |E ⟨∇³g(W), u⊗u⊗u⟩|`
(Proposition 2.1 identifies it with the injective norm of the expected tensor). -/
noncomputable def mvbeDiag3 {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ⨆ u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1},
    |∫ y, iteratedFDeriv ℝ 3 g y ![u.1, u.1, u.1] ∂μ|

end Defs


/-! ## The interfaces -/

section Props

/-- **Smoothing functions of Raic's Lemma 2.1.**  `f` is a smoothing function for the class `C` at
scale `ε`, between the sets `A1 ⊆ A2`, where `(A1, A2) = (A, A^{ε|ρ})` (outer smoothing `f_A^{ε}`)
or `(A1, A2) = (A^{-ε|ρ}, A)` (inner smoothing `f_A^{-ε}`) for a member `A` of the class:
`0 ≤ f ≤ 1`, `f = 1` on `A1`, `f = 0` off `A2`, `f` is `C¹` with `M₁ f ≤ 2/ε` and
`M₂ f ≤ 4(1+κ)/ε²` (that is: `∇f` is Lipschitz), and the level sets `{f ≥ u}`, `0 < u < 1`, are in
`A ∪ {∅, ℝ^d}`. -/
structure MvbeSmoothFn {d : ℕ} {κ : ℝ} (C : MvbeRegularClass d κ) (ε : ℝ)
    (A1 A2 : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  layer_pair : ∃ A ∈ C.cls, (A1 = A ∧ A2 = mvbeLayer C.rho A ε) ∨
    (A1 = mvbeLayer C.rho A (-ε) ∧ A2 = A)
  zero_le : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  eq_one : ∀ x ∈ A1, f x = 1
  eq_zero : ∀ x ∉ A2, f x = 0
  contDiff : ContDiff ℝ 1 f
  norm_fderiv_le : ∀ x, ‖fderiv ℝ f x‖ ≤ 2 / ε
  lipschitz_fderiv : LipschitzWith (Real.toNNReal (4 * (1 + κ) / ε ^ 2)) (fderiv ℝ f)
  levelSet_mem : ∀ u : ℝ, 0 < u → u < 1 → {x | u ≤ f x} ∈ C.cls ∪ {∅, Set.univ}

/-- **Lemma 2.1 of Raic (packet P9).**  For a regular class with `{ρ_A < 0}` open, `A` in the class
and `ε > 0` there are the smoothing functions `f_A^{ε}` (between `A` and `A^{ε|ρ}`) and `f_A^{-ε}`
(between `A^{-ε|ρ}` and `A`): the explicit functions `C.smoothOuter A ε`, `C.smoothInner A ε`
of packet P9.  Proved below: `mvbe_smoothingFacts`. -/
def MvbeSmoothingFacts : Prop :=
  ∀ (d : ℕ) (κ : ℝ) (C : MvbeRegularClass d κ), MvbeNegOpen C →
    ∀ A ∈ C.cls, ∀ ε : ℝ, 0 < ε →
      MvbeSmoothFn C ε A (mvbeLayer C.rho A ε) (C.smoothOuter A ε) ∧
      MvbeSmoothFn C ε (mvbeLayer C.rho A (-ε)) A (C.smoothInner A ε)

/-- **Lemma 2.3 of Raic (image classes)** (packet P12), in the form used by the bootstrapping:
the image class under `T` is a regular class with the same `κ`, contains `T '' A` for `A ∈ C`,
keeps `MvbeNegOpen`, and `γ*(T C) ≤ ‖T⁻¹‖ max(1, ‖T‖) γ*(C)`.  Proved below:
`mvbe_imageClassFacts`. -/
def MvbeImageClassFacts : Prop :=
  ∀ (d : ℕ) [NeZero d] (κ : ℝ) (C : MvbeRegularClass d κ)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
    ∃ Ĉ : MvbeRegularClass d κ,
      (∀ A ∈ C.cls, T '' A ∈ Ĉ.cls) ∧ (MvbeNegOpen C → MvbeNegOpen Ĉ) ∧
      Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))
        ≤ ENNReal.ofReal (‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
            * max 1 ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖)
          * C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- **Lemma 2.7 of Raic (key estimate)** with explicit absolute constants `ca`, `cb`
(Raic: `ca = c₃/6`, `cb = √(2 c₁ c₃)`, `c_r = ∫ |φ₁^{(r)}| = E|He_r(Z)|`).  The left side is
`∫₀^{π/2} |E ∇³U_α f (W)|_∨ tan α dα` for `W ∼ μW`, the injective norm being the diagonal
supremum `sup_{‖u‖≤1} |E ⟨∇³U_α f(W), u⊗u⊗u⟩|` (`mvbeDiag3`; Proposition 2.1), so that the
proof of the lemma needs no polarisation.  `f` is any smoothing function (`MvbeSmoothFn`) of the
class; `μW` any probability measure with `|μW(A) - N(m, S)(A)| ≤ D` on the class (2.10),
`S ⪰ σ² I`, `0 < σ ≤ 1`.  The smoothing functions are the explicit `C.smoothOuter A ε`,
`C.smoothInner A ε` of Lemma 2.1.  Proved below: `mvbe_keyLemmaWith`, from
`mvbe_keyLemma_proved` (with `ca = c₃/6`, `cb = √(2 c₁ c₃)`). -/
def MvbeKeyLemmaWith (ca cb : ℝ) : Prop :=
  ∀ (d : ℕ) (κ : ℝ) (C : MvbeRegularClass d κ), MvbeNegOpen C →
    C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤ →
    ∀ (μW : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure μW →
    ∀ (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) (σ D ε : ℝ),
      0 < σ → σ ≤ 1 → (S - σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef →
      0 ≤ D → 0 < ε →
      (∀ A ∈ C.cls, |(μW A).toReal - (multivariateGaussian m S A).toReal| ≤ D) →
      ∀ A ∈ C.cls, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (f = C.smoothOuter A ε ∨ f = C.smoothInner A ε) →
        ∫⁻ a in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal (mvbeDiag3 (mehlerI a f) μW * Real.tan a)
          ≤ ENNReal.ofReal (ca / σ ^ 3 + cb * √(1 + κ) *
              ((C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal / σ
                + 4 * D / ε))

/-- **Lemma 2.7 of Raic (key estimate)** in the form consumed by the bootstrapping argument. -/
def MvbeKeyLemma : Prop := ∃ ca cb : ℝ, 0 < ca ∧ 0 < cb ∧ MvbeKeyLemmaWith ca cb

/-- **Raic's (2.5) for `C^{1,1}_b` functions** (the Slepian interpolation; the verified
`mehlerI_interpolation` is the case `f ∈ C²_b`).  The smoothing functions of Lemma 2.1 are only
`C^{1,1}`.  Proved below: `mvbe_mehlerInterp`. -/
def MvbeMehlerInterp : Prop :=
  ∀ (d : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → EuclideanSpace ℝ (Fin d)), Measurable W → Integrable (fun ω => ‖W ω‖) P →
    ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 f → (∃ C, ∀ x, |f x| ≤ C) →
      (∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) → (∃ L, LipschitzWith L (fderiv ℝ f)) →
      ∫ ω, f (W ω) ∂P - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        = -∫ a in Set.Ioo 0 (Real.pi / 2),
            Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P

/-- **Raic's Theorem 1.3, form (1.4)**, with existential absolute constants. -/
def MvbeThmR : Prop :=
  ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
    ∀ (d : ℕ) [NeZero d] (κ : ℝ) (C : MvbeRegularClass d κ), MvbeNegOpen C →
      C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤ →
      ∀ (n : ℕ) (ν : Fin n → Measure (EuclideanSpace ℝ (Fin d)))
        [∀ i, IsProbabilityMeasure (ν i)],
        (∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) → (∀ i, ∫ x, x ∂ν i = 0) →
        (∀ u v : EuclideanSpace ℝ (Fin d),
          ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v) →
        ∀ A ∈ C.cls,
          |((Measure.pi ν) {ω | ∑ i, ω i ∈ A}).toReal
              - (stdGaussian (EuclideanSpace ℝ (Fin d)) A).toReal|
            ≤ max c0 (1 + c1 * (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal
                * √(1 + κ)) * ∑ i, ∫ x, ‖x‖ ^ 3 ∂ν i

end Props


/-! ## Concrete discharge of the interfaces coming from verified packets -/

section Concrete

/-- **Lemma 2.1 is available** (packet P9, `MvbeRegularClass.raic_lemma_2_1`). -/
theorem mvbe_smoothingFacts : MvbeSmoothingFacts := by
  intro d κ C hneg A hA ε hε
  have hc : 0 ≤ 4 * (1 + κ) / ε ^ 2 := by
    have := C.kappa_nonneg
    positivity
  have lip : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ 4 * (1 + κ) / ε ^ 2 * ‖x - y‖) →
      LipschitzWith (Real.toNNReal (4 * (1 + κ) / ε ^ 2)) (fderiv ℝ g) := by
    intro g h
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.coe_toNNReal _ hc, dist_eq_norm, dist_eq_norm]
    exact h x y
  refine ⟨?_, ?_⟩
  · exact { layer_pair := ⟨A, hA, Or.inl ⟨rfl, rfl⟩⟩
            zero_le := fun x => (C.smoothOuter_mem_Icc A ε x).1
            le_one := fun x => (C.smoothOuter_mem_Icc A ε x).2
            eq_one := fun x hx => C.smoothOuter_eq_one hA hε hx
            eq_zero := fun x hx => C.smoothOuter_eq_zero hε hx
            contDiff := C.contDiff_smoothOuter hneg hA hε
            norm_fderiv_le := C.norm_fderiv_smoothOuter_le hneg hA hε
            lipschitz_fderiv := lip _ (C.fderiv_smoothOuter_sub_le hneg hA hε)
            levelSet_mem := fun _ h0 h1 => C.smoothOuter_levelSet_mem hA hε h0 h1 }
  · exact { layer_pair := ⟨A, hA, Or.inr ⟨rfl, rfl⟩⟩
            zero_le := fun x => (C.smoothInner_mem_Icc hA ε x).1
            le_one := fun x => (C.smoothInner_mem_Icc hA ε x).2
            eq_one := fun x hx => C.smoothInner_eq_one hA hε hx
            eq_zero := fun x hx => C.smoothInner_eq_zero hA hε hx
            contDiff := C.contDiff_smoothInner hneg hA hε
            norm_fderiv_le := C.norm_fderiv_smoothInner_le hneg hA hε
            lipschitz_fderiv := lip _ (C.fderiv_smoothInner_sub_le hneg hA hε)
            levelSet_mem := fun _ h0 h1 => C.smoothInner_levelSet_mem hA hε h0 h1 }

/-- **Lemma 2.3 is available** (packet P12, `MvbeRegularClass.imageCLE`). -/
theorem mvbe_imageClassFacts : MvbeImageClassFacts := by
  intro d _ κ C T
  refine ⟨C.imageCLE T, fun A hA => ⟨A, hA, rfl⟩, fun h => C.imageCLE_negOpen T h, ?_⟩
  have h := C.imageCLE_gammaStar_le T
  have hpos : 0 < ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ :=
    T.norm_pos
  rw [mvbe_div_min_one_div hpos] at h
  have e : mvbeInvNorm T = ‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ :=
    rfl
  refine h.trans (le_of_eq ?_)
  rw [mul_comm, e, mul_comm (max 1 _) _]

end Concrete


/-! ## Pieces of the bootstrapping argument -/

section Pieces

variable {d : ℕ} {κ : ℝ}

instance mvbeCondLaw_isProb (S : MvbeSummands d) (i : Fin S.n) (m : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (mvbeCondLaw S i m) := by
  unfold mvbeCondLaw
  haveI : IsProbabilityMeasure ((Measure.pi S.ν).map (mvbeWithout i)) :=
    Measure.isProbabilityMeasure_map (mvbe_measurable_without i).aemeasurable
  exact Measure.isProbabilityMeasure_map (measurable_add_const m).aemeasurable

/-- `E‖X‖² ≤ 1/4` if `E‖X‖³ < 1/8` (via `t² ≤ (4/3) t³ + 1/12`). -/
theorem mvbe_sq_moment_le (S : MvbeSummands d) (i : Fin S.n) (hβ : S.beta < 1 / 8) :
    ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ 1 / 4 := by
  have h3 : ∫ x, ‖x‖ ^ 3 ∂S.ν i ≤ S.beta :=
    Finset.single_le_sum (f := fun j => ∫ x, ‖x‖ ^ 3 ∂S.ν j)
      (fun j _ => integral_nonneg fun x => by positivity) (Finset.mem_univ i)
  have hpt : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ 2 ≤ 4 / 3 * ‖x‖ ^ 3 + 1 / 12 := by
    intro x
    have ht := norm_nonneg x
    nlinarith [mul_nonneg ht (sq_nonneg (‖x‖ - 1 / 2)), sq_nonneg (‖x‖ - 1 / 2)]
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => 4 / 3 * ‖x‖ ^ 3 + 1 / 12) (S.ν i) :=
    ((S.mom i).const_mul _).add (integrable_const _)
  calc ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ ∫ x, (4 / 3 * ‖x‖ ^ 3 + 1 / 12) ∂S.ν i :=
        integral_mono (mvbe_integrable_sq (S.mom i)) hint hpt
    _ = 4 / 3 * ∫ x, ‖x‖ ^ 3 ∂S.ν i + 1 / 12 := by
        rw [integral_add ((S.mom i).const_mul _) (integrable_const _), integral_const_mul]
        simp
    _ ≤ 1 / 4 := by linarith

end Pieces


section W2Mehler

section Polar2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mvbe_w2_T2_add_left (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (x y u : E) : B ![x + y, u] = B ![x, u] + B ![y, u] := by
  have h := B.map_update_add ![x, u] 0 x y
  have e : ∀ w : E, Function.update ![x, u] 0 w = ![w, u] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_w2_T2_add_right (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (x y u : E) : B ![u, x + y] = B ![u, x] + B ![u, y] := by
  have h := B.map_update_add ![u, x] 1 x y
  have e : ∀ w : E, Function.update ![u, x] 1 w = ![u, w] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_w2_T2_smul_left (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (r : ℝ) (x u : E) : B ![r • x, u] = r * B ![x, u] := by
  have h := B.map_update_smul ![x, u] 0 r x
  have e : ∀ w : E, Function.update ![x, u] 0 w = ![w, u] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_w2_T2_smul_right (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (r : ℝ) (x u : E) : B ![u, r • x] = r * B ![u, x] := by
  have h := B.map_update_smul ![u, x] 1 r x
  have e : ∀ w : E, Function.update ![u, x] 1 w = ![u, w] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

/-- Polarisation identity for a symmetric bilinear form: `4 B(u,v) = B(u+v,u+v) - B(u-v,u-v)`. -/
theorem mvbe_w2_T2_polar (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (s : ∀ p q : E, B ![p, q] = B ![q, p]) (u v : E) :
    4 * B ![u, v] = B ![u + v, u + v] - B ![u - v, u - v] := by
  have e : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  simp only [mvbe_w2_T2_add_left, mvbe_w2_T2_add_right, mvbe_w2_T2_smul_left,
    mvbe_w2_T2_smul_right, s v u]
  ring

/-- Unit-ball bound of a symmetric bilinear form from its diagonal. -/
theorem mvbe_w2_unit_le (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (s : ∀ p q : E, B ![p, q] = B ![q, p]) {K : ℝ}
    (hd : ∀ u : E, |B ![u, u]| ≤ K * ‖u‖ ^ 2) {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    |B ![a, b]| ≤ K := by
  have hp := mvbe_w2_T2_polar B s a b
  have hpar := parallelogram_law_with_norm ℝ a b
  have h1 := hd (a + b)
  have h2 := hd (a - b)
  rw [ha, hb] at hpar
  have h4 : |4 * B ![a, b]| ≤ 4 * K := by
    rw [hp]
    calc |B ![a + b, a + b] - B ![a - b, a - b]|
        ≤ |B ![a + b, a + b]| + |B ![a - b, a - b]| := abs_sub _ _
      _ ≤ K * ‖a + b‖ ^ 2 + K * ‖a - b‖ ^ 2 := add_le_add h1 h2
      _ = K * (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2) := by ring
      _ = 4 * K := by rw [hpar]; ring
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h4
  linarith

/-- **Polarisation for symmetric bilinear forms.**  If `B` is a continuous symmetric bilinear
form with `|B(u,u)| ≤ K ‖u‖²` then `‖B‖ ≤ K`. -/
theorem mvbe_w2_norm_le_of_diag (B : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (s : ∀ p q : E, B ![p, q] = B ![q, p]) {K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ u : E, |B ![u, u]| ≤ K * ‖u‖ ^ 2) : ‖B‖ ≤ K := by
  refine ContinuousMultilinearMap.opNorm_le_bound hK fun m => ?_
  have hm : m = ![m 0, m 1] := by
    ext i; fin_cases i <;> simp
  rw [Fin.prod_univ_two]
  by_cases h0 : m 0 = 0
  · have : B m = 0 := B.map_coord_zero 0 h0
    rw [this]; simp [h0]
  by_cases h1 : m 1 = 0
  · have : B m = 0 := B.map_coord_zero 1 h1
    rw [this]; simp [h1]
  have n0 : 0 < ‖m 0‖ := norm_pos_iff.2 h0
  have n1 : 0 < ‖m 1‖ := norm_pos_iff.2 h1
  have key := mvbe_w2_unit_le B s hd (a := ‖m 0‖⁻¹ • m 0) (b := ‖m 1‖⁻¹ • m 1)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n0.ne'])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1.ne'])
  have e : B m = ‖m 0‖ * ‖m 1‖ * B ![‖m 0‖⁻¹ • m 0, ‖m 1‖⁻¹ • m 1] := by
    rw [mvbe_w2_T2_smul_left, mvbe_w2_T2_smul_right, ← hm]
    field_simp
  have hP : 0 ≤ ‖m 0‖ * ‖m 1‖ := by positivity
  rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
  calc ‖m 0‖ * ‖m 1‖ * |B ![‖m 0‖⁻¹ • m 0, ‖m 1‖⁻¹ • m 1]|
      ≤ ‖m 0‖ * ‖m 1‖ * K := by gcongr
    _ = K * (‖m 0‖ * ‖m 1‖) := by ring

end Polar2

section Main

variable {d : ℕ}

theorem mvbe_w2_sin_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) : 0 < Real.sin a :=
  Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])

theorem mvbe_w2_vec2 {E : Type*} (u : E) : (![u, u] : Fin 2 → E) = fun _ => u := by
  ext i; fin_cases i <;> rfl

theorem mvbe_w2_vec3 {E : Type*} (u : E) : (![u, u, u] : Fin 3 → E) = fun _ => u := by
  ext i; fin_cases i <;> rfl

theorem mvbe_w2_contDiff_three {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {a : ℝ} (hs : 0 < Real.sin a) : ContDiff ℝ 3 (mehlerI a f) := by
  have h := mehlerN_contDiff a hf ⟨M, hM⟩ hs
  exact contDiff_infty.1 h 3

theorem mvbe_mehlerI_smooth {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) :
    ContDiff ℝ 3 (mehlerI a f) ∧ (∃ C, ∀ x, ‖fderiv ℝ (mehlerI a f) x‖ ≤ C) ∧
      (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 (mehlerI a f) x‖ ≤ C) ∧
      (∃ C, ∀ x, ‖iteratedFDeriv ℝ 3 (mehlerI a f) x‖ ≤ C) := by
  have hs := mvbe_w2_sin_pos ha0 ha1
  have hg3 : ContDiff ℝ 3 (mehlerI a f) := mvbe_w2_contDiff_three hf hM hs
  have hg2 : ContDiff ℝ 2 (mehlerI a f) := hg3.of_le (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨hg3, ⟨(mehlerNLip a M : ℝ), fun x => ?_⟩, ?_, ?_⟩
  · exact norm_fderiv_le_of_lipschitz ℝ (mehlerN_lipschitz a hf hM hs)
  · set K : ℝ := M * |Real.cos a / Real.sin a| ^ 2 *
      ∫ z, |Polynomial.aeval z (Polynomial.hermite 2)| ∂(gaussianReal 0 1) with hKdef
    have hI : 0 ≤ ∫ z, |Polynomial.aeval z (Polynomial.hermite 2)| ∂(gaussianReal 0 1) :=
      integral_nonneg fun z => abs_nonneg _
    have hK : 0 ≤ K := by positivity
    refine ⟨K, fun x => ?_⟩
    refine mvbe_w2_norm_le_of_diag (iteratedFDeriv ℝ 2 (mehlerI a f) x)
      (fun p q => mvbe_iteratedFDeriv_two_symm hg2 x p q) hK fun u => ?_
    rw [mvbe_w2_vec2]
    have := mehlerN_iteratedFDeriv_diag_bound a hf hM hs 2 x u
    calc |iteratedFDeriv ℝ 2 (mehlerI a f) x fun _ => u|
        ≤ M * |Real.cos a / Real.sin a| ^ 2 * ‖u‖ ^ 2 *
          ∫ z, |Polynomial.aeval z (Polynomial.hermite 2)| ∂(gaussianReal 0 1) := this
      _ = K * ‖u‖ ^ 2 := by rw [hKdef]; ring
  · set K : ℝ := M * |Real.cos a / Real.sin a| ^ 3 *
      ∫ z, |Polynomial.aeval z (Polynomial.hermite 3)| ∂(gaussianReal 0 1) with hKdef
    have hI : 0 ≤ ∫ z, |Polynomial.aeval z (Polynomial.hermite 3)| ∂(gaussianReal 0 1) :=
      integral_nonneg fun z => abs_nonneg _
    have hK : 0 ≤ K := by positivity
    refine ⟨9 / 2 * K, fun x => ?_⟩
    refine mvbe_norm_iteratedFDeriv_three_le hg3 x fun u hu => ?_
    rw [mvbe_w2_vec3]
    have := mehlerN_iteratedFDeriv_diag_bound a hf hM hs 3 x u
    calc |iteratedFDeriv ℝ 3 (mehlerI a f) x fun _ => u|
        ≤ M * |Real.cos a / Real.sin a| ^ 3 * ‖u‖ ^ 3 *
          ∫ z, |Polynomial.aeval z (Polynomial.hermite 3)| ∂(gaussianReal 0 1) := this
      _ = K * ‖u‖ ^ 3 := by rw [hKdef]; ring
      _ ≤ K * 1 := by
        gcongr
        exact pow_le_one₀ (norm_nonneg u) hu
      _ = K := mul_one K

theorem mvbe_mehlerI_D3_formula {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2)
    (z u : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ 3 (mehlerI a f) z ![u, u, u] =
      (Real.cos a / Real.sin a) ^ 3 *
        ∫ y, f (Real.cos a • z + Real.sin a • y) * mehlerNHerm 3 y u
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  mehlerN_iteratedFDeriv_three_hermite a hf ⟨M, hM⟩ (mvbe_w2_sin_pos ha0 ha1) z u

theorem mvbe_mehlerIS_eq_mvbeStein {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 2 g)
    (w : EuclideanSpace ℝ (Fin d)) :
    mehlerIS g w = mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) g w := by
  rw [mvbeStein_basisFun_apply]
  unfold mehlerIS
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mehlerN_iteratedDeriv_line_eq hg w (EuclideanSpace.single k (1 : ℝ)),
    mvbe_w2_vec2 (EuclideanSpace.single k (1 : ℝ))]

end Main


end W2Mehler

section W1Cond
open scoped ENNReal Matrix MatrixOrder

section W1Sigma

variable {d : ℕ} {κ : ℝ}

theorem mvbe_w1_inner_expand (x u : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x u = ∑ p, u p * x p := by
  simp [PiLp.inner_apply]

theorem mvbe_w1_integral_inner_mul (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (u v : EuclideanSpace ℝ (Fin d)) :
    ∫ x, inner ℝ x u * inner ℝ x v ∂μ = ∑ p, ∑ q, u p * v q * ∫ x, x p * x q ∂μ := by
  have hint : ∀ p q : Fin d, Integrable (fun x : EuclideanSpace ℝ (Fin d) => x p * x q) μ := by
    intro p q
    have := mvbe_integrable_inner_mul hmom (EuclideanSpace.single p (1 : ℝ))
      (EuclideanSpace.single q (1 : ℝ))
    simpa [mvbe_w1_inner_expand] using this
  have e : ∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x u * inner ℝ x v
      = ∑ p, ∑ q, u p * v q * (x p * x q) := by
    intro x
    rw [mvbe_w1_inner_expand x u, mvbe_w1_inner_expand x v, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
    (hint p q).const_mul _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => (hint p q).const_mul _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul]

theorem mvbe_w1_sigma_bilin (S : MvbeSummands d) (i : Fin S.n)
    (u v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ u (WithLp.toLp 2 (mvbeSigma S i *ᵥ WithLp.ofLp v)) =
      inner ℝ u v - ∫ x, inner ℝ x u * inner ℝ x v ∂S.ν i := by
  rw [mvbe_w1_integral_inner_mul _ (S.mom i) u v, mvbe_w1_inner_expand, mvbe_w1_inner_expand]
  simp only [mvbeSigma, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp [ite_mul, Finset.sum_ite_eq]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

theorem mvbe_w1_sigma_isHermitian (S : MvbeSummands d) (i : Fin S.n) :
    (mvbeSigma S i).IsHermitian := by
  rw [mvbe_isHermitian_iff_isSymm]
  ext p q
  simp [mvbeSigma, eq_comm, mul_comm]

theorem mvbe_w1_sigma_quad (S : MvbeSummands d) (i : Fin S.n)
    (h : ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ 1 / 4) (v : EuclideanSpace ℝ (Fin d)) :
    3 / 4 * ‖v‖ ^ 2 ≤ inner ℝ v (WithLp.toLp 2 (mvbeSigma S i *ᵥ WithLp.ofLp v)) ∧
      inner ℝ v (WithLp.toLp 2 (mvbeSigma S i *ᵥ WithLp.ofLp v)) ≤ ‖v‖ ^ 2 := by
  rw [mvbe_w1_sigma_bilin, real_inner_self_eq_norm_sq]
  have h0 : 0 ≤ ∫ x, inner ℝ x v * inner ℝ x v ∂S.ν i :=
    integral_nonneg fun x => mul_self_nonneg _
  have h1 : ∫ x, inner ℝ x v * inner ℝ x v ∂S.ν i ≤ ∫ x, ‖v‖ ^ 2 * ‖x‖ ^ 2 ∂S.ν i := by
    refine integral_mono (mvbe_integrable_inner_mul (S.mom i) v v)
      ((mvbe_integrable_sq (S.mom i)).const_mul _) fun x => ?_
    have := real_inner_mul_inner_self_le x v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    linarith
  rw [integral_const_mul] at h1
  have h2 : ‖v‖ ^ 2 * ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ ‖v‖ ^ 2 * (1 / 4) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  constructor <;> linarith

theorem mvbeSigma_posSemidef (S : MvbeSummands d) (i : Fin S.n)
    (h : ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ 1 / 4) :
    (mvbeSigma S i - ((1 : ℝ) / 2) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  rw [mvbe_posSemidef_sub_sq_smul_one_iff (mvbe_w1_sigma_isHermitian S i)]
  intro v
  rw [real_inner_comm]
  have := (mvbe_w1_sigma_quad S i h v).1
  nlinarith [sq_nonneg ‖v‖]

theorem mvbe_w1_sigma_psd (S : MvbeSummands d) (i : Fin S.n)
    (h : ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ 1 / 4) : (mvbeSigma S i).PosSemidef := by
  have := (mvbe_posSemidef_sub_sq_smul_one_iff (mvbe_w1_sigma_isHermitian S i) 0).mpr
    (fun v => by
      rw [real_inner_comm]
      have := (mvbe_w1_sigma_quad S i h v).1
      nlinarith [sq_nonneg ‖v‖])
  simpa using this

end W1Sigma

section W1Whiten

variable {d : ℕ}

theorem mvbe_w1_sqrt_posSemidef {M : Matrix (Fin d) (Fin d) ℝ} :
    (CFC.sqrt M).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)

theorem mvbe_w1_sqrt_symm (M : Matrix (Fin d) (Fin d) ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x) y
      = inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) y) := by
  have h : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M)) :=
    (mvbe_w1_sqrt_posSemidef (M := M)).isHermitian.isSelfAdjoint.map _
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h) x y

theorem mvbe_w1_sqrt_sq {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (x : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x)
      = Matrix.toEuclideanCLM (𝕜 := ℝ) M x := by
  have h : CFC.sqrt M * CFC.sqrt M = M :=
    CFC.sqrt_mul_sqrt_self M (Matrix.nonneg_iff_posSemidef.mpr hM)
  conv_rhs => rw [← h]
  rw [map_mul]
  rfl

theorem mvbe_w1_sqrt_norm_sq {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x‖ ^ 2
      = inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) := by
  rw [← real_inner_self_eq_norm_sq, mvbe_w1_sqrt_symm, mvbe_w1_sqrt_sq hM]

theorem mvbe_w1_sqrt_norm_le {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (hhi : ∀ v : EuclideanSpace ℝ (Fin d), inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) M v)
      ≤ ‖v‖ ^ 2) (x : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x‖ ≤ ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [mvbe_w1_sqrt_norm_sq hM]
  exact hhi x

theorem mvbe_w1_sqrt_norm_ge {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin d), 1 / 4 * ‖v‖ ^ 2
      ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) M v)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  have := hlo x
  rw [← mvbe_w1_sqrt_norm_sq hM] at this
  nlinarith

/-- The whitening equivalence `T = (√M)⁻¹`: a continuous linear equivalence with
`T.symm = √M`, `‖T‖ ≤ 2` and `‖T⁻¹‖ ≤ 1`. -/
theorem mvbe_w1_exists_equiv {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (hlo : ∀ v : EuclideanSpace ℝ (Fin d), 1 / 4 * ‖v‖ ^ 2
      ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) M v))
    (hhi : ∀ v : EuclideanSpace ℝ (Fin d), inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) M v)
      ≤ ‖v‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x, T.symm x = Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x) ∧
      (∀ x, ‖T x‖ ≤ 2 * ‖x‖) ∧ (∀ x, ‖T.symm x‖ ≤ ‖x‖) := by
  have hinj : Function.Injective (CFC.sqrt M).mulVec := by
    intro a b hab
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) (WithLp.toLp 2 a - WithLp.toLp 2 b)
        = 0 := by
      rw [map_sub]
      simp [hab]
    have h2 := mvbe_w1_sqrt_norm_ge hM hlo (WithLp.toLp 2 a - WithLp.toLp 2 b)
    rw [h1, norm_zero, mul_zero] at h2
    have h3 : WithLp.toLp 2 a - WithLp.toLp 2 b = 0 := norm_le_zero_iff.mp h2
    have h4 : WithLp.toLp 2 a = (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)) := sub_eq_zero.mp h3
    simpa using h4
  have hU : IsUnit (CFC.sqrt M).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨(mvbeMatrixCLE (CFC.sqrt M) hU).symm, fun x => rfl, fun x => ?_, fun x => ?_⟩
  · have h := mvbe_w1_sqrt_norm_ge hM hlo ((mvbeMatrixCLE (CFC.sqrt M) hU).symm x)
    have e : Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M)
        ((mvbeMatrixCLE (CFC.sqrt M) hU).symm x) = x :=
      (mvbeMatrixCLE (CFC.sqrt M) hU).apply_symm_apply x
    rw [e] at h
    exact h
  · exact mvbe_w1_sqrt_norm_le hM hhi x

end W1Whiten

section W1Measure

variable {d : ℕ}

theorem mvbe_w1_marginal {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ j, IsProbabilityMeasure (ν j)] (i : Fin (n + 1)) :
    (Measure.pi ν).map (fun ω (j : Fin n) => ω (i.succAbove j))
      = Measure.pi (fun j : Fin n => ν (i.succAbove j)) := by
  have h := measurePreserving_piFinSuccAbove ν i
  have e : (fun (ω : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (j : Fin n) => ω (i.succAbove j))
      = Prod.snd ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ (Fin d)) i) := by
    funext ω j
    rfl
  rw [e, ← Measure.map_map measurable_snd h.measurable, h.map_eq, Measure.map_snd_prod]
  simp

theorem mvbe_w1_without_eq {n : ℕ} (i : Fin (n + 1)) (ω : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) :
    mvbeWithout i ω = ∑ j : Fin n, ω (i.succAbove j) := by
  have h := mvbe_without_add i ω
  rw [Fin.sum_univ_succAbove _ i, add_comm (ω i)] at h
  exact add_right_cancel h

theorem mvbe_w1_pi_map {n : ℕ} (μ : Fin n → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ j, IsProbabilityMeasure (μ j)]
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.pi (fun j => (μ j).map T)
      = (Measure.pi μ).map (fun ω j => T (ω j)) :=
  (Measure.pi_map_pi (fun _ => T.continuous.measurable.aemeasurable)).symm

theorem mvbe_w1_condLaw_eq {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ j, IsProbabilityMeasure (ν j)] (i : Fin (n + 1))
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (m' : EuclideanSpace ℝ (Fin d))
    {A' : Set (EuclideanSpace ℝ (Fin d))} (hA' : MeasurableSet A') :
    (((Measure.pi ν).map (mvbeWithout i)).map (fun w => w + m')) A'
      = (Measure.pi (fun j : Fin n => (ν (i.succAbove j)).map T))
          {ω | ∑ j, ω j ∈ T '' ((fun z => z + m') ⁻¹' A')} := by
  have hB : MeasurableSet ((fun z : EuclideanSpace ℝ (Fin d) => z + m') ⁻¹' A') :=
    measurable_add_const m' hA'
  have hTB : MeasurableSet (T '' ((fun z : EuclideanSpace ℝ (Fin d) => z + m') ⁻¹' A')) := by
    rw [T.image_eq_preimage_symm]
    exact T.symm.continuous.measurable hB
  have hS : MeasurableSet {ω : Fin n → EuclideanSpace ℝ (Fin d) |
      ∑ j, ω j ∈ T '' ((fun z : EuclideanSpace ℝ (Fin d) => z + m') ⁻¹' A')} :=
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) hTB
  have hm1 : Measurable (fun (ω : Fin (n + 1) → EuclideanSpace ℝ (Fin d)) (j : Fin n) =>
      ω (i.succAbove j)) := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hm2 : Measurable (fun (ω : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n) => T (ω j)) :=
    measurable_pi_lambda _ fun j => T.continuous.measurable.comp (measurable_pi_apply j)
  rw [Measure.map_apply (measurable_add_const m') hA',
    Measure.map_apply (mvbe_measurable_without i) hB, mvbe_w1_pi_map, ← mvbe_w1_marginal ν i,
    Measure.map_map hm2 hm1, Measure.map_apply (hm2.comp hm1) hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply]
  rw [mvbe_w1_without_eq, ← map_sum, T.injective.mem_set_image]
  rfl

end W1Measure

section W1Reduce

variable {d : ℕ}

theorem mvbe_w1_gauss_eq (M : Matrix (Fin d) (Fin d) ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : ∀ x, T.symm x = Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x)
    (m' : EuclideanSpace ℝ (Fin d)) {A' : Set (EuclideanSpace ℝ (Fin d))}
    (hA' : MeasurableSet A') :
    multivariateGaussian m' M A'
      = stdGaussian (EuclideanSpace ℝ (Fin d)) (T '' ((fun z => z + m') ⁻¹' A')) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
      m' + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M) x) := by fun_prop
  unfold multivariateGaussian
  rw [Measure.map_apply hm hA', T.image_eq_preimage_symm]
  congr 1
  ext x
  simp only [Set.mem_preimage, hT, add_comm]

theorem mvbe_w1_map_mom (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT2 : ∀ x, ‖T x‖ ≤ 2 * ‖x‖) :
    Integrable (fun x => ‖x‖ ^ 3) (μ.map T) := by
  rw [integrable_map_measure (by fun_prop) T.continuous.measurable.aemeasurable]
  refine Integrable.mono' (hmom.const_mul 8) (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, norm_pow, norm_norm]
  calc ‖T x‖ ^ 3 ≤ (2 * ‖x‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hT2 x) 3
    _ = 8 * ‖x‖ ^ 3 := by ring

theorem mvbe_w1_map_mean (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (hmean : ∫ x, x ∂μ = 0)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∫ x, x ∂(μ.map T) = 0 := by
  rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]
  have := (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).integral_comp_comm
    (φ := fun x : EuclideanSpace ℝ (Fin d) => x) (mvbe_integrable_id hmom)
  simp only [ContinuousLinearEquiv.coe_coe] at this
  rw [this, hmean, map_zero]

theorem mvbe_w1_map_beta_le (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT2 : ∀ x, ‖T x‖ ≤ 2 * ‖x‖) :
    ∫ x, ‖x‖ ^ 3 ∂(μ.map T) ≤ 8 * ∫ x, ‖x‖ ^ 3 ∂μ := by
  have hint := mvbe_w1_map_mom μ hmom T hT2
  rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop), ← integral_const_mul]
  refine integral_mono ?_ (hmom.const_mul 8) fun x => ?_
  · rw [integrable_map_measure (by fun_prop) T.continuous.measurable.aemeasurable] at hint
    exact hint
  · calc ‖T x‖ ^ 3 ≤ (2 * ‖x‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hT2 x) 3
      _ = 8 * ‖x‖ ^ 3 := by ring

theorem mvbe_w1_red_cov {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin d),
      ∑ j, ∫ x, inner ℝ x u * inner ℝ x v ∂ν j = inner ℝ u v)
    (i : Fin (n + 1)) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : ∀ x, T.symm x = L x)
    (hsym : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (hMat : ∀ u v : EuclideanSpace ℝ (Fin d),
      inner ℝ u v - ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u (L (L v)))
    (u v : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin n, ∫ x, inner ℝ (T x) u * inner ℝ (T x) v ∂ν (i.succAbove j) = inner ℝ u v := by
  have hLT : ∀ x, L (T x) = x := fun x => by rw [← hT]; exact T.symm_apply_apply x
  have hTs : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y) := by
    intro x y
    calc inner ℝ (T x) y = inner ℝ (T x) (L (T y)) := by rw [hLT]
      _ = inner ℝ (L (T x)) (T y) := (hsym _ _).symm
      _ = inner ℝ x (T y) := by rw [hLT]
  simp_rw [hTs]
  have h1 := hcov (T u) (T v)
  rw [Fin.sum_univ_succAbove _ i] at h1
  have h2 := hMat (T u) (T v)
  rw [hLT v] at h2
  have h3 : inner ℝ (T u) (L v) = inner ℝ u v := by rw [← hsym, hLT]
  linarith

end W1Reduce

section W1Book

variable {d : ℕ} {κ : ℝ}

theorem mvbe_w1_bookkeeping [NeZero d] (C : MvbeRegularClass d κ) (hC : MvbeNegOpen C)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤)
    {β0 γ0 K : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ mvbeKSet d κ β0 γ0, r ≤ K)
    (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : ∀ x, ‖T x‖ ≤ 2 * ‖x‖) (hTs : ∀ x, ‖T.symm x‖ ≤ ‖x‖)
    (S' : MvbeSummands d) {b : ℝ} (hS' : S'.beta ≤ 8 * b)
    {B : Set (EuclideanSpace ℝ (Fin d))} (hB : B ∈ C.cls) :
    S'.dev (T '' B) ≤ 16 * K * (max b β0 *
      max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0) := by
  obtain ⟨Ĉ, hmem, hneg, hgam⟩ := mvbe_imageClassFacts d κ C T
  have hn1 : ‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using hTs x)
  have hn2 : ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hT
  have hc : ‖(T.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
      * max 1 ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ 2 := by
    have h2 : max 1 ‖(T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ≤ 2 :=
      max_le (by norm_num) hn2
    calc _ ≤ 1 * 2 := mul_le_mul hn1 h2 (le_max_of_le_left zero_le_one) zero_le_one
      _ = 2 := by norm_num
  have hĈ : Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ ENNReal.ofReal 2 * C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    hgam.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl)
  have hne : ENNReal.ofReal 2 * C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hγ
  have hĈne : Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤ :=
    ne_top_of_le_ne_top hne hĈ
  have hĈr : (Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal
      ≤ 2 * (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal := by
    have := ENNReal.toReal_mono hne hĈ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at this
  have hmemK : S'.dev (T '' B) / (max S'.beta β0 *
      max (Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0)
        ∈ mvbeKSet d κ β0 γ0 :=
    ⟨S', Ĉ, hneg hC, hĈne, T '' B, hmem B hB, rfl⟩
  have hKle := hK _ hmemK
  have hpos : 0 < max S'.beta β0 *
      max (Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0 :=
    mul_pos (lt_max_of_lt_right hβ0) (lt_max_of_lt_right hγ0)
  rw [div_le_iff₀ hpos] at hKle
  have hm1 := le_max_left b β0
  have hm2 := le_max_right b β0
  have hg1 := le_max_left (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0
  have hg2 := le_max_right (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0
  have h1 : max S'.beta β0 ≤ 8 * max b β0 := max_le (by linarith) (by linarith)
  have h2 : max (Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0
      ≤ 2 * max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0 :=
    max_le (by linarith) (by linarith)
  calc S'.dev (T '' B) ≤ K * (max S'.beta β0 *
        max (Ĉ.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0) := hKle
    _ ≤ K * ((8 * max b β0) * (2 * max
        (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (le_max_of_le_right hγ0.le)
        (by linarith)) hK0
    _ = _ := by ring

end W1Book

section W1Final

variable {d : ℕ} {κ : ℝ}

/-- The whitened summands `(T X_j)_{j ≠ i}`. -/
noncomputable def mvbe_w1_reduce {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    (hprob : ∀ j, IsProbabilityMeasure (ν j))
    (hmom : ∀ j, Integrable (fun x => ‖x‖ ^ 3) (ν j)) (hmean : ∀ j, ∫ x, x ∂ν j = 0)
    (i : Fin (n + 1)) (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT2 : ∀ x, ‖T x‖ ≤ 2 * ‖x‖)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin d),
      ∑ j : Fin n, ∫ x, inner ℝ (T x) u * inner ℝ (T x) v ∂ν (i.succAbove j) = inner ℝ u v) :
    MvbeSummands d where
  n := n
  ν := fun j => (ν (i.succAbove j)).map T
  prob := fun j => by
    haveI := hprob (i.succAbove j)
    exact Measure.isProbabilityMeasure_map T.continuous.measurable.aemeasurable
  mom := fun j => mvbe_w1_map_mom _ (hmom _) T hT2
  mean := fun j => by
    haveI := hprob (i.succAbove j)
    exact mvbe_w1_map_mean _ (hmom _) (hmean _) T
  cov := fun u v => by
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcov u v)
    rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]

theorem mvbe_w1_reduce_beta_le {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    (hprob : ∀ j, IsProbabilityMeasure (ν j))
    (hmom : ∀ j, Integrable (fun x => ‖x‖ ^ 3) (ν j)) (hmean : ∀ j, ∫ x, x ∂ν j = 0)
    (i : Fin (n + 1)) (T : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT2 : ∀ x, ‖T x‖ ≤ 2 * ‖x‖)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin d),
      ∑ j : Fin n, ∫ x, inner ℝ (T x) u * inner ℝ (T x) v ∂ν (i.succAbove j) = inner ℝ u v) :
    (mvbe_w1_reduce ν hprob hmom hmean i T hT2 hcov).beta ≤ 8 * ∑ j, ∫ x, ‖x‖ ^ 3 ∂ν j := by
  have hi : 0 ≤ ∫ x, ‖x‖ ^ 3 ∂ν i := integral_nonneg fun x => by positivity
  rw [Fin.sum_univ_succAbove _ i, mul_add]
  have h : (mvbe_w1_reduce ν hprob hmom hmean i T hT2 hcov).beta
      ≤ ∑ j : Fin n, 8 * ∫ x, ‖x‖ ^ 3 ∂ν (i.succAbove j) :=
    Finset.sum_le_sum fun j _ => mvbe_w1_map_beta_le _ (hmom _) T hT2
  rw [← Finset.mul_sum] at h
  linarith

/-- The whitened core of the bootstrapping step, in components. -/
theorem mvbe_w1_cond_dev_aux [NeZero d] (C : MvbeRegularClass d κ) (hC : MvbeNegOpen C)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤)
    {n : ℕ} (ν : Fin (n + 1) → Measure (EuclideanSpace ℝ (Fin d)))
    (hprob : ∀ j, IsProbabilityMeasure (ν j))
    (hmom : ∀ j, Integrable (fun x => ‖x‖ ^ 3) (ν j)) (hmean : ∀ j, ∫ x, x ∂ν j = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin d),
      ∑ j, ∫ x, inner ℝ x u * inner ℝ x v ∂ν j = inner ℝ u v)
    (i : Fin (n + 1)) (hsm : ∫ x, ‖x‖ ^ 2 ∂ν i ≤ 1 / 4)
    {β0 γ0 K : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ mvbeKSet d κ β0 γ0, r ≤ K)
    (m' : EuclideanSpace ℝ (Fin d)) {A' : Set (EuclideanSpace ℝ (Fin d))} (hA' : A' ∈ C.cls) :
    |(mvbeCondLaw (⟨n + 1, ν, hprob, hmom, hmean, hcov⟩ : MvbeSummands d) i m' A').toReal
        - (multivariateGaussian m'
          (mvbeSigma (⟨n + 1, ν, hprob, hmom, hmean, hcov⟩ : MvbeSummands d) i) A').toReal|
      ≤ 16 * K * (max (MvbeSummands.beta
          (⟨n + 1, ν, hprob, hmom, hmean, hcov⟩ : MvbeSummands d)) β0 *
        max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0) := by
  haveI : ∀ j, IsProbabilityMeasure (ν j) := hprob
  set S : MvbeSummands d := ⟨n + 1, ν, hprob, hmom, hmean, hcov⟩ with hS
  have hM : (mvbeSigma S i).PosSemidef := mvbe_w1_sigma_psd S i hsm
  have hlo : ∀ v : EuclideanSpace ℝ (Fin d), 1 / 4 * ‖v‖ ^ 2
      ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (mvbeSigma S i) v) := fun v => by
    have := (mvbe_w1_sigma_quad S i hsm v).1
    have h0 := sq_nonneg ‖v‖
    exact le_trans (by linarith) this
  have hhi : ∀ v : EuclideanSpace ℝ (Fin d),
      inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (mvbeSigma S i) v) ≤ ‖v‖ ^ 2 :=
    fun v => (mvbe_w1_sigma_quad S i hsm v).2
  obtain ⟨T, hT, hT2, hTs⟩ := mvbe_w1_exists_equiv hM hlo hhi
  have hMat : ∀ u v : EuclideanSpace ℝ (Fin d),
      inner ℝ u v - ∫ x, inner ℝ x u * inner ℝ x v ∂ν i
        = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (mvbeSigma S i))
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (mvbeSigma S i)) v)) := fun u v => by
    rw [mvbe_w1_sqrt_sq hM]
    exact (mvbe_w1_sigma_bilin S i u v).symm
  have hcov' := mvbe_w1_red_cov ν hcov i _ T hT (mvbe_w1_sqrt_symm (mvbeSigma S i)) hMat
  set S' := mvbe_w1_reduce ν hprob hmom hmean i T hT2 hcov' with hS'
  have hb : 0 ≤ ∑ j, ∫ x, ‖x‖ ^ 3 ∂ν j :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  have hB : (fun z : EuclideanSpace ℝ (Fin d) => z + m') ⁻¹' A' ∈ C.cls := by
    rw [mvbe_preimage_add_eq_image_add_neg]
    exact C.a1_translate A' hA' (-m')
  have hbk := mvbe_w1_bookkeeping C hC hγ hβ0 hγ0 hK0 hK T hT2 hTs S'
    (mvbe_w1_reduce_beta_le ν hprob hmom hmean i T hT2 hcov') hB
  have hAm : MeasurableSet A' := C.measurableSet_mem A' hA'
  have e1 : mvbeCondLaw S i m' A' = (Measure.pi S'.ν)
      {ω | ∑ j, ω j ∈ T '' ((fun z => z + m') ⁻¹' A')} :=
    mvbe_w1_condLaw_eq ν i T m' hAm
  have e2 : multivariateGaussian m' (mvbeSigma S i) A'
      = stdGaussian (EuclideanSpace ℝ (Fin d)) (T '' ((fun z => z + m') ⁻¹' A')) :=
    mvbe_w1_gauss_eq _ T hT m' hAm
  rw [e1, e2]
  exact hbk

/-- **Raic's estimate of `D_{i,A}`** (bootstrapping step).  If `E‖X_i‖² ≤ 1/4`, the law of
`W_i + m'` differs from `N(m', Σ_i)` on a class set `A'` by at most `16 K β̄ γ̄`. -/
theorem mvbe_cond_dev [NeZero d] (C : MvbeRegularClass d κ) (hC : MvbeNegOpen C)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤)
    (S : MvbeSummands d) (i : Fin S.n) (hsm : ∫ x, ‖x‖ ^ 2 ∂S.ν i ≤ 1 / 4)
    {β0 γ0 K : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) (hK0 : 0 ≤ K)
    (hK : ∀ r ∈ mvbeKSet d κ β0 γ0, r ≤ K)
    (m' : EuclideanSpace ℝ (Fin d)) {A' : Set (EuclideanSpace ℝ (Fin d))} (hA' : A' ∈ C.cls) :
    |(mvbeCondLaw S i m' A').toReal - (multivariateGaussian m' (mvbeSigma S i) A').toReal|
      ≤ 16 * K * (max S.beta β0 *
        max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0) := by
  obtain ⟨n, ν, hprob, hmom, hmean, hcov⟩ := S
  cases n with
  | zero => exact i.elim0
  | succ n =>
    exact mvbe_w1_cond_dev_aux C hC hγ ν hprob hmom hmean hcov i hsm hβ0 hγ0 hK0 hK m' hA'

end W1Final


end W1Cond

section W3Interp

noncomputable section

open Filter Topology
open scoped Convolution NNReal

section Formula

variable {d : ℕ}

theorem mvbe_w3_herm_two (z u : EuclideanSpace ℝ (Fin d)) :
    mehlerNHerm 2 z u = inner ℝ z u ^ 2 - ‖u‖ ^ 2 := by
  have h2 : Polynomial.hermite 2 = Polynomial.X ^ 2 - 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Polynomial.hermite_succ, Polynomial.hermite_one]
    simp [pow_two]
  by_cases hu : u = 0
  · subst hu
    simp [mehlerNHerm]
  · have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
    simp only [mehlerNHerm, h2, map_sub, map_pow, Polynomial.aeval_X, map_one]
    field_simp

theorem mvbe_w3_integrable_inner_sq (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => inner ℝ z u ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h := (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin d))) (innerSL ℝ u) 2
    (by simp)).integrable_sq
  refine h.congr (ae_of_all _ fun z => ?_)
  simp [real_inner_comm]

theorem mvbe_w3_integrable_herm_two (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => inner ℝ z u ^ 2 - ‖u‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
  (mvbe_w3_integrable_inner_sq u).sub (integrable_const _)

theorem mvbe_w3_integrable_herm_two_one (j : Fin d) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
      inner ℝ z (EuclideanSpace.single j (1 : ℝ)) ^ 2 - 1)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have := mvbe_w3_integrable_herm_two (EuclideanSpace.single j (1 : ℝ))
  simpa using this

theorem mvbe_w3_mehlerIS_formula (a : ℝ) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hm : Measurable h) (hb : ∃ C, ∀ x, |h x| ≤ C) (hs : 0 < Real.sin a)
    (w : EuclideanSpace ℝ (Fin d)) :
    mehlerIS (mehlerI a h) w =
      (∑ k : Fin d, (Real.cos a / Real.sin a) ^ 2 *
        ∫ z, h (Real.cos a • w + Real.sin a • z) *
          (inner ℝ z (EuclideanSpace.single k (1 : ℝ)) ^ 2 - 1)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
      - Real.cos a / Real.sin a *
        ∫ z, h (Real.cos a • w + Real.sin a • z) * inner ℝ z w
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  unfold mehlerIS
  have hN : mehlerI a h = mehlerN a h := rfl
  rw [hN]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mehlerN_iteratedDeriv_line a hm hb hs 2 w (EuclideanSpace.single k (1 : ℝ))]
    simp_rw [mvbe_w3_herm_two]
    simp
  · rw [mehlerN_fderiv_apply a hm hb.choose_spec hs w w]

theorem mvbe_w3_tendsto_integral_mul {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C0 : ℝ} (hg : ∀ k, Measurable (g k))
    (hC : ∀ k x, |g k x| ≤ C0) (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)))
    (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Integrable φ (stdGaussian (EuclideanSpace ℝ (Fin d)))) :
    Tendsto (fun k => ∫ z, g k (Real.cos a • w + Real.sin a • z) * φ z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) atTop
      (𝓝 (∫ z, f (Real.cos a • w + Real.sin a • z) * φ z
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))) := by
  refine tendsto_integral_of_dominated_convergence (fun z => C0 * |φ z|) ?_ ?_ ?_ ?_
  · intro k
    exact (((hg k).comp (by fun_prop)).aestronglyMeasurable).mul hφ.aestronglyMeasurable
  · exact hφ.abs.const_mul C0
  · intro k
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC k _) (abs_nonneg _)
  · exact ae_of_all _ fun z => (hlim _).mul_const _

theorem mvbe_w3_tendsto_mehlerIS {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C0 : ℝ} (hg : ∀ k, Measurable (g k))
    (hC : ∀ k x, |g k x| ≤ C0) (hmf : Measurable f) (hbf : ∃ C, ∀ x, |f x| ≤ C)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)))
    {a : ℝ} (hs : 0 < Real.sin a) (w : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k => mehlerIS (mehlerI a (g k)) w) atTop (𝓝 (mehlerIS (mehlerI a f) w)) := by
  have e : (fun k => mehlerIS (mehlerI a (g k)) w) = fun k =>
      (∑ j : Fin d, (Real.cos a / Real.sin a) ^ 2 *
        ∫ z, g k (Real.cos a • w + Real.sin a • z) *
          (inner ℝ z (EuclideanSpace.single j (1 : ℝ)) ^ 2 - 1)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
      - Real.cos a / Real.sin a *
        ∫ z, g k (Real.cos a • w + Real.sin a • z) * inner ℝ z w
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    funext fun k => mvbe_w3_mehlerIS_formula a (hg k) ⟨C0, hC k⟩ hs w
  rw [e, mvbe_w3_mehlerIS_formula a hmf hbf hs w]
  refine Tendsto.sub (tendsto_finsetSum _ fun j _ => ?_) ?_
  · have := mvbe_w3_tendsto_integral_mul hg hC hlim a w
      (mvbe_w3_integrable_herm_two_one j)
    exact this.const_mul _
  · exact (mvbe_w3_tendsto_integral_mul hg hC hlim a w (mehlerI_integrable_inner w)).const_mul _

theorem mvbe_w3_tendsto_mehlerIAng {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C1 : ℝ} (hC1 : 0 ≤ C1)
    (hgd : ∀ k, Continuous (fderiv ℝ (g k)))
    (hb : ∀ k x, ‖fderiv ℝ (g k) x‖ ≤ C1)
    (hlim : ∀ x, Tendsto (fun k => fderiv ℝ (g k) x) atTop (𝓝 (fderiv ℝ f x)))
    (a : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k => mehlerIAng (g k) a w) atTop (𝓝 (mehlerIAng f a w)) := by
  unfold mehlerIAng
  refine tendsto_integral_of_dominated_convergence (fun z => C1 * (‖w‖ + ‖z‖)) ?_ ?_ ?_ ?_
  · intro k
    exact (((hgd k).comp (by fun_prop)).clm_apply (by fun_prop)).aestronglyMeasurable
  · exact ((integrable_const ‖w‖).add (mehlerI_integrable_norm d)).const_mul C1
  · intro k
    exact ae_of_all _ fun z => mehlerI_angle_integrand_norm_le hC1 (hb k) a w z
  · refine ae_of_all _ fun z => ?_
    exact ((ContinuousLinearMap.apply ℝ ℝ
      (-(Real.sin a) • w + Real.cos a • z)).continuous.tendsto _).comp (hlim _)

/-- Pointwise identity `tan a · S U_a f (w) = ∂_a U_a f (w)` for a `C^{1}_b` function `f` which is
the pointwise limit of `C²_b` functions with uniformly bounded gradient and converging gradient. -/
theorem mvbe_w3_tan_mehlerIS_eq {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C0 C1 : ℝ} (hC1 : 0 ≤ C1)
    (hg2 : ∀ k, mehlerIClassC2b (g k))
    (hC : ∀ k x, |g k x| ≤ C0) (hb : ∀ k x, ‖fderiv ℝ (g k) x‖ ≤ C1)
    (hmf : Measurable f) (hbf : ∃ C, ∀ x, |f x| ≤ C)
    (hlim : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)))
    (hlimd : ∀ x, Tendsto (fun k => fderiv ℝ (g k) x) atTop (𝓝 (fderiv ℝ f x)))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < Real.pi / 2) (w : EuclideanSpace ℝ (Fin d)) :
    Real.tan a * mehlerIS (mehlerI a f) w = mehlerIAng f a w := by
  have hs : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have h1 : Tendsto (fun k => Real.tan a * mehlerIS (mehlerI a (g k)) w) atTop
      (𝓝 (Real.tan a * mehlerIS (mehlerI a f) w)) :=
    (mvbe_w3_tendsto_mehlerIS (fun k => (hg2 k).1.continuous.measurable) hC hmf hbf hlim hs
      w).const_mul _
  have h2 := mvbe_w3_tendsto_mehlerIAng hC1
    (fun k => ((hg2 k).1.continuous_fderiv (by norm_num))) hb hlimd a w
  have h3 : (fun k => Real.tan a * mehlerIS (mehlerI a (g k)) w)
      = fun k => mehlerIAng (g k) a w :=
    funext fun k => mehlerI_tan_mehlerIS (hg2 k) ha0 ha1 w
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end Formula

section Mollifier

variable {d : ℕ}

/-- The bump function of outer radius `1 / (k + 1)`. -/
def mvbe_w3_bump (d k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := 1 / ((k : ℝ) + 2)
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

/-- The normalised bump function (mollifier kernel). -/
def mvbe_w3_ker (d k : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (mvbe_w3_bump d k).normed volume

/-- The mollification `f_k = ker_k ⋆ f`. -/
def mvbe_w3_moll (d k : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (mvbe_w3_ker d k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

theorem mvbe_w3_ker_nonneg (k : ℕ) (t : EuclideanSpace ℝ (Fin d)) : 0 ≤ mvbe_w3_ker d k t :=
  (mvbe_w3_bump d k).nonneg_normed t

theorem mvbe_w3_ker_integrable (k : ℕ) : Integrable (mvbe_w3_ker d k) volume :=
  (mvbe_w3_bump d k).integrable_normed

theorem mvbe_w3_ker_integral (k : ℕ) : ∫ t, mvbe_w3_ker d k t = 1 :=
  (mvbe_w3_bump d k).integral_normed

theorem mvbe_w3_ker_continuous (k : ℕ) : Continuous (mvbe_w3_ker d k) :=
  (mvbe_w3_bump d k).continuous_normed

theorem mvbe_w3_moll_apply (k : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    mvbe_w3_moll d k f x = ∫ t, mvbe_w3_ker d k t * f (x - t) := by
  unfold mvbe_w3_moll
  rw [convolution_def]
  simp

theorem mvbe_w3_moll_contDiff (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) :
    ContDiff ℝ (⊤ : ℕ∞) (mvbe_w3_moll d k f) :=
  ((mvbe_w3_bump d k).hasCompactSupport_normed).contDiff_convolution_left _
    (mvbe_w3_bump d k).contDiff_normed (hf.locallyIntegrable)

theorem mvbe_w3_moll_abs_le (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} {C0 : ℝ}
    (h0 : ∀ x, |f x| ≤ C0) (x : EuclideanSpace ℝ (Fin d)) : |mvbe_w3_moll d k f x| ≤ C0 := by
  rw [mvbe_w3_moll_apply]
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => mvbe_w3_ker d k t * f (x - t)) (g := fun t => mvbe_w3_ker d k t * C0)
    ((mvbe_w3_ker_integrable k).mul_const C0)
    (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mvbe_w3_ker_nonneg k t)]
      exact mul_le_mul_of_nonneg_left (h0 _) (mvbe_w3_ker_nonneg k t))
  rw [integral_mul_const, mvbe_w3_ker_integral, one_mul] at h
  simpa using h

theorem mvbe_w3_moll_hasFDerivAt (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (mvbe_w3_moll d k f)
      (∫ t, mvbe_w3_ker d k t • fderiv ℝ f (x - t)) x := by
  have hfc : Continuous f := hf1.continuous
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  have e : mvbe_w3_moll d k f = fun x => ∫ t, mvbe_w3_ker d k t * f (x - t) :=
    funext (mvbe_w3_moll_apply k f)
  rw [e]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => mvbe_w3_ker d k t * f (x - t))
    (F' := fun x t => mvbe_w3_ker d k t • fderiv ℝ f (x - t))
    (bound := fun t => mvbe_w3_ker d k t * C1) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      ((mvbe_w3_ker_continuous k).mul (hfc.comp (by fun_prop))).aestronglyMeasurable
  · refine ((mvbe_w3_ker_integrable k).mul_const C0).mono'
      ((mvbe_w3_ker_continuous k).mul (hfc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mvbe_w3_ker_nonneg k t)]
    exact mul_le_mul_of_nonneg_left (h0 _) (mvbe_w3_ker_nonneg k t)
  · exact ((mvbe_w3_ker_continuous k).smul (hdc.comp (by fun_prop))).aestronglyMeasurable
  · refine ae_of_all _ fun t y _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mvbe_w3_ker_nonneg k t)]
    exact mul_le_mul_of_nonneg_left (h1 _) (mvbe_w3_ker_nonneg k t)
  · exact (mvbe_w3_ker_integrable k).mul_const C1
  · refine ae_of_all _ fun t y _ => ?_
    have h3 : HasFDerivAt (fun y => f (y - t)) (fderiv ℝ f (y - t)) y := by
      simpa using! (hf1.differentiable one_ne_zero (y - t)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).sub_const t)
    exact h3.const_mul (mvbe_w3_ker d k t)

theorem mvbe_w3_moll_fderiv_eq (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (mvbe_w3_moll d k f) x = ∫ t, mvbe_w3_ker d k t • fderiv ℝ f (x - t) :=
  (mvbe_w3_moll_hasFDerivAt k hf1 h0 h1 x).fderiv

theorem mvbe_w3_integrable_ker_smul_fderiv (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C1 : ℝ} (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun t => mvbe_w3_ker d k t • fderiv ℝ f (x - t)) volume := by
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  refine ((mvbe_w3_ker_integrable k).mul_const C1).mono'
    ((mvbe_w3_ker_continuous k).smul (hdc.comp (by fun_prop))).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mvbe_w3_ker_nonneg k t)]
  exact mul_le_mul_of_nonneg_left (h1 _) (mvbe_w3_ker_nonneg k t)

theorem mvbe_w3_moll_fderiv_norm_le (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (x : EuclideanSpace ℝ (Fin d)) : ‖fderiv ℝ (mvbe_w3_moll d k f) x‖ ≤ C1 := by
  rw [mvbe_w3_moll_fderiv_eq k hf1 h0 h1 x]
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => mvbe_w3_ker d k t • fderiv ℝ f (x - t)) (g := fun t => mvbe_w3_ker d k t * C1)
    ((mvbe_w3_ker_integrable k).mul_const C1)
    (ae_of_all _ fun t => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mvbe_w3_ker_nonneg k t)]
      exact mul_le_mul_of_nonneg_left (h1 _) (mvbe_w3_ker_nonneg k t))
  rw [integral_mul_const, mvbe_w3_ker_integral, one_mul] at h
  exact h

theorem mvbe_w3_moll_fderiv_lipschitz (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) :
    LipschitzWith L (fderiv ℝ (mvbe_w3_moll d k f)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, mvbe_w3_moll_fderiv_eq k hf1 h0 h1 x, mvbe_w3_moll_fderiv_eq k hf1 h0 h1 y,
    ← integral_sub (mvbe_w3_integrable_ker_smul_fderiv k hf1 h1 x)
      (mvbe_w3_integrable_ker_smul_fderiv k hf1 h1 y)]
  have h := norm_integral_le_of_norm_le (μ := volume)
    (f := fun t => mvbe_w3_ker d k t • fderiv ℝ f (x - t) - mvbe_w3_ker d k t • fderiv ℝ f (y - t))
    (g := fun t => mvbe_w3_ker d k t * ((L : ℝ) * dist x y))
    ((mvbe_w3_ker_integrable k).mul_const _)
    (ae_of_all _ fun t => by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mvbe_w3_ker_nonneg k t),
        ← dist_eq_norm]
      refine mul_le_mul_of_nonneg_left ?_ (mvbe_w3_ker_nonneg k t)
      calc dist (fderiv ℝ f (x - t)) (fderiv ℝ f (y - t)) ≤ L * dist (x - t) (y - t) :=
            hL.dist_le_mul _ _
        _ = L * dist x y := by rw [dist_sub_right])
  rw [integral_mul_const, mvbe_w3_ker_integral, one_mul] at h
  exact h

theorem mvbe_w3_moll_iteratedFDeriv_two_le (k : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ 2 (mvbe_w3_moll d k f) x‖ ≤ L := by
  have h := norm_fderiv_le_of_lipschitz ℝ (mvbe_w3_moll_fderiv_lipschitz k hf1 h0 h1 hL)
    (x₀ := x)
  have e : ‖iteratedFDeriv ℝ 2 (mvbe_w3_moll d k f) x‖
      = ‖fderiv ℝ (fderiv ℝ (mvbe_w3_moll d k f)) x‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ (mvbe_w3_moll d k f)) (x := x)]
    exact (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := mvbe_w3_moll d k f) (x := x) (n := 1)).symm
  rw [e]
  exact h

theorem mvbe_w3_bump_rOut_tendsto :
    Tendsto (fun k : ℕ => (mvbe_w3_bump d k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem mvbe_w3_moll_tendsto {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k => mvbe_w3_moll d k f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := fun k => mvbe_w3_bump d k) (l := atTop) mvbe_w3_bump_rOut_tendsto hf x

theorem mvbe_w3_moll_fderiv_tendsto {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ} (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun k => fderiv ℝ (mvbe_w3_moll d k f) x) atTop (𝓝 (fderiv ℝ f x)) := by
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := fun k => mvbe_w3_bump d k) (l := atTop) mvbe_w3_bump_rOut_tendsto hdc x
  refine this.congr fun k => ?_
  rw [mvbe_w3_moll_fderiv_eq k hf1 h0 h1 x, convolution_def]
  simp [mvbe_w3_ker]

/-- Mollification: a `C^{1,1}_b` function is the pointwise limit of `C²_b` functions with the
same bounds on `f` and `Df`, whose gradients converge pointwise to the gradient of `f`. -/
theorem mvbe_w3_mollify {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf1 : ContDiff ℝ 1 f) {C0 C1 : ℝ}
    (h0 : ∀ x, |f x| ≤ C0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C1)
    {L : ℝ≥0} (hL : LipschitzWith L (fderiv ℝ f)) :
    ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ, (∀ k, mehlerIClassC2b (g k)) ∧
      (∀ k x, |g k x| ≤ C0) ∧ (∀ k x, ‖fderiv ℝ (g k) x‖ ≤ C1) ∧
      (∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x))) ∧
      (∀ x, Tendsto (fun k => fderiv ℝ (g k) x) atTop (𝓝 (fderiv ℝ f x))) := by
  refine ⟨fun k => mvbe_w3_moll d k f, fun k => ⟨?_, ⟨C0, mvbe_w3_moll_abs_le k h0⟩,
    ⟨C1, mvbe_w3_moll_fderiv_norm_le k hf1 h0 h1⟩,
    ⟨L, mvbe_w3_moll_iteratedFDeriv_two_le k hf1 h0 h1 hL⟩⟩,
    fun k => mvbe_w3_moll_abs_le k h0, fun k => mvbe_w3_moll_fderiv_norm_le k hf1 h0 h1,
    mvbe_w3_moll_tendsto hf1.continuous, mvbe_w3_moll_fderiv_tendsto hf1 h0 h1⟩
  exact (mvbe_w3_moll_contDiff k hf1.continuous).of_le (WithTop.coe_le_coe.2 le_top)

end Mollifier

section Main

/-- **Raic's (2.5) for `C^{1,1}_b` functions**: the Slepian/Mehler interpolation identity for
`f` with `f`, `Df` bounded and `Df` Lipschitz.  Proof: mollify (`mvbe_w3_mollify`), obtain the
pointwise heat equation `tan a · S U_a f = ∂_a U_a f` in the limit
(`mvbe_w3_tan_mehlerIS_eq`), and integrate `∂_a U_a f` over `[0, π/2]` as in
`mehlerI_interpolation`. -/
theorem mvbe_mehlerInterp_c11 (d : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → EuclideanSpace ℝ (Fin d)) (hW : Measurable W)
    (hWint : Integrable (fun ω => ‖W ω‖) P) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf1 : ContDiff ℝ 1 f) (hf0 : ∃ C, ∀ x, |f x| ≤ C) (hf1b : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hfL : ∃ L, LipschitzWith L (fderiv ℝ f)) :
    ∫ ω, f (W ω) ∂P - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -∫ a in Set.Ioo 0 (Real.pi / 2),
          Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P := by
  obtain ⟨C0, h0⟩ := hf0
  obtain ⟨C1, h1⟩ := hf1b
  obtain ⟨L, hL⟩ := hfL
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  obtain ⟨g, hg2, hC, hb, hlim, hlimd⟩ := mvbe_w3_mollify hf1 h0 h1 hL
  have hf : mehlerIClassC1b f := ⟨hf1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩
  have hmf : Measurable f := hf1.continuous.measurable
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => mehlerI_integral_hasDerivAt P W hW hWint hf a)
    (mehlerI_integral_angle_intervalIntegrable P W hW hWint hf)
  have hΦ0 : ∫ ω, mehlerI 0 f (W ω) ∂P = ∫ ω, f (W ω) ∂P := by simp [mehlerI]
  have hΦ1 : ∫ ω, mehlerI (Real.pi / 2) f (W ω) ∂P
      = ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    simp [mehlerI]
  have hIoo : ∫ a in Set.Ioo 0 (Real.pi / 2), ∫ ω, mehlerIAng f a (W ω) ∂P
      = ∫ a in Set.Ioo 0 (Real.pi / 2),
          Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (W ω) ∂P := by
    refine setIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (mvbe_w3_tan_mehlerIS_eq hC1 hg2 hC hb hmf ⟨C0, h0⟩ hlim hlimd ha.1 ha.2 (W ω)).symm
  rw [← hIoo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi, hftc, hΦ0,
    hΦ1]
  ring

end Main

end


end W3Interp

section InterpFacts

/-- **Raic's (2.5) for `C^{1,1}_b` functions** is proved. -/
theorem mvbe_mehlerInterp : MvbeMehlerInterp := by
  intro d Ω _ P _ W hW hWint f h1 h2 h3 h4
  exact mvbe_mehlerInterp_c11 d Ω P W hW hWint f h1 h2 h3 h4

/-- **Mehler smoothing facts** (Raic (2.5)-(2.7), Lemma 2.6; packet P8a): `U_α f` is `C³` with
bounded derivatives of orders `1, 2, 3` for bounded Borel `f` and `0 < α < π/2`, and the
Slepian interpolation identity holds for `C^{1,1}_b` functions. -/
def MvbeMehlerFacts : Prop :=
  (∀ (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ), Measurable f → ∀ M : ℝ, (∀ x, |f x| ≤ M) →
    ∀ a : ℝ, 0 < a → a < Real.pi / 2 →
      ContDiff ℝ 3 (mehlerI a f) ∧ (∃ C, ∀ x, ‖fderiv ℝ (mehlerI a f) x‖ ≤ C) ∧
      (∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 (mehlerI a f) x‖ ≤ C) ∧
      (∃ C, ∀ x, ‖iteratedFDeriv ℝ 3 (mehlerI a f) x‖ ≤ C)) ∧ MvbeMehlerInterp

/-- The Mehler facts are proved (`mvbe_mehlerI_smooth`, `mvbe_mehlerInterp`). -/
theorem mvbe_mehlerFacts : MvbeMehlerFacts :=
  ⟨fun _ _ hf _ hM _ ha0 ha1 => mvbe_mehlerI_smooth hf hM ha0 ha1, mvbe_mehlerInterp⟩

end InterpFacts

section S3a

section CondStein

variable {d : ℕ}

/-- The tensor `T_i(x, θ) = E D³g(W_i + θ x)` (a continuous trilinear form). -/
noncomputable def mvbeTens (S : MvbeSummands d) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (i : Fin S.n) (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin d)) ℝ :=
  ∫ y, iteratedFDeriv ℝ 3 g y ∂(mvbeCondLaw S i (θ • x))

/-- The law of `(W_i, X_i)` is the product of the laws. -/
theorem mvbe_law_pair (S : MvbeSummands d) (i : Fin S.n) :
    (Measure.pi S.ν).map (fun ω => (mvbeWithout i ω, ω i))
      = ((Measure.pi S.ν).map (mvbeWithout i)).prod (S.ν i) := by
  have hmW : Measurable (mvbeWithout (E := EuclideanSpace ℝ (Fin d)) i) :=
    mvbe_measurable_without i
  have hmX : Measurable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ω i) :=
    measurable_pi_apply i
  have hmap := (mvbe_indep_without S.ν i).map_prod_eq_prod_map_map hmW.aemeasurable
    hmX.aemeasurable
  have hX : (Measure.pi S.ν).map (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ω i) = S.ν i :=
    (measurePreserving_eval S.ν i).map_eq
  rw [hX] at hmap
  exact hmap

/-- The pushforward of `P ⊗ (ν_i ⊗ λ)` under `(ω, x̃, θ) ↦ (W_i, (X_i, (x̃, θ)))`. -/
theorem mvbe_law_Psi (S : MvbeSummands d) (i : Fin S.n)
    (ρ' : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) [IsProbabilityMeasure ρ'] :
    ((Measure.pi S.ν).prod ρ').map
        (fun p : (Fin S.n → EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
          (mvbeWithout i p.1, (p.1 i, p.2)))
      = ((Measure.pi S.ν).map (mvbeWithout i)).prod ((S.ν i).prod ρ') := by
  have hmW : Measurable (mvbeWithout (E := EuclideanSpace ℝ (Fin d)) i) :=
    mvbe_measurable_without i
  have hmX : Measurable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ω i) :=
    measurable_pi_apply i
  have hΦ : Measurable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) =>
      (mvbeWithout i ω, ω i)) := hmW.prodMk hmX
  have h1 := Measure.map_prod_map (Measure.pi S.ν) ρ' hΦ measurable_id
  rw [Measure.map_id] at h1
  have h2 := (measurePreserving_prodAssoc ((Measure.pi S.ν).map (mvbeWithout i)) (S.ν i) ρ').map_eq
  have e : (fun p : (Fin S.n → EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      (mvbeWithout i p.1, (p.1 i, p.2)))
      = (MeasurableEquiv.prodAssoc : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × ℝ) ≃ᵐ _) ∘
        (Prod.map (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => (mvbeWithout i ω, ω i))
          (id : EuclideanSpace ℝ (Fin d) × ℝ → _)) := by
    funext p
    rfl
  rw [e, ← Measure.map_map MeasurableEquiv.prodAssoc.measurable (hΦ.prodMap measurable_id),
    ← h1, mvbe_law_pair, h2]


theorem mvbe_D3_continuous {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) :
    Continuous (iteratedFDeriv ℝ 3 g) := hg.continuous_iteratedFDeriv (by norm_num)

theorem mvbe_D3_integrable {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] : Integrable (iteratedFDeriv ℝ 3 g) μ :=
  Integrable.of_bound (mvbe_D3_continuous hg).aestronglyMeasurable C₃
    (ae_of_all _ hb3)

theorem mvbe_D3_apply_integrable {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g)
    {C₃ : ℝ} (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (m : Fin 3 → EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => iteratedFDeriv ℝ 3 g y m) μ := by
  refine Integrable.of_bound (mvbe_continuous_iter (k := 3) hg m).aestronglyMeasurable
    (C₃ * ∏ i, ‖m i‖) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  have := (iteratedFDeriv ℝ 3 g y).le_opNorm m
  rw [Real.norm_eq_abs] at this
  exact this.trans
    (mul_le_mul_of_nonneg_right (hb3 y) (Finset.prod_nonneg fun i _ => norm_nonneg _))

/-- `E` of the third-order integrand against the conditional law is the evaluation of the tensor. -/
theorem mvbe_tens_apply {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (S : MvbeSummands d) (i : Fin S.n)
    (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (m : Fin 3 → EuclideanSpace ℝ (Fin d)) :
    mvbeTens S g i x θ m = ∫ y, iteratedFDeriv ℝ 3 g y m ∂(mvbeCondLaw S i (θ • x)) :=
  ContinuousMultilinearMap.integral_apply (mvbe_D3_integrable hg hb3 _) m

/-- The conditional Stein formula for one summand. -/
theorem mvbe_cond_stein_i (S : MvbeSummands d) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ 3 g) {C₃ : ℝ} (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (i : Fin S.n) :
    ∫ p : (Fin S.n → EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × ℝ),
        mvbeSteinRem g (mvbeWithout i p.1) (p.1 i) p.2.1 p.2.2
        ∂((Measure.pi S.ν).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
      = ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
        ((mvbeTens S g i q.1 q.2.2) ![q.1, q.2.1, q.2.1]
          - (1 - q.2.2) * (mvbeTens S g i q.1 q.2.2) ![q.1, q.1, q.1])
        ∂((S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply]⟩
  set ρ' := (S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) with hρ'
  haveI : IsProbabilityMeasure ρ' := inferInstance
  set Pi := (Measure.pi S.ν).map (mvbeWithout i) with hPi
  haveI : IsProbabilityMeasure Pi :=
    Measure.isProbabilityMeasure_map (mvbe_measurable_without i).aemeasurable
  have hc3 := mvbe_D3_continuous hg
  set G : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ))
      → ℝ := fun z => mvbeSteinRem g z.1 z.2.1 z.2.2.1 z.2.2.2 with hG
  have hGc : Continuous G := by
    have hpt : Continuous fun z : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
        (EuclideanSpace ℝ (Fin d) × ℝ)) => z.1 + z.2.2.2 • z.2.1 :=
      continuous_fst.add ((continuous_snd.comp (continuous_snd.comp continuous_snd)).smul
        (continuous_fst.comp continuous_snd))
    have hm1 : Continuous fun z : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
        (EuclideanSpace ℝ (Fin d) × ℝ)) =>
        (![z.2.1, z.2.2.1, z.2.2.1] : Fin 3 → EuclideanSpace ℝ (Fin d)) := by
      refine continuous_pi fun j => ?_
      fin_cases j <;> simp
      · exact continuous_fst.comp continuous_snd
      · exact continuous_fst.comp (continuous_snd.comp continuous_snd)
      · exact continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hm2 : Continuous fun z : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) ×
        (EuclideanSpace ℝ (Fin d) × ℝ)) =>
        (![z.2.1, z.2.1, z.2.1] : Fin 3 → EuclideanSpace ℝ (Fin d)) := by
      refine continuous_pi fun j => ?_
      fin_cases j <;> simp <;> exact continuous_fst.comp continuous_snd
    simp only [hG, mvbeSteinRem]
    exact ((hc3.comp hpt).eval hm1).sub
      ((continuous_const.sub (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
        ((hc3.comp hpt).eval hm2))
  have hΨm : Measurable (fun p : (Fin S.n → EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × ℝ) => (mvbeWithout i p.1, (p.1 i, p.2))) :=
    ((mvbe_measurable_without i).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  have hlaw := mvbe_law_Psi S i ρ'
  have hint : Integrable G (Pi.prod ((S.ν i).prod ρ')) := by
    rw [← hlaw]
    refine (integrable_map_measure hGc.aestronglyMeasurable hΨm.aemeasurable).2 ?_
    exact mvbe_integrable_steinRem S.ν S.mom hg hb3 i
  calc _ = ∫ p, G ((fun p : (Fin S.n → EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × ℝ)
          => (mvbeWithout i p.1, (p.1 i, p.2))) p) ∂((Measure.pi S.ν).prod ρ') := rfl
    _ = ∫ z, G z ∂(((Measure.pi S.ν).prod ρ').map (fun p : (Fin S.n → EuclideanSpace ℝ (Fin d)) ×
          (EuclideanSpace ℝ (Fin d) × ℝ) => (mvbeWithout i p.1, (p.1 i, p.2)))) :=
        (integral_map hΨm.aemeasurable hGc.aestronglyMeasurable).symm
    _ = ∫ z, G z ∂(Pi.prod ((S.ν i).prod ρ')) := by rw [hlaw]
    _ = ∫ q, ∫ w, G (w, q) ∂Pi ∂((S.ν i).prod ρ') := integral_prod_symm G hint
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      obtain ⟨x, x', θ⟩ := q
      haveI : IsProbabilityMeasure (mvbeCondLaw S i (θ • x)) := inferInstance
      have hI : ∀ m : Fin 3 → EuclideanSpace ℝ (Fin d),
          Integrable (fun y => iteratedFDeriv ℝ 3 g y m) (mvbeCondLaw S i (θ • x)) :=
        fun m => mvbe_D3_apply_integrable hg hb3 _ m
      have hshift : ∫ w, G (w, (x, (x', θ))) ∂Pi
          = ∫ y, (iteratedFDeriv ℝ 3 g y ![x, x', x']
              - (1 - θ) * iteratedFDeriv ℝ 3 g y ![x, x, x]) ∂(mvbeCondLaw S i (θ • x)) := by
        unfold mvbeCondLaw
        rw [integral_map (measurable_add_const (θ • x)).aemeasurable]
        · rfl
        · exact (((mvbe_continuous_iter (k := 3) hg ![x, x', x']).sub
            (continuous_const.mul
              (mvbe_continuous_iter (k := 3) hg ![x, x, x])))).aestronglyMeasurable
      dsimp only
      rw [hshift, integral_sub (hI _) ((hI _).const_mul _), integral_const_mul,
        mvbe_tens_apply hg hb3, mvbe_tens_apply hg hb3]

end CondStein


end S3a

section S3b

section FixedA

variable {d : ℕ}

theorem mvbe_ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) : ENNReal.ofReal |∫ x, f x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
  have h := norm_integral_le_lintegral_norm (μ := μ) f
  simp only [Real.norm_eq_abs] at h
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_toReal_le

/-- The family defining `mvbeDiag3` is bounded above. -/
theorem mvbe_diag_bdd {g : EuclideanSpace ℝ (Fin d) → ℝ} {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] :
    BddAbove (Set.range fun u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} =>
      |∫ y, iteratedFDeriv ℝ 3 g y ![u.1, u.1, u.1] ∂μ|) := by
  refine ⟨C₃, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hu := u.2
  have hb : ∀ y, ‖iteratedFDeriv ℝ 3 g y ![u.1, u.1, u.1]‖ ≤ C₃ := by
    intro y
    rw [Real.norm_eq_abs]
    have h1 := mvbe_abs_apply_three_le (iteratedFDeriv ℝ 3 g y) u.1 u.1 u.1
    have h2 : ‖u.1‖ * ‖u.1‖ * ‖u.1‖ ≤ 1 := by
      have h0 := norm_nonneg u.1
      calc ‖u.1‖ * ‖u.1‖ * ‖u.1‖ ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    have hC : 0 ≤ C₃ := (norm_nonneg _).trans (hb3 0)
    calc _ ≤ ‖iteratedFDeriv ℝ 3 g y‖ * (‖u.1‖ * ‖u.1‖ * ‖u.1‖) := h1
      _ ≤ C₃ * 1 := mul_le_mul (hb3 y) h2 (by positivity) hC
      _ = C₃ := mul_one _
  have := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hb)
  simpa [Real.norm_eq_abs] using this

theorem mvbe_diag_le {g : EuclideanSpace ℝ (Fin d) → ℝ} {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ≤ 1) :
    |∫ y, iteratedFDeriv ℝ 3 g y ![u, u, u] ∂μ| ≤ mvbeDiag3 g μ :=
  le_ciSup (f := fun u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} =>
    |∫ y, iteratedFDeriv ℝ 3 g y ![u.1, u.1, u.1] ∂μ|) (mvbe_diag_bdd hb3 μ) ⟨u, hu⟩

/-- Polarisation: `‖T_i(x, θ)‖ ≤ (9/2) sup_{‖u‖≤1} |T_i(x, θ)(u, u, u)|`. -/
theorem mvbe_tens_norm_le {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (S : MvbeSummands d) (i : Fin S.n)
    (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ) :
    ‖mvbeTens S g i x θ‖ ≤ 9 / 2 * mvbeDiag3 g (mvbeCondLaw S i (θ • x)) := by
  refine mvbe_polarization_norm (mvbeTens S g i x θ) ?_ ?_ ?_
  · intro p q r
    rw [mvbe_tens_apply hg hb3, mvbe_tens_apply hg hb3]
    exact integral_congr_ae (ae_of_all _ fun y => mvbe_iteratedFDeriv_three_swap12 hg y p q r)
  · intro p q r
    rw [mvbe_tens_apply hg hb3, mvbe_tens_apply hg hb3]
    exact integral_congr_ae (ae_of_all _ fun y => mvbe_iteratedFDeriv_three_swap23 hg y p q r)
  · intro u hu
    rw [mvbe_tens_apply hg hb3]
    exact mvbe_diag_le hb3 _ hu

/-- The pointwise bound for the integrand of the conditional Stein formula. -/
theorem mvbe_rem_abs_le {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (S : MvbeSummands d) (i : Fin S.n)
    (x x' : EuclideanSpace ℝ (Fin d)) (θ : ℝ) :
    |(mvbeTens S g i x θ) ![x, x', x'] - (1 - θ) * (mvbeTens S g i x θ) ![x, x, x]|
      ≤ 9 / 2 * mvbeDiag3 g (mvbeCondLaw S i (θ • x)) *
        (‖x‖ * ‖x'‖ ^ 2 + |1 - θ| * ‖x‖ ^ 3) := by
  set T := mvbeTens S g i x θ
  have hT := mvbe_tens_norm_le hg hb3 S i x θ
  have e1 := mvbe_abs_apply_three_le T x x' x'
  have e2 := mvbe_abs_apply_three_le T x x x
  have hN : 0 ≤ ‖T‖ := norm_nonneg _
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have e3 : |1 - θ| * |T ![x, x, x]| ≤ |1 - θ| * (‖T‖ * (‖x‖ * ‖x‖ * ‖x‖)) :=
    mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
  have h4 : ‖T‖ * (‖x‖ * ‖x'‖ * ‖x'‖) + |1 - θ| * (‖T‖ * (‖x‖ * ‖x‖ * ‖x‖))
      = ‖T‖ * (‖x‖ * ‖x'‖ ^ 2 + |1 - θ| * ‖x‖ ^ 3) := by ring
  have h5 : ‖T‖ * (‖x‖ * ‖x'‖ ^ 2 + |1 - θ| * ‖x‖ ^ 3)
      ≤ 9 / 2 * mvbeDiag3 g (mvbeCondLaw S i (θ • x)) * (‖x‖ * ‖x'‖ ^ 2 + |1 - θ| * ‖x‖ ^ 3) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  linarith

/-- **The conditional Stein bound for fixed `g`** (Raic (2.24) before the integration in `α`). -/
theorem mvbe_stein_bound (S : MvbeSummands d) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hg : ContDiff ℝ 3 g) {C₁ C₂ C₃ : ℝ} (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁)
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) :
    ENNReal.ofReal |∫ ω, mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) g (∑ i, ω i)
        ∂Measure.pi S.ν|
      ≤ ∑ i, ∫⁻ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
        ENNReal.ofReal (9 / 2 * mvbeDiag3 g (mvbeCondLaw S i (q.2.2 • q.1)) *
          (‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3))
        ∂((S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  rw [mvbe_stein_expectation S.ν S.mom S.mean S.cov hg hb1 hb2 hb3]
  refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  refine Finset.sum_le_sum fun i _ => ?_
  have hci := mvbe_cond_stein_i S hg hb3 i
  have h2 := mvbe_ofReal_abs_integral_le
    ((S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
    (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      (mvbeTens S g i q.1 q.2.2) ![q.1, q.2.1, q.2.1]
        - (1 - q.2.2) * (mvbeTens S g i q.1 q.2.2) ![q.1, q.1, q.1])
  refine (le_of_eq (congrArg (fun r : ℝ => ENNReal.ofReal |r|) hci)).trans ?_
  refine h2.trans (lintegral_mono fun q => ?_)
  exact ENNReal.ofReal_le_ofReal (mvbe_rem_abs_le hg hb3 S i q.1 q.2.1 q.2.2)

end FixedA


end S3b

section S3c

section Meas

variable {d : ℕ}

theorem mvbe_exists_dense_ball (d : ℕ) :
    ∃ D : ℕ → {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1}, DenseRange D := by
  haveI : Nonempty {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  exact TopologicalSpace.exists_dense_seq _

theorem mvbe_iSup_eq_iSup_seq {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Continuous φ)
    {D : ℕ → {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1}} (hD : DenseRange D)
    (hb : BddAbove (Set.range fun u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} => |φ u.1|)) :
    (⨆ u : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1}, |φ u.1|) = ⨆ k, |φ (D k).1| := by
  haveI : Nonempty {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  have hbk : BddAbove (Set.range fun k => |φ (D k).1|) := by
    obtain ⟨c, hc⟩ := hb
    exact ⟨c, by rintro _ ⟨k, rfl⟩; exact hc ⟨D k, rfl⟩⟩
  refine le_antisymm (ciSup_le fun u => ?_) (ciSup_le fun k => le_ciSup hb (D k))
  refine DenseRange.induction_on hD u ?_ (fun k => le_ciSup hbk k)
  exact isClosed_le (by fun_prop : Continuous fun v : {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} =>
    |φ v.1|) continuous_const

/-- The explicit Hermite formula for the diagonal third derivative of `U_a f`
(`mvbe_mehlerI_D3_formula`), as a function of `(a, z)` defined for all real `a`. -/
noncomputable def mvbeThetaHat (f : EuclideanSpace ℝ (Fin d) → ℝ) (u : EuclideanSpace ℝ (Fin d))
    (p : ℝ × EuclideanSpace ℝ (Fin d)) : ℝ :=
  (Real.cos p.1 / Real.sin p.1) ^ 3 *
    ∫ y, f (Real.cos p.1 • p.2 + Real.sin p.1 • y) * mehlerNHerm 3 y u
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

theorem mvbeThetaHat_measurable {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (u : EuclideanSpace ℝ (Fin d)) : Measurable (mvbeThetaHat f u) := by
  unfold mvbeThetaHat
  refine Measurable.mul ?_ ?_
  · exact ((Real.measurable_cos.comp measurable_fst).div
      (Real.measurable_sin.comp measurable_fst)).pow_const 3
  · have hc : Continuous fun q : (ℝ × EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) =>
        f (Real.cos q.1.1 • q.1.2 + Real.sin q.1.1 • q.2) * mehlerNHerm 3 q.2 u := by
      refine (hf.comp (by fun_prop)).mul ?_
      unfold mehlerNHerm
      exact continuous_const.mul
        (((Polynomial.hermite 3).continuous_aeval (A := ℝ)).comp
          ((continuous_snd.inner continuous_const).div_const _))
    exact (hc.measurable.stronglyMeasurable.integral_prod_right').measurable


/-- The explicit (Hermite) version of `u ↦ E ⟨∇³ U_a f (W_i + θ x), u^{⊗3}⟩`. -/
noncomputable def mvbeFt (S : MvbeSummands d) (i : Fin S.n)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (u : EuclideanSpace ℝ (Fin d))
    (p : ℝ × (EuclideanSpace ℝ (Fin d) × ℝ)) : ℝ :=
  ∫ w, mvbeThetaHat f u (p.1, w + p.2.2 • p.2.1) ∂((Measure.pi S.ν).map (mvbeWithout i))

theorem mvbeFt_measurable (S : MvbeSummands d) (i : Fin S.n)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) (u : EuclideanSpace ℝ (Fin d)) :
    Measurable (mvbeFt S i f u) := by
  unfold mvbeFt
  have hm : Measurable fun q : (ℝ × (EuclideanSpace ℝ (Fin d) × ℝ)) × EuclideanSpace ℝ (Fin d) =>
      mvbeThetaHat f u (q.1.1, q.2 + q.1.2.2 • q.1.2.1) := by
    refine (mvbeThetaHat_measurable hf u).comp ?_
    refine (measurable_fst.comp measurable_fst).prodMk ?_
    exact measurable_snd.add ((measurable_snd.comp (measurable_snd.comp measurable_fst)).smul
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

/-- A jointly measurable version of the diagonal norm `N_a(x, θ)`. -/
theorem mvbe_Ntilde (S : MvbeSummands d) (i : Fin S.n)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∃ Nt : ℝ × (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ, Measurable Nt ∧
      ∀ a : ℝ, 0 < a → a < Real.pi / 2 → ∀ (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ),
        Nt (a, (x, θ)) = mvbeDiag3 (mehlerI a f) (mvbeCondLaw S i (θ • x)) := by
  obtain ⟨D, hD⟩ := mvbe_exists_dense_ball d
  refine ⟨fun p => ⨆ k, |mvbeFt S i f (D k).1 p|, ?_, ?_⟩
  · exact Measurable.iSup fun k => (mvbeFt_measurable S i hf (D k).1).abs
  · intro a ha0 ha1 x θ
    obtain ⟨hg3, -, -, ⟨C₃, hb3⟩⟩ := mvbe_mehlerI_smooth hf.measurable hM ha0 ha1
    set g := mehlerI a f with hg
    have hφ : ∀ u : EuclideanSpace ℝ (Fin d), mvbeFt S i f u (a, (x, θ))
        = ∫ y, iteratedFDeriv ℝ 3 g y ![u, u, u] ∂(mvbeCondLaw S i (θ • x)) := by
      intro u
      unfold mvbeFt mvbeCondLaw
      rw [integral_map (measurable_add_const (θ • x)).aemeasurable
        (mvbe_continuous_iter (k := 3) hg3 ![u, u, u]).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      exact (mvbe_mehlerI_D3_formula hf.measurable hM ha0 ha1 _ u).symm
    have hcont : Continuous fun u : EuclideanSpace ℝ (Fin d) =>
        ∫ y, iteratedFDeriv ℝ 3 g y ![u, u, u] ∂(mvbeCondLaw S i (θ • x)) := by
      have : (fun u : EuclideanSpace ℝ (Fin d) =>
          ∫ y, iteratedFDeriv ℝ 3 g y ![u, u, u] ∂(mvbeCondLaw S i (θ • x)))
          = fun u => (mvbeTens S g i x θ) ![u, u, u] := by
        funext u
        exact (mvbe_tens_apply hg3 hb3 S i x θ _).symm
      rw [this]
      refine (mvbeTens S g i x θ).cont.comp ?_
      refine continuous_pi fun j => ?_
      fin_cases j <;> simp <;> exact continuous_id'
    simp only [mvbeDiag3]
    rw [mvbe_iSup_eq_iSup_seq hcont hD (mvbe_diag_bdd hb3 _)]
    simp only [hφ]

end Meas


end S3c

section S3d

section Weight

variable {d : ℕ}

instance mvbe_unitIcc_prob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply]⟩

theorem mvbe_integral_abs_one_sub :
    ∫ θ : ℝ, |1 - θ| ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 1 / 2 := by
  have h1 : ∫ θ : ℝ, |1 - θ| ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫ θ : ℝ in Set.Icc (0 : ℝ) 1, (1 - θ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    exact abs_of_nonneg (by linarith [hθ.2])
  rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  simp
  norm_num

theorem mvbe_weight_integrable (S : MvbeSummands d) (i : Fin S.n) :
    Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
        ‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3)
      ((S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have hU : Integrable (fun θ : ℝ => |1 - θ|) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (by fun_prop : Continuous fun θ : ℝ => |1 - θ|).integrableOn_Icc
  have hq1 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ‖q.1‖ ^ 2 * (1 : ℝ))
      ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (mvbe_integrable_sq (S.mom i)).mul_prod (integrable_const (1 : ℝ))
  have hq2 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => (1 : ℝ) * |1 - q.2|)
      ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (integrable_const (1 : ℝ)).mul_prod hU
  have hp1 := (mvbe_integrable_norm (S.mom i)).mul_prod hq1
  have hp2 := (S.mom i).mul_prod hq2
  refine (hp1.add hp2).congr (ae_of_all _ fun q => ?_)
  simp only [mul_one, one_mul, Pi.add_apply]
  ring


theorem mvbe_weight_lintegral_le (S : MvbeSummands d) (i : Fin S.n) :
    ∫⁻ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
        ENNReal.ofReal (‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3)
        ∂((S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
      ≤ ENNReal.ofReal (3 / 2 * ∫ x, ‖x‖ ^ 3 ∂S.ν i) := by
  set ρ' := (S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) with hρ'
  have hU : Integrable (fun θ : ℝ => |1 - θ|) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (by fun_prop : Continuous fun θ : ℝ => |1 - θ|).integrableOn_Icc
  have hq1 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ‖q.1‖ ^ 2 * (1 : ℝ)) ρ' :=
    (mvbe_integrable_sq (S.mom i)).mul_prod (integrable_const (1 : ℝ))
  have hq2 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => (1 : ℝ) * |1 - q.2|) ρ' :=
    (integrable_const (1 : ℝ)).mul_prod hU
  have hp1 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      ‖q.1‖ * (‖q.2.1‖ ^ 2 * (1 : ℝ))) ((S.ν i).prod ρ') :=
    (mvbe_integrable_norm (S.mom i)).mul_prod hq1
  have hp2 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      ‖q.1‖ ^ 3 * ((1 : ℝ) * |1 - q.2.2|)) ((S.ν i).prod ρ') :=
    (S.mom i).mul_prod hq2
  have hW := mvbe_weight_integrable S i
  rw [← ofReal_integral_eq_lintegral_ofReal hW (ae_of_all _ fun q => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set b := ∫ x, ‖x‖ ^ 3 ∂S.ν i with hb
  -- split the integral
  have hsplit : ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
      (‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3) ∂((S.ν i).prod ρ')
      = ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
          ‖q.1‖ * (‖q.2.1‖ ^ 2 * (1 : ℝ)) ∂((S.ν i).prod ρ')
        + ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
          ‖q.1‖ ^ 3 * ((1 : ℝ) * |1 - q.2.2|) ∂((S.ν i).prod ρ') := by
    rw [← integral_add hp1 hp2]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only [mul_one, one_mul]
    ring
  -- first term: Young's inequality `s t² ≤ s³/3 + 2 t³/3`
  have hyoung : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s * t ^ 2 ≤ s ^ 3 / 3 + 2 * t ^ 3 / 3 := by
    intro s t hs ht
    nlinarith [mul_nonneg (add_nonneg hs ht) (sq_nonneg (s - t)), sq_nonneg (s - t),
      mul_nonneg ht (sq_nonneg (s - t)), mul_nonneg hs (sq_nonneg (s - t))]
  have hm1 : ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ), ‖q.1‖ ^ 3
      ∂((S.ν i).prod ρ') = b := by
    rw [integral_fun_fst (f := fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 3)]
    simp [hb]
  have hm2 : ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ), ‖q.2.1‖ ^ 3
      ∂((S.ν i).prod ρ') = b := by
    rw [integral_fun_snd (f := fun y : EuclideanSpace ℝ (Fin d) × ℝ => ‖y.1‖ ^ 3),
      hρ', integral_fun_fst (f := fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 3)]
    simp [hb]
  have a1 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      ‖q.1‖ ^ 3) ((S.ν i).prod ρ') := by
    simpa using (S.mom i).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : EuclideanSpace ℝ (Fin d) × ℝ => (1 : ℝ)) ρ')
  have a2 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      ‖q.2.1‖ ^ 3) ((S.ν i).prod ρ') := by
    have : Integrable (fun y : EuclideanSpace ℝ (Fin d) × ℝ => ‖y.1‖ ^ 3) ρ' := by
      simpa using (S.mom i).mul_prod (integrable_const (1 : ℝ) :
        Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    simpa using (integrable_const (1 : ℝ) :
      Integrable (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) (S.ν i)).mul_prod this
  have hI1 : Integrable (fun q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) =>
      ‖q.1‖ ^ 3 / 3 + 2 * ‖q.2.1‖ ^ 3 / 3) ((S.ν i).prod ρ') :=
    (a1.div_const 3).add ((a2.const_mul 2).div_const 3)
  have hA1 : ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
      ‖q.1‖ * (‖q.2.1‖ ^ 2 * (1 : ℝ)) ∂((S.ν i).prod ρ') ≤ b := by
    calc _ ≤ ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
          (‖q.1‖ ^ 3 / 3 + 2 * ‖q.2.1‖ ^ 3 / 3) ∂((S.ν i).prod ρ') := by
          refine integral_mono hp1 hI1 fun q => ?_
          simpa using hyoung ‖q.1‖ ‖q.2.1‖ (norm_nonneg _) (norm_nonneg _)
      _ = b := by
          rw [integral_add (a1.div_const 3) ((a2.const_mul 2).div_const 3), integral_div,
            integral_div, integral_const_mul, hm1, hm2]
          ring
  have hA2 : ∫ q : EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ),
      ‖q.1‖ ^ 3 * ((1 : ℝ) * |1 - q.2.2|) ∂((S.ν i).prod ρ') = b / 2 := by
    rw [integral_prod_mul (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ 3)
      (fun y : EuclideanSpace ℝ (Fin d) × ℝ => (1 : ℝ) * |1 - y.2|)]
    simp only [one_mul]
    rw [integral_fun_snd (f := fun θ : ℝ => |1 - θ|), mvbe_integral_abs_one_sub]
    simp [hb]
    ring
  rw [hsplit, hA2]
  linarith

end Weight


end S3d

section S3e

section Main

variable {d : ℕ}

theorem mvbe_measurable_tan : Measurable Real.tan := by
  have : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [this]
  exact Real.measurable_sin.div Real.measurable_cos

/-- **Slepian interpolation + Stein expectation + conditioning** (Raic (2.5), Lemma 2.4, (2.24),
(2.25)). -/
theorem mvbe_slepian_stein (hinterp : MvbeMehlerInterp) (S : MvbeSummands d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf1 : ContDiff ℝ 1 f) (hf0 : ∀ x, |f x| ≤ 1)
    {L1 : ℝ} (hfd : ∀ x, ‖fderiv ℝ f x‖ ≤ L1) {L2 : NNReal}
    (hfL : LipschitzWith L2 (fderiv ℝ f)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (i : Fin S.n) (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ), θ ∈ Set.Icc (0 : ℝ) 1 →
      ∫⁻ a in Set.Ioo 0 (Real.pi / 2),
          ENNReal.ofReal (mvbeDiag3 (mehlerI a f) (mvbeCondLaw S i (θ • x)) * Real.tan a)
        ≤ ENNReal.ofReal B) :
    |∫ ω, f (∑ i, ω i) ∂Measure.pi S.ν - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
      ≤ 27 / 4 * B * S.beta := by
  have hfc := hf1.continuous
  have hfm := hfc.measurable
  have hWm : Measurable fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ∑ i, ω i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hWint : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ‖∑ i, ω i‖)
      (Measure.pi S.ν) := by
    have h : ∀ i, Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ‖ω i‖)
        (Measure.pi S.ν) := fun i =>
      mvbe_integrable_eval S.ν i (mvbe_integrable_norm (S.mom i))
    have hsum : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ∑ i, ‖ω i‖)
        (Measure.pi S.ν) := integrable_finsetSum Finset.univ fun i _ => h i
    refine hsum.mono' hWm.norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa using norm_sum_le Finset.univ fun i => ω i
  have hid := hinterp d (Fin S.n → EuclideanSpace ℝ (Fin d)) (Measure.pi S.ν)
    (fun ω => ∑ i, ω i) hWm hWint f hf1 ⟨1, hf0⟩ ⟨L1, hfd⟩ ⟨L2, hfL⟩
  choose Nt hNtm hNt using fun i => mvbe_Ntilde S i hfc hf0
  set Q := EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) × ℝ) with hQ
  set ρ : Fin S.n → Measure Q := fun i =>
    (S.ν i).prod ((S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) with hρ
  set wt : Q → ℝ := fun q => ‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3 with hwt
  have hwt0 : ∀ q, 0 ≤ wt q := fun q => by simp only [hwt]; positivity
  have hwtm : Measurable wt := by simp only [hwt]; fun_prop
  set Hf : Fin S.n → ℝ × Q → ℝ≥0∞ := fun i p =>
    ENNReal.ofReal (Real.tan p.1 * (9 / 2 * Nt i (p.1, (p.2.1, p.2.2.2)) * wt p.2)) with hHf
  have hHm : ∀ i, Measurable (Hf i) := fun i => by
    refine ENNReal.measurable_ofReal.comp ?_
    refine (mvbe_measurable_tan.comp measurable_fst).mul ?_
    refine (measurable_const.mul ((hNtm i).comp ?_)).mul (hwtm.comp measurable_snd)
    exact measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  -- pointwise in `a`
  have hstar : ∀ a ∈ Set.Ioo 0 (Real.pi / 2),
      ENNReal.ofReal |Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (∑ i, ω i) ∂Measure.pi S.ν|
        ≤ ∑ i, ∫⁻ q, Hf i (a, q) ∂ρ i := by
    intro a ha
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hg3, ⟨C₁, hb1⟩, ⟨C₂, hb2⟩, ⟨C₃, hb3⟩⟩ := mvbe_mehlerI_smooth hfm hf0 ha0 ha1
    have hE : ∫ ω, mehlerIS (mehlerI a f) (∑ i, ω i) ∂Measure.pi S.ν
        = ∫ ω, mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) (mehlerI a f) (∑ i, ω i)
          ∂Measure.pi S.ν :=
      integral_congr_ae (ae_of_all _ fun ω =>
        mvbe_mehlerIS_eq_mvbeStein (hg3.of_le (by norm_num)) _)
    have hs := mvbe_stein_bound S hg3 hb1 hb2 hb3
    have htan : 0 ≤ Real.tan a := (Real.tan_pos_of_pos_of_lt_pi_div_two ha0 ha1).le
    rw [hE, abs_mul, abs_of_nonneg htan, ENNReal.ofReal_mul htan]
    calc ENNReal.ofReal (Real.tan a) * ENNReal.ofReal
          |∫ ω, mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) (mehlerI a f) (∑ i, ω i)
            ∂Measure.pi S.ν|
        ≤ ENNReal.ofReal (Real.tan a) * ∑ i, ∫⁻ q : Q,
            ENNReal.ofReal (9 / 2 * mvbeDiag3 (mehlerI a f) (mvbeCondLaw S i (q.2.2 • q.1)) *
              (‖q.1‖ * ‖q.2.1‖ ^ 2 + |1 - q.2.2| * ‖q.1‖ ^ 3)) ∂ρ i := by
          gcongr
      _ = ∑ i, ∫⁻ q, Hf i (a, q) ∂ρ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun q => ?_
          simp only [hHf, hwt]
          rw [← ENNReal.ofReal_mul htan, hNt i a ha0 ha1 q.1 q.2.2]
  -- inner bound for a.e. `q`
  have hinner : ∀ i, ∀ᵐ q ∂ρ i, ∫⁻ a in Set.Ioo 0 (Real.pi / 2), Hf i (a, q)
        ≤ ENNReal.ofReal (9 / 2 * wt q) * ENNReal.ofReal B := by
    intro i
    have hθ : ∀ᵐ q ∂ρ i, q.2.2 ∈ Set.Icc (0 : ℝ) 1 := by
      have hmp : MeasurePreserving (fun q : Q => q.2.2) (ρ i)
          (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (measurePreserving_snd (μ := S.ν i) (ν := volume.restrict (Set.Icc (0 : ℝ) 1))).comp
          (measurePreserving_snd (μ := S.ν i)
            (ν := (S.ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))))
      exact hmp.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hθ] with q hq
    have hw0 : 0 ≤ 9 / 2 * wt q := by have := hwt0 q; positivity
    have h1 : ∫⁻ a in Set.Ioo 0 (Real.pi / 2), Hf i (a, q)
        = ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (9 / 2 * wt q) *
          ENNReal.ofReal (mvbeDiag3 (mehlerI a f) (mvbeCondLaw S i (q.2.2 • q.1)) *
            Real.tan a) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
      simp only [hHf]
      rw [hNt i a ha.1 ha.2 q.1 q.2.2, ← ENNReal.ofReal_mul hw0]
      congr 1
      ring
    rw [h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (hB i q.1 q.2.2 hq) _
  -- the bound for each summand
  have hsum_i : ∀ i, ∫⁻ q, ENNReal.ofReal (9 / 2 * wt q) * ENNReal.ofReal B ∂ρ i
      ≤ ENNReal.ofReal (27 / 4 * B * ∫ x, ‖x‖ ^ 3 ∂S.ν i) := by
    intro i
    have hb0 : 0 ≤ ∫ x, ‖x‖ ^ 3 ∂S.ν i := integral_nonneg fun x => by positivity
    calc ∫⁻ q, ENNReal.ofReal (9 / 2 * wt q) * ENNReal.ofReal B ∂ρ i
        = ∫⁻ q, ENNReal.ofReal (9 / 2 * B) * ENNReal.ofReal (wt q) ∂ρ i := by
          refine lintegral_congr fun q => ?_
          have hw0 : 0 ≤ 9 / 2 * wt q := by have := hwt0 q; positivity
          rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 / 2 * B)]
          congr 1
          ring
      _ = ENNReal.ofReal (9 / 2 * B) * ∫⁻ q, ENNReal.ofReal (wt q) ∂ρ i :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (9 / 2 * B) * ENNReal.ofReal (3 / 2 * ∫ x, ‖x‖ ^ 3 ∂S.ν i) :=
          mul_le_mul_right (mvbe_weight_lintegral_le S i) _
      _ = ENNReal.ofReal (27 / 4 * B * ∫ x, ‖x‖ ^ 3 ∂S.ν i) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hbound : ENNReal.ofReal
      |∫ ω, f (∑ i, ω i) ∂Measure.pi S.ν - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
        ≤ ENNReal.ofReal (27 / 4 * B * S.beta) := by
    rw [hid, abs_neg]
    calc ENNReal.ofReal |∫ a in Set.Ioo 0 (Real.pi / 2),
            Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (∑ i, ω i) ∂Measure.pi S.ν|
        ≤ ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal
            |Real.tan a * ∫ ω, mehlerIS (mehlerI a f) (∑ i, ω i) ∂Measure.pi S.ν| :=
          mvbe_ofReal_abs_integral_le _ _
      _ ≤ ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ∑ i, ∫⁻ q, Hf i (a, q) ∂ρ i :=
          setLIntegral_mono' measurableSet_Ioo hstar
      _ = ∑ i, ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ∫⁻ q, Hf i (a, q) ∂ρ i :=
          lintegral_finsetSum' _ fun i _ => ((hHm i).lintegral_prod_right').aemeasurable
      _ = ∑ i, ∫⁻ q, (∫⁻ a in Set.Ioo 0 (Real.pi / 2), Hf i (a, q)) ∂ρ i :=
          Finset.sum_congr rfl fun i _ => lintegral_lintegral_swap (hHm i).aemeasurable
      _ ≤ ∑ i, ∫⁻ q, ENNReal.ofReal (9 / 2 * wt q) * ENNReal.ofReal B ∂ρ i :=
          Finset.sum_le_sum fun i _ => lintegral_mono_ae (hinner i)
      _ ≤ ∑ i, ENNReal.ofReal (27 / 4 * B * ∫ x, ‖x‖ ^ 3 ∂S.ν i) :=
          Finset.sum_le_sum fun i _ => hsum_i i
      _ = ENNReal.ofReal (27 / 4 * B * S.beta) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun i _ =>
            mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)]
          congr 1
          rw [MvbeSummands.beta, Finset.mul_sum]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => integral_nonneg fun x => by positivity))).1 hbound

end Main


end S3e

section Sandwich

variable {d : ℕ} {κ : ℝ}

theorem mvbe_toReal_le_add_diff {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {s t : Set α} (hst : s ⊆ t) :
    (μ t).toReal ≤ (μ s).toReal + (μ (t \ s)).toReal := by
  have h : μ t ≤ μ s + μ (t \ s) := by
    calc μ t = μ (s ∪ (t \ s)) := by rw [Set.union_sdiff_cancel hst]
      _ ≤ μ s + μ (t \ s) := measure_union_le _ _
  calc (μ t).toReal ≤ (μ s + μ (t \ s)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
    _ = _ := ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

theorem mvbe_indicator_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) {h : α → ℝ}
    (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1) (hle : ∀ x, s.indicator (fun _ => (1 : ℝ)) x ≤ h x) :
    (μ s).toReal ≤ ∫ x, h x ∂μ := by
  have hi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa using hb x)
  have h1 : ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = (μ s).toReal := by
    rw [integral_indicator hs]; simp [Measure.real]
  rw [← h1]
  exact integral_mono ((integrable_const (1 : ℝ)).indicator hs) hi hle

theorem mvbe_integral_le_indicator {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) {h : α → ℝ}
    (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1) (hle : ∀ x, h x ≤ s.indicator (fun _ => (1 : ℝ)) x) :
    ∫ x, h x ∂μ ≤ (μ s).toReal := by
  have hi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa using hb x)
  have h1 : ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = (μ s).toReal := by
    rw [integral_indicator hs]; simp [Measure.real]
  rw [← h1]
  exact integral_mono hi ((integrable_const (1 : ℝ)).indicator hs) hle

/-- **Sandwich** (Raic (2.23)). -/
theorem mvbe_sandwich (C : MvbeRegularClass d κ) (S : MvbeSummands d)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : A ∈ C.cls) {ε : ℝ} (hε : 0 < ε)
    {fp fm : EuclideanSpace ℝ (Fin d) → ℝ}
    (hp : MvbeSmoothFn C ε A (mvbeLayer C.rho A ε) fp)
    (hm : MvbeSmoothFn C ε (mvbeLayer C.rho A (-ε)) A fm) :
    S.dev A ≤ max
        |∫ ω, fp (∑ i, ω i) ∂Measure.pi S.ν
          - ∫ x, fp x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
        |∫ ω, fm (∑ i, ω i) ∂Measure.pi S.ν
          - ∫ x, fm x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
      + (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal * ε := by
  set P := Measure.pi S.ν with hP
  set γ := stdGaussian (EuclideanSpace ℝ (Fin d)) with hγdef
  set G := (C.gammaStar γ).toReal with hG
  have hAm : MeasurableSet A := C.measurableSet_mem A hA
  have hLm : ∀ t : ℝ, MeasurableSet (mvbeLayer C.rho A t) := fun t =>
    measurableSet_le (C.measurable_rho A hA) measurable_const
  have hWm : Measurable fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => ∑ i, ω i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hpm : Measurable fp := hp.contDiff.continuous.measurable
  have hmm : Measurable fm := hm.contDiff.continuous.measurable
  have hpb : ∀ x, |fp x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hp.zero_le x], hp.le_one x⟩
  have hmb : ∀ x, |fm x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [hm.zero_le x], hm.le_one x⟩
  -- sandwiches
  have hpl : ∀ x, A.indicator (fun _ => (1 : ℝ)) x ≤ fp x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hp.eq_one x hx]
    · rw [Set.indicator_of_notMem hx]; exact hp.zero_le x
  have hpu : ∀ x, fp x ≤ (mvbeLayer C.rho A ε).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ mvbeLayer C.rho A ε
    · rw [Set.indicator_of_mem hx]; exact hp.le_one x
    · rw [Set.indicator_of_notMem hx, hp.eq_zero x hx]
  have hml : ∀ x, (mvbeLayer C.rho A (-ε)).indicator (fun _ => (1 : ℝ)) x ≤ fm x := by
    intro x
    by_cases hx : x ∈ mvbeLayer C.rho A (-ε)
    · rw [Set.indicator_of_mem hx, hm.eq_one x hx]
    · rw [Set.indicator_of_notMem hx]; exact hm.zero_le x
  have hmu : ∀ x, fm x ≤ A.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; exact hm.le_one x
    · rw [Set.indicator_of_notMem hx, hm.eq_zero x hx]
  -- A ⊆ A^ε, A^{-ε} ⊆ A
  have hsub1 : A ⊆ mvbeLayer C.rho A ε := fun x hx => by
    have := C.a4_nonpos A hA x hx
    show C.rho A x ≤ ε
    linarith
  have hsub2 : mvbeLayer C.rho A (-ε) ⊆ A := by
    intro x hx
    by_contra hxA
    have h1 := C.a4_nonneg A hA x hxA
    have h2 : C.rho A x ≤ -ε := hx
    linarith
  -- layer estimates
  have hd1 : (γ (mvbeLayer C.rho A ε \ A)).toReal ≤ G * ε := by
    have h := mvbe_layer_diff_le γ C.cls C.rho hA hε
    have hne : ENNReal.ofReal ε * C.gammaStar γ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hγ
    calc _ ≤ (ENNReal.ofReal ε * C.gammaStar γ).toReal := ENNReal.toReal_mono hne h
      _ = G * ε := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]; ring
  have hd2 : (γ (A \ mvbeLayer C.rho A (-ε))).toReal ≤ G * ε := by
    have h := mvbe_diff_layer_le γ C.cls C.rho hA hε
    have hne : ENNReal.ofReal ε * C.gammaStar γ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hγ
    calc _ ≤ (ENNReal.ofReal ε * C.gammaStar γ).toReal := ENNReal.toReal_mono hne h
      _ = G * ε := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]; ring
  -- probabilities
  have hpre : MeasurableSet {ω : Fin S.n → EuclideanSpace ℝ (Fin d) | ∑ i, ω i ∈ A} :=
    hWm hAm
  have hPA : (P {ω | ∑ i, ω i ∈ A}).toReal = ∫ ω, A.indicator (fun _ => (1 : ℝ)) (∑ i, ω i) ∂P := by
    have : (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) =>
        A.indicator (fun _ => (1 : ℝ)) (∑ i, ω i))
        = {ω : Fin S.n → EuclideanSpace ℝ (Fin d) | ∑ i, ω i ∈ A}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ∑ i, ω i ∈ A <;> simp [Set.indicator, h]
    rw [this, integral_indicator hpre]; simp [Measure.real]
  -- the two integrals against P
  have hIp : (P {ω | ∑ i, ω i ∈ A}).toReal ≤ ∫ ω, fp (∑ i, ω i) ∂P := by
    rw [hPA]
    have hi : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => fp (∑ i, ω i)) P :=
      Integrable.of_bound (hpm.comp hWm).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by simpa using hpb _)
    have hi2 : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) =>
        A.indicator (fun _ => (1 : ℝ)) (∑ i, ω i)) P :=
      Integrable.of_bound ((measurable_const.indicator hAm).comp hWm).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by
          by_cases h : ∑ i, ω i ∈ A <;> simp [Set.indicator, h])
    exact integral_mono hi2 hi fun ω => hpl _
  have hIm : ∫ ω, fm (∑ i, ω i) ∂P ≤ (P {ω | ∑ i, ω i ∈ A}).toReal := by
    rw [hPA]
    have hi : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) => fm (∑ i, ω i)) P :=
      Integrable.of_bound (hmm.comp hWm).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by simpa using hmb _)
    have hi2 : Integrable (fun ω : Fin S.n → EuclideanSpace ℝ (Fin d) =>
        A.indicator (fun _ => (1 : ℝ)) (∑ i, ω i)) P :=
      Integrable.of_bound ((measurable_const.indicator hAm).comp hWm).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by
          by_cases h : ∑ i, ω i ∈ A <;> simp [Set.indicator, h])
    exact integral_mono hi hi2 fun ω => hmu _
  -- Gaussian side
  have hgp : ∫ x, fp x ∂γ ≤ (γ (mvbeLayer C.rho A ε)).toReal :=
    mvbe_integral_le_indicator γ (hLm ε) hpm hpb hpu
  have hgm : (γ (mvbeLayer C.rho A (-ε))).toReal ≤ ∫ x, fm x ∂γ :=
    mvbe_indicator_integral_le γ (hLm (-ε)) hmm hmb hml
  have hg1 := mvbe_toReal_le_add_diff γ hsub1
  have hg2 := mvbe_toReal_le_add_diff γ hsub2
  -- assemble
  have hup : (P {ω | ∑ i, ω i ∈ A}).toReal - (γ A).toReal
      ≤ (∫ ω, fp (∑ i, ω i) ∂P - ∫ x, fp x ∂γ) + G * ε := by linarith
  have hlow : (∫ ω, fm (∑ i, ω i) ∂P - ∫ x, fm x ∂γ) - G * ε
      ≤ (P {ω | ∑ i, ω i ∈ A}).toReal - (γ A).toReal := by linarith
  unfold MvbeSummands.dev
  rw [abs_le]
  constructor
  · have := neg_abs_le (∫ ω, fm (∑ i, ω i) ∂P - ∫ x, fm x ∂γ)
    have := le_max_right |∫ ω, fp (∑ i, ω i) ∂P - ∫ x, fp x ∂γ|
      |∫ ω, fm (∑ i, ω i) ∂P - ∫ x, fm x ∂γ|
    linarith
  · have := le_abs_self (∫ ω, fp (∑ i, ω i) ∂P - ∫ x, fp x ∂γ)
    have := le_max_left |∫ ω, fp (∑ i, ω i) ∂P - ∫ x, fp x ∂γ|
      |∫ ω, fm (∑ i, ω i) ∂P - ∫ x, fm x ∂γ|
    linarith

end Sandwich


theorem mvbe_algebra {ca cb q K β βb γs γb γ0 : ℝ} (hca : 0 < ca) (hcb : 0 < cb) (hq : 1 ≤ q)
    (hK : 0 ≤ K) (hββ : β ≤ βb) (hβb : 0 < βb) (hγs : 0 ≤ γs) (hγsb : γs ≤ γb)
    (hγ0 : 0 < γ0) (hγ0b : γ0 ≤ γb) :
    27 / 4 * (ca / (1 / 2 : ℝ) ^ 3 + cb * q * (γs / (1 / 2 : ℝ)
        + 4 * (16 * K * (βb * γb)) / (864 * cb * q * βb))) * β + γs * (864 * cb * q * βb)
      ≤ (K / 2 + 54 * ca / γ0 + 878 * cb * q) * (βb * γb) := by
  have hq0 : 0 < q := by linarith
  have hγb : 0 < γb := lt_of_lt_of_le hγ0 hγ0b
  have e1 : cb * q * (4 * (16 * K * (βb * γb)) / (864 * cb * q * βb)) = 2 * K * γb / 27 := by
    field_simp
    ring
  have e2 : ca / (1 / 2 : ℝ) ^ 3 + cb * q * (γs / (1 / 2 : ℝ)
        + 4 * (16 * K * (βb * γb)) / (864 * cb * q * βb))
      = 8 * ca + 2 * cb * q * γs + 2 * K * γb / 27 := by
    calc _ = ca / (1 / 2 : ℝ) ^ 3 + cb * q * (γs / (1 / 2 : ℝ))
          + cb * q * (4 * (16 * K * (βb * γb)) / (864 * cb * q * βb)) := by ring
      _ = _ := by rw [e1]; ring
  rw [e2]
  have hB : 0 ≤ 8 * ca + 2 * cb * q * γs + 2 * K * γb / 27 := by positivity
  have h1 : 27 / 4 * (8 * ca + 2 * cb * q * γs + 2 * K * γb / 27) * β
      ≤ 27 / 4 * (8 * ca + 2 * cb * q * γs + 2 * K * γb / 27) * βb :=
    mul_le_mul_of_nonneg_left hββ (by positivity)
  have h2 : 54 * ca * βb ≤ 54 * ca / γ0 * (βb * γb) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hγ0]
    nlinarith [mul_pos hca hβb]
  have h3 : 878 * cb * q * γs * βb ≤ 878 * cb * q * (βb * γb) := by
    have := mul_le_mul_of_nonneg_left hγsb (by positivity : (0:ℝ) ≤ 878 * cb * q * βb)
    nlinarith
  have h4 : 0 ≤ cb * q * γs * βb := by positivity
  nlinarith [h1, h2, h3, h4]


section MainStep

/-- **The key inequality step** (Raic (2.26)-(2.27) with the choice of `ε`). -/
theorem mvbe_main_step {ca cb : ℝ} (hca : 0 < ca) (hcb : 0 < cb) (hkey : MvbeKeyLemmaWith ca cb)
    (hinterp : MvbeMehlerInterp) {d : ℕ} [NeZero d] {κ β0 γ0 K : ℝ} (hβ0 : 0 < β0)
    (hγ0 : 0 < γ0) (hK0 : 0 ≤ K) (hK : ∀ r ∈ mvbeKSet d κ β0 γ0, r ≤ K) (S : MvbeSummands d)
    (C : MvbeRegularClass d κ) (hC : MvbeNegOpen C)
    (hγ : C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d))) ≠ ⊤)
    {A : Set (EuclideanSpace ℝ (Fin d))} (hA : A ∈ C.cls) (hβ : max S.beta β0 < 1 / 8) :
    S.dev A ≤ (K / 2 + 54 * ca / γ0 + 878 * cb * √(1 + κ)) *
      (max S.beta β0 * max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0) := by
  set βb := max S.beta β0 with hβb_def
  set γs := (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal with hγs_def
  set γb := max γs γ0 with hγb_def
  set q := √(1 + κ) with hq_def
  have hκ := C.kappa_nonneg
  have hq1 : 1 ≤ q := by
    rw [hq_def]
    exact Real.one_le_sqrt.2 (by linarith)
  have hβbpos : 0 < βb := lt_of_lt_of_le hβ0 (le_max_right _ _)
  have hγs0 : 0 ≤ γs := ENNReal.toReal_nonneg
  have hγ0b : γ0 ≤ γb := le_max_right _ _
  have hγsb : γs ≤ γb := le_max_left _ _
  have hγbpos : 0 < γb := lt_of_lt_of_le hγ0 hγ0b
  have hSβ : S.beta ≤ βb := le_max_left _ _
  set ε := 864 * cb * q * βb with hε_def
  have hε : 0 < ε := by positivity
  obtain ⟨hfp, hfm⟩ := mvbe_smoothingFacts d κ C hC A hA ε hε
  set D := 16 * K * (βb * γb) with hD_def
  have hD0 : 0 ≤ D := by positivity
  set B := ca / (1 / 2 : ℝ) ^ 3 + cb * q * (γs / (1 / 2 : ℝ) + 4 * D / ε) with hB_def
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ (A1 A2 : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ),
      MvbeSmoothFn C ε A1 A2 f → (f = C.smoothOuter A ε ∨ f = C.smoothInner A ε) →
      |∫ ω, f (∑ i, ω i) ∂Measure.pi S.ν
          - ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤ 27 / 4 * B * S.beta := by
    intro A1 A2 f hf hfeq
    refine mvbe_slepian_stein hinterp S hf.contDiff
      (fun x => abs_le.2 ⟨by linarith [hf.zero_le x], hf.le_one x⟩) hf.norm_fderiv_le
      hf.lipschitz_fderiv hB0 ?_
    intro i x θ _
    have hsm : ∫ y, ‖y‖ ^ 2 ∂S.ν i ≤ 1 / 4 := mvbe_sq_moment_le S i (lt_of_le_of_lt hSβ hβ)
    exact hkey d κ C hC hγ (mvbeCondLaw S i (θ • x)) inferInstance (θ • x) (mvbeSigma S i)
      (1 / 2) D ε (by norm_num) (by norm_num) (mvbeSigma_posSemidef S i hsm) hD0 hε
      (fun A' hA' => mvbe_cond_dev C hC hγ S i hsm hβ0 hγ0 hK0 hK (θ • x) hA') A hA f hfeq
  have hsand := mvbe_sandwich C S hγ hA hε hfp hfm
  have h1 := key _ _ _ hfp (Or.inl rfl)
  have h2 := key _ _ _ hfm (Or.inr rfl)
  have hmax := max_le h1 h2
  have hfin := mvbe_algebra hca hcb hq1 hK0 hSβ hβbpos hγs0 hγsb hγ0 hγ0b
  calc S.dev A ≤ _ := hsand
    _ ≤ 27 / 4 * B * S.beta + γs * ε := by linarith
    _ ≤ _ := hfin

end MainStep

section KFacts

variable {d : ℕ} {κ : ℝ}

theorem mvbe_dev_nonneg (S : MvbeSummands d) (A : Set (EuclideanSpace ℝ (Fin d))) :
    0 ≤ S.dev A := abs_nonneg _

theorem mvbe_toReal_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (s : Set α) : (μ s).toReal ≤ 1 := by
  have h : μ s ≤ 1 := prob_le_one
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 h

theorem mvbe_dev_le_one (S : MvbeSummands d) (A : Set (EuclideanSpace ℝ (Fin d))) :
    S.dev A ≤ 1 := by
  unfold MvbeSummands.dev
  have h1 := mvbe_toReal_le_one (Measure.pi S.ν) {ω | ∑ i, ω i ∈ A}
  have h2 := mvbe_toReal_le_one (stdGaussian (EuclideanSpace ℝ (Fin d))) A
  have h3 := ENNReal.toReal_nonneg (a := (Measure.pi S.ν) {ω | ∑ i, ω i ∈ A})
  have h4 := ENNReal.toReal_nonneg (a := stdGaussian (EuclideanSpace ℝ (Fin d)) A)
  rw [abs_le]
  constructor <;> linarith

theorem mvbe_beta_nonneg (S : MvbeSummands d) : 0 ≤ S.beta :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun x => by positivity

theorem mvbeKSet_le {β0 γ0 r : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0)
    (hr : r ∈ mvbeKSet d κ β0 γ0) : 0 ≤ r ∧ r ≤ 1 / (β0 * γ0) := by
  obtain ⟨S, C, -, -, A, -, rfl⟩ := hr
  have hden : 0 < max S.beta β0 *
      max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0 :=
    mul_pos (lt_max_of_lt_right hβ0) (lt_max_of_lt_right hγ0)
  refine ⟨div_nonneg (mvbe_dev_nonneg S A) hden.le, ?_⟩
  rw [div_le_div_iff₀ hden (mul_pos hβ0 hγ0)]
  have h1 : β0 * γ0 ≤ max S.beta β0 *
      max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0 :=
    mul_le_mul (le_max_right _ _) (le_max_right _ _) hγ0.le (le_trans hβ0.le (le_max_right _ _))
  have h2 := mvbe_dev_le_one S A
  nlinarith [mvbe_dev_nonneg S A]

theorem mvbeKSet_bddAbove {β0 γ0 : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) :
    BddAbove (mvbeKSet d κ β0 γ0) :=
  ⟨1 / (β0 * γ0), fun _ hr => (mvbeKSet_le hβ0 hγ0 hr).2⟩

theorem mvbeK_nonneg {β0 γ0 : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) : 0 ≤ mvbeK d κ β0 γ0 :=
  Real.sSup_nonneg fun _ hr => (mvbeKSet_le hβ0 hγ0 hr).1

/-- `K(β₀, γ₀) ≤ 1/(β₀ γ₀) < ∞`. -/
theorem mvbeK_le_inv {β0 γ0 : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) :
    mvbeK d κ β0 γ0 ≤ 1 / (β0 * γ0) :=
  Real.sSup_le (fun _ hr => (mvbeKSet_le hβ0 hγ0 hr).2) (by positivity)

theorem le_mvbeK {β0 γ0 r : ℝ} (hβ0 : 0 < β0) (hγ0 : 0 < γ0) (hr : r ∈ mvbeKSet d κ β0 γ0) :
    r ≤ mvbeK d κ β0 γ0 := le_csSup (mvbeKSet_bddAbove hβ0 hγ0) hr

end KFacts

section KeyIneq

/-- **The key inequality** `K ≤ max(8/γ₀, K/2 + c)` (Raic (2.28)-(2.33)). -/
theorem mvbe_key_ineq {ca cb : ℝ} (hca : 0 < ca) (hcb : 0 < cb) (hkey : MvbeKeyLemmaWith ca cb)
    (hinterp : MvbeMehlerInterp) {d : ℕ} [NeZero d] {κ β0 γ0 : ℝ} (hβ0 : 0 < β0)
    (hγ0 : 0 < γ0) :
    mvbeK d κ β0 γ0 ≤ max (8 / γ0)
      (mvbeK d κ β0 γ0 / 2 + 54 * ca / γ0 + 878 * cb * √(1 + κ)) := by
  have hK0 := mvbeK_nonneg (d := d) (κ := κ) hβ0 hγ0
  have hRHS : 0 ≤ max (8 / γ0) (mvbeK d κ β0 γ0 / 2 + 54 * ca / γ0 + 878 * cb * √(1 + κ)) :=
    le_trans (by positivity) (le_max_left _ _)
  refine Real.sSup_le ?_ hRHS
  rintro r ⟨S, C, hC, hγ, A, hA, rfl⟩
  set βb := max S.beta β0 with hβb
  set γb := max (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal γ0 with hγb
  have hβbpos : 0 < βb := lt_of_lt_of_le hβ0 (le_max_right _ _)
  have hγbpos : 0 < γb := lt_of_lt_of_le hγ0 (le_max_right _ _)
  have hden : 0 < βb * γb := mul_pos hβbpos hγbpos
  rw [div_le_iff₀ hden]
  rcases le_or_gt (1 / 8) βb with hb | hb
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) hden.le)
    have h1 := mvbe_dev_le_one S A
    have h2 : (1 : ℝ) ≤ 8 / γ0 * (βb * γb) := by
      have hγ0b : γ0 ≤ γb := le_max_right _ _
      have : 8 * βb ≤ 8 / γ0 * (βb * γb) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hγ0]
        nlinarith [mul_pos hβbpos hγ0]
      linarith
    linarith
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le)
    exact mvbe_main_step hca hcb hkey hinterp hβ0 hγ0 hK0
      (fun r hr => le_mvbeK hβ0 hγ0 hr) S C hC hγ hA hb

/-- **The bootstrapped bound** (Raic (2.33)): `K(β₀, γ₀) ≤ max(8/γ₀, 108 ca/γ₀ + 1756 cb √(1+κ))`.
-/
theorem mvbeK_le_bound {ca cb : ℝ} (hca : 0 < ca) (hcb : 0 < cb) (hkey : MvbeKeyLemmaWith ca cb)
    (hinterp : MvbeMehlerInterp) {d : ℕ} [NeZero d] {κ β0 γ0 : ℝ} (hβ0 : 0 < β0)
    (hγ0 : 0 < γ0) :
    mvbeK d κ β0 γ0 ≤ max (8 / γ0) (108 * ca / γ0 + 1756 * cb * √(1 + κ)) := by
  have h := mvbe_key_ineq hca hcb hkey hinterp (d := d) (κ := κ) hβ0 hγ0
  rcases le_max_iff.1 h with h1 | h1
  · exact le_trans h1 (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have : 108 * ca / γ0 = 2 * (54 * ca / γ0) := by ring
    rw [this]
    linarith

end KeyIneq

section Final

theorem mvbe_limit_bound {dev β γs q a2 a3 : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (ha3 : 0 ≤ a3)
    (h : ∀ β0 t : ℝ, 0 < β0 → γs < t → dev ≤ max 8 (a2 + a3 * q * t) * (β + β0)) :
    dev ≤ max 8 (a2 + a3 * q * γs) * β := by
  -- first let `β0 → 0`
  have h1 : ∀ t : ℝ, γs < t → dev ≤ max 8 (a2 + a3 * q * t) * β := by
    intro t ht
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hM : 0 < max 8 (a2 + a3 * q * t) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have := h (ε / max 8 (a2 + a3 * q * t)) t (by positivity) ht
    calc dev ≤ max 8 (a2 + a3 * q * t) * (β + ε / max 8 (a2 + a3 * q * t)) := this
      _ = max 8 (a2 + a3 * q * t) * β + ε := by field_simp
  -- then let `t ↓ γs`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set M := max 8 (a2 + a3 * q * γs) with hM
  set δ := ε / (a3 * q * β + 1) with hδ
  have hc : 0 < a3 * q * β + 1 := by positivity
  have hδpos : 0 < δ := by positivity
  have hmax : max 8 (a2 + a3 * q * (γs + δ)) ≤ M + a3 * q * δ := by
    refine max_le ?_ ?_
    · have : 0 ≤ a3 * q * δ := by positivity
      linarith [le_max_left 8 (a2 + a3 * q * γs)]
    · have : a2 + a3 * q * (γs + δ) = (a2 + a3 * q * γs) + a3 * q * δ := by ring
      rw [this]
      linarith [le_max_right 8 (a2 + a3 * q * γs)]
  have h2 := h1 (γs + δ) (by linarith)
  calc dev ≤ max 8 (a2 + a3 * q * (γs + δ)) * β := h2
    _ ≤ (M + a3 * q * δ) * β := mul_le_mul_of_nonneg_right hmax hβ
    _ = M * β + a3 * q * β * δ := by ring
    _ ≤ M * β + ε := by
        have : a3 * q * β * δ ≤ ε := by
          rw [hδ, ← mul_div_assoc, div_le_iff₀ hc]
          nlinarith [mul_nonneg (mul_nonneg ha3 hq) hβ, hε]
        linarith

theorem mvbe_max_le_form {a2 a3 X : ℝ} (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hX : 0 ≤ X) :
    max 8 (a2 + a3 * X) ≤ max (8 + a2 + a3) (1 + (8 + a2 + a3) * X) := by
  rcases le_total X 1 with h | h
  · refine le_trans ?_ (le_max_left _ _)
    refine max_le (by linarith) ?_
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith

/-- **Raic's Theorem 1.3, form (1.4)**, from the key estimate (Lemma 2.7) and the interpolation
identity for `C^{1,1}` functions.  Everything else (Lemma 2.1, Lemma 2.3, the Stein expectation,
Mehler smoothness) is proved. -/
theorem mvbe_thmR_of_keyLemma_interp (hkey : MvbeKeyLemma) (hinterp : MvbeMehlerInterp) :
    MvbeThmR := by
  obtain ⟨ca, cb, hca, hcb, hk⟩ := hkey
  refine ⟨8 + 108 * ca + 1756 * cb, 8 + 108 * ca + 1756 * cb, by positivity, by positivity, ?_⟩
  intro d _ κ C hC hγ n ν _ hmom hmean hcov A hA
  let S : MvbeSummands d := ⟨n, ν, inferInstance, hmom, hmean, hcov⟩
  show S.dev A ≤ max _ (1 + _ * (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal
    * √(1 + κ)) * S.beta
  set γs := (C.gammaStar (stdGaussian (EuclideanSpace ℝ (Fin d)))).toReal
  have hγs0 : 0 ≤ γs := ENNReal.toReal_nonneg
  have hκ := C.kappa_nonneg
  have hq0 : 0 ≤ √(1 + κ) := Real.sqrt_nonneg _
  have hβ0 := mvbe_beta_nonneg S
  have hbound : ∀ β0 t : ℝ, 0 < β0 → γs < t →
      S.dev A ≤ max 8 (108 * ca + 1756 * cb * √(1 + κ) * t) * (S.beta + β0) := by
    intro β0 t hβ0' hlt
    have ht : 0 < t := lt_of_le_of_lt hγs0 hlt
    have hmem : S.dev A / (max S.beta β0 * max γs t) ∈ mvbeKSet d κ β0 t :=
      ⟨S, C, hC, hγ, A, hA, rfl⟩
    have hle := (le_mvbeK hβ0' ht hmem).trans (mvbeK_le_bound hca hcb hk hinterp hβ0' ht)
    have hden : 0 < max S.beta β0 * max γs t :=
      mul_pos (lt_of_lt_of_le hβ0' (le_max_right _ _)) (lt_of_lt_of_le ht (le_max_right _ _))
    rw [div_le_iff₀ hden, max_eq_right hlt.le] at hle
    have e : max (8 / t) (108 * ca / t + 1756 * cb * √(1 + κ)) * t
        = max 8 (108 * ca + 1756 * cb * √(1 + κ) * t) := by
      rw [max_mul_of_nonneg _ _ ht.le]
      congr 1
      · field_simp
      · field_simp
    have hmb : max S.beta β0 ≤ S.beta + β0 := max_le (by linarith) (by linarith)
    calc S.dev A ≤ max (8 / t) (108 * ca / t + 1756 * cb * √(1 + κ)) *
          (max S.beta β0 * t) := hle
      _ = max 8 (108 * ca + 1756 * cb * √(1 + κ) * t) * max S.beta β0 := by
          rw [← e]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmb (le_trans (by norm_num) (le_max_left _ _))
  have hlim := mvbe_limit_bound (a2 := 108 * ca) (a3 := 1756 * cb) hβ0 hq0
    (by positivity) (fun β0 t hβ0' hlt => by simpa [mul_assoc] using hbound β0 t hβ0' hlt)
  refine le_trans hlim (mul_le_mul_of_nonneg_right ?_ hβ0)
  have hX : 0 ≤ γs * √(1 + κ) := mul_nonneg hγs0 hq0
  have := mvbe_max_le_form (a2 := 108 * ca) (a3 := 1756 * cb) (X := γs * √(1 + κ))
    (by positivity) (by positivity) hX
  calc max 8 (108 * ca + 1756 * cb * √(1 + κ) * γs)
      = max 8 (108 * ca + 1756 * cb * (γs * √(1 + κ))) := by ring_nf
    _ ≤ max (8 + 108 * ca + 1756 * cb) (1 + (8 + 108 * ca + 1756 * cb) * (γs * √(1 + κ))) := this
    _ = _ := by ring_nf


/-- **Raic's Theorem 1.3, form (1.4), from the key estimate (Lemma 2.7) alone.**  Lemma 2.1, the
image-class Lemma 2.3, the Stein expectation (Lemma 2.4), the Mehler calculus and the Slepian
interpolation are all proved in this development. -/
theorem mvbe_thmR_of_keyLemma (hkey : MvbeKeyLemma) : MvbeThmR :=
  mvbe_thmR_of_keyLemma_interp hkey mvbe_mehlerInterp

/-- The brief's form of the conditional theorem: the three interface propositions imply
Theorem R.  Only `MvbeKeyLemma` is not proved in this development; the other two are the theorems
`mvbe_imageClassFacts` and `mvbe_mehlerFacts`. -/
theorem mvbe_thmR_of_facts (hkey : MvbeKeyLemma) (_himg : MvbeImageClassFacts)
    (_hmeh : MvbeMehlerFacts) : MvbeThmR :=
  mvbe_thmR_of_keyLemma hkey

end Final



section KeyDischarge

/-- **Lemma 2.7 is proved**, in the form consumed by the bootstrapping, from
`mvbe_keyLemma_proved` (packets P5, P15-P18, P8a, P9, P10): the measurable majorant `b` of
`|E⟨∇³U_α f(W), u⊗3⟩|` bounds the diagonal supremum `mvbeDiag3`, and `∫ b tan` is the bound of
(2.11) with `c₃ = mvbeHermiteConst 3`, `c₁ = mvbeHermiteConst 1`. -/
theorem mvbe_keyLemmaWith :
    MvbeKeyLemmaWith (mvbeHermiteConst 3 / 6)
      (Real.sqrt (2 * mvbeHermiteConst 1 * mvbeHermiteConst 3)) := by
  intro d κ C hneg hγ μW hprob m S σ D ε hσ hσ1 hS hD0 hε hdev A hA f hf
  have hSpsd : S.PosSemidef := by
    have h1 : (σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (sq_nonneg σ)
    simpa using hS.add h1
  have hS' := mvbe_le_sqrt_of_posSemidef_sub_sq hSpsd hS
  have hD' : ∀ B ∈ C.cls ∪ {∅, Set.univ},
      |(μW (id ⁻¹' B)).toReal - (multivariateGaussian m S B).toReal| ≤ D := by
    intro B hB
    rcases hB with hB | hB
    · simpa using hdev B hB
    · rcases hB with hB | hB
      · subst hB
        simpa using hD0
      · rw [Set.mem_singleton_iff] at hB
        subst hB
        simpa using hD0
  obtain ⟨b, hbm, hb0, hbH, hbint, hbbound⟩ :=
    mvbe_keyLemma_proved C hneg hγ hA hε hf μW measurable_id m S hσ hσ1 hS' hD'
  haveI : Nonempty {u : EuclideanSpace ℝ (Fin d) // ‖u‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  have hmono : ∀ a ∈ Set.Ioo 0 (Real.pi / 2), mvbeDiag3 (mehlerI a f) μW ≤ b a := by
    intro a ha
    refine ciSup_le fun u => ?_
    have h := hbH a ha u.1 u.2
    have e : (![u.1, u.1, u.1] : Fin 3 → EuclideanSpace ℝ (Fin d)) = fun _ => u.1 :=
      mvbe_w2_vec3 u.1
    simp only [mvbeH] at h
    rw [e]
    exact h
  have hnn : ∀ a ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ Real.tan a := fun a ha =>
    (Real.tan_pos_of_pos_of_lt_pi_div_two ha.1 ha.2).le
  have hint : IntegrableOn (fun a => b a * Real.tan a) (Set.Ioo 0 (Real.pi / 2)) :=
    (hbint.1).mono_set Set.Ioo_subset_Ioc_self
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 (Real.pi / 2))] fun a => b a * Real.tan a :=
    (ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ fun a ha => mul_nonneg (hb0 a ha) (hnn a ha))
  have hc1 := mvbeHermiteConst_one_pos
  have hc3 := mvbeHermiteConst_three_pos
  have hsq : Real.sqrt (2 * (1 + κ) * mvbeHermiteConst 1 * mvbeHermiteConst 3)
      = Real.sqrt (2 * mvbeHermiteConst 1 * mvbeHermiteConst 3) * √(1 + κ) := by
    have : 2 * (1 + κ) * mvbeHermiteConst 1 * mvbeHermiteConst 3
        = (2 * mvbeHermiteConst 1 * mvbeHermiteConst 3) * (1 + κ) := by ring
    rw [this, Real.sqrt_mul (by positivity)]
  calc ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (mvbeDiag3 (mehlerI a f) μW * Real.tan a)
      ≤ ∫⁻ a in Set.Ioo 0 (Real.pi / 2), ENNReal.ofReal (b a * Real.tan a) :=
        setLIntegral_mono' measurableSet_Ioo fun a ha =>
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hmono a ha) (hnn a ha))
    _ = ENNReal.ofReal (∫ a in Set.Ioo 0 (Real.pi / 2), b a * Real.tan a) :=
        (ofReal_integral_eq_lintegral_ofReal hint hae).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity)]
        refine hbbound.trans (le_of_eq ?_)
        rw [hsq]
        ring

/-- **The key estimate, existentially quantified**: this discharges `MvbeKeyLemma`. -/
theorem mvbe_keyLemma_exists : MvbeKeyLemma := by
  have hc1 := mvbeHermiteConst_one_pos
  have hc3 := mvbeHermiteConst_three_pos
  exact ⟨mvbeHermiteConst 3 / 6, Real.sqrt (2 * mvbeHermiteConst 1 * mvbeHermiteConst 3),
    by positivity, Real.sqrt_pos.2 (by positivity), mvbe_keyLemmaWith⟩

/-- **Raic's Theorem 1.3, form (1.4), unconditionally** (existential absolute constants, all
regular classes with `{ρ_A < 0}` open). -/
theorem mvbe_thmR : MvbeThmR := mvbe_thmR_of_keyLemma mvbe_keyLemma_exists

end KeyDischarge

end LatticeProb
