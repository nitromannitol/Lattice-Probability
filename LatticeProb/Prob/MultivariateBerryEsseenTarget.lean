/-
# Multivariate Berry--Esseen: the frozen vocabulary

The frozen external `Sandpile.External.MultivariateBerryEsseen`
(`Divisible-Sandpile-Percolation/Sandpile/External/BerryEsseen.lean`, sha256 `f59d1224…`) is
Raič's multivariate Berry--Esseen theorem (*Bernoulli* 25, 2019, Theorem 1.1).  Its statement is
phrased through three pieces of vocabulary: the covariance matrix `gram` of the linear forms
`Y_j = ∑_i a_i(j) ξ_i`, the Euclidean norms `coeffNorm a i = |a(i)|` of the coefficient vectors,
and the quadratic form `quadForm`.  The library may not import the DSP, so this file fixes the
same vocabulary under `LatticeProb` names.

* `LatticeProb.mvbeGram`, `LatticeProb.mvbeCoeffNorm`, `LatticeProb.mvbeQuadForm` — the three
  definitions, term-for-term the frozen ones.
* `LatticeProb.mvbeQuadForm_eq` — the quadratic form really is `vᵀ S v`, i.e.
  `v ⬝ᵥ (S *ᵥ v)`.
* `LatticeProb.mvbeQuadForm_mvbeGram` — the quadratic form of `Σ` is `Var(ν)` times the sum of
  the squares of the linear forms, the identity in which the frozen statement's spectral bound
  is transcribed.

## The gap

With the vocabulary fixed, the only missing declaration between the library and the frozen
external is **route C1** of `scratch/pk/mvbe-route.md`:

> **Raič's multivariate orthant smoothing inequality with the `m^{1/4}` factor**, comparing
> `μ(orthant h)` and `μ'(orthant h)` for two probability measures on `ℝ^m` with near-isotropic
> covariance, at the level of their characteristic functions.

Every one-dimensional input is landed (`charFun_third_order_le`, `charFun_norm_le_exp_of_sq_le`,
`charFun_sub_exp_le`, the general-kernel deconvolution `sup_cdf_sub_le_of_smoothed`, the
general-target smoothing `esseen_smoothing`, and the law-based and random-variable forms
`berryEsseen_oneDim`/`berryEsseen_oneDim_indep`).  C1 has no reference formalization and no Mathlib
infrastructure: the orthant kernel is not the one-dimensional `∏ sin(t_j)/t_j` (an orthant is
not an integrable difference of boxes in dimension `> 1`), so it must be a Gaussian-smoothed orthant
indicator with a tail controlled by the orthant estimate in `LatticeProb/Prob/GaussOrthant.lean`, or
else one needs a disintegration of `Measure.pi ν` (absent from Mathlib).  Its consumer D1 — the
assembly `multivariateBerryEsseen` — is bookkeeping once C1 exists.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace LatticeProb

/-- The covariance matrix `Σ` of the linear forms `Y_j = ∑_i a_i(j) ξ_i` when the coordinates
`ξ_i` are i.i.d. with one-site law `ν`: `Σ_{jk} = Var(ν) ∑_i a_i(j) a_i(k)`. -/
noncomputable def mvbeGram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- `|a(i)|`, the Euclidean norm of the coefficient vector of the `i`-th coordinate. -/
noncomputable def mvbeCoeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix, in which the paper's spectral bound on `Σ`
is transcribed. -/
noncomputable def mvbeQuadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

/-- **The quadratic form is `vᵀ S v`.**  `mvbeQuadForm S v = v ⬝ᵥ (S *ᵥ v)`. -/
theorem mvbeQuadForm_eq {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    mvbeQuadForm S v = v ⬝ᵥ (S *ᵥ v) := by
  simp only [mvbeQuadForm, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ∑ k, S j k * v j * v k = v j * ∑ k, S j k * v k
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The quadratic form of `mvbeGram`.**  For the linear forms `Y_j = ∑_i a_i(j) ξ_i` the
quadratic form of the covariance matrix `Σ = mvbeGram ν a` is `Var(ν)` times the sum of the
squares of the linear forms:
`mvbeQuadForm (mvbeGram ν a) v = Var(ν) ∑_i (∑_j a_i(j) v_j)²`.
This is the identity in which the paper's spectral bound — the hypothesis
`1 - δ ≤ ⟨Σv, v⟩ ≤ 1 + δ` of the frozen statement — is transcribed. -/
theorem mvbeQuadForm_mvbeGram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ)
    (v : Fin m → ℝ) :
    mvbeQuadForm (mvbeGram ν a) v = variance id ν * ∑ i, (∑ j, a i j * v j) ^ 2 := by
  set A : Matrix (Fin m) (Fin N) ℝ := Matrix.of fun j i => a i j with hA
  have hgram : mvbeGram ν a = variance id ν • (A * Aᵀ) := by
    rw [hA]
    ext j k
    simp [mvbeGram, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hgram, mvbeQuadForm_eq, smul_mulVec]
  have hdot : ∀ (c : ℝ) (w : Fin m → ℝ), v ⬝ᵥ (c • w) = c * (v ⬝ᵥ w) := by
    intro c w
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hdot]
  congr 1
  rw [← Matrix.mulVec_mulVec v A Aᵀ, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose A v]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hwi : (Aᵀ *ᵥ v) i = ∑ j, a i j * v j := by
    rw [hA]
    simp [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
  rw [hwi]
  ring

end LatticeProb
