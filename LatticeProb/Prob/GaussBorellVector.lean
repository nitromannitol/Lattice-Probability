/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/ConcentrationVector.lean.
-/
import LatticeProb.Prob.GaussBorellFinite

/-!
# Borell–TIS inequality for the maximum of a centred Gaussian vector

A centred Gaussian vector `X : Ω → (Fin n → ℝ)` has the law of the Gram image `(⟪vᵢ, Z⟫)ᵢ` of a
standard Gaussian vector `Z` of `EuclideanSpace ℝ (Fin n)`, with `‖vᵢ‖ ^ 2 = Var[Xᵢ]`
(`LatticeProb.GaussConc.exists_gramVec_of_centered`, obtained from the Gram representation
`LatticeProb.Pitt.exists_gram_map_eq`). In this form the file proves:

* `GaussConc.exists_gramVec_of_centered`: the Gram representation of a centred Gaussian vector;
* `GaussConc.norm_le_of_sq_eq_iSup`: every Gram row has norm at most `σ` when `σ ^ 2` is the
  largest variance of the coordinates;
* `GaussConc.measureReal_preimage_eq`: the probability that `X` lies in a measurable set equals the
  standard Gaussian probability that the Gram image lies in it;
* `GaussConc.borellTIS_gaussianVector`: the Borell–TIS upper tail bound
  `P(maxᵢ Xᵢ - E maxᵢ Xᵢ ≥ u) ≤ exp (-u² / (2σ²))` for a centred Gaussian vector.

The last bound follows from `GaussConc.borellTIS_finiteMax` for the standard Gaussian measure.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped RealInnerProductSpace NNReal

namespace LatticeProb.GaussConc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}

/-- A centred Gaussian vector is, in law, the Gram image `(⟪vᵢ, Z⟫)ᵢ` of a standard Gaussian
vector `Z` of `EuclideanSpace ℝ (Fin n)`, for vectors `vᵢ` with `‖vᵢ‖ ^ 2 = Var[Xᵢ]`. -/
theorem exists_gramVec_of_centered (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      (∀ i, ‖v i‖ ^ 2 = Var[fun ω => X ω i; P]) ∧
      P.map X = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (gramVec v) := by
  obtain ⟨v, hv, hmap⟩ := LatticeProb.Pitt.exists_gram_map_eq hX
  refine ⟨v, fun i => ?_, ?_⟩
  · rw [← real_inner_self_eq_norm_sq, hv, covariance_self]
    exact (measurable_pi_apply i).comp_aemeasurable hX.aemeasurable
  · rw [hmap]
    congr 1
    funext x
    ext i
    simp [gramVec, h0]

/-- Each row of a Gram representation has norm at most `σ`, when `σ ^ 2` is the largest variance
`⨆ i, Var[Xᵢ]` of the coordinates and `σ ≥ 0`. -/
lemma norm_le_of_sq_eq_iSup {v : Fin n → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ i, ‖v i‖ ^ 2 = Var[fun ω => X ω i; P]) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ2 : σ ^ 2 = ⨆ i, Var[fun ω => X ω i; P]) (i : Fin n) : ‖v i‖ ≤ σ := by
  have h : ‖v i‖ ^ 2 ≤ σ ^ 2 := by
    rw [hv, hσ2]; exact le_ciSup (f := fun i => Var[fun ω => X ω i; P]) (Finite.bddAbove_range _) i
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h

/-- Transfer of probabilities of measurable events along the Gram representation: the probability
that `X` lies in a measurable set `S` is the standard Gaussian probability that the Gram image
lies in `S`. -/
lemma measureReal_preimage_eq {v : Fin n → EuclideanSpace ℝ (Fin n)} (hX : HasGaussianLaw X P)
    (hmap : P.map X = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (gramVec v))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    P.real (X ⁻¹' S) = (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gramVec v ⁻¹' S) := by
  have hg : Measurable (gramVec v) :=
    (continuous_pi fun i => continuous_const.inner continuous_id).measurable
  rw [measureReal_def, measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable hS,
    hmap, Measure.map_apply hg hS]

/-- **Borell–TIS inequality for a centred Gaussian vector.** Let `X : Ω → (Fin n → ℝ)` be a
Gaussian vector with `E Xᵢ = 0` for every `i`, let the index type `Fin n` be nonempty, and let
`σ ≥ 0` satisfy `σ ^ 2 = maxᵢ Var[Xᵢ]`. Then for every `u ≥ 0`,
`P(maxᵢ Xᵢ - E maxᵢ Xᵢ ≥ u) ≤ exp (-u ^ 2 / (2 σ ^ 2))`. -/
theorem borellTIS_gaussianVector (hn : (Finset.univ : Finset (Fin n)).Nonempty)
    (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ2 : σ ^ 2 = ⨆ i, Var[fun ω => X ω i; P]) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ Finset.univ.sup' hn (X ω) - ∫ ω', Finset.univ.sup' hn (X ω') ∂P} ≤
      exp (-u ^ 2 / (2 * σ ^ 2)) := by
  have := hX.isProbabilityMeasure
  obtain ⟨v, hv, hmap⟩ := exists_gramVec_of_centered hX h0
  have hvσ : ∀ i, ‖v i‖ ≤ ((⟨σ, hσ⟩ : ℝ≥0) : ℝ) := norm_le_of_sq_eq_iSup hv hσ hσ2
  have hsc : Continuous fun x : Fin n → ℝ => Finset.univ.sup' hn x :=
    (lipschitzWith_sup' hn).continuous
  have hm : ∫ ω', Finset.univ.sup' hn (X ω') ∂P =
      ∫ z, Finset.univ.sup' hn (gramVec v z) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    have hg : Measurable (gramVec v) := (lipschitzWith_gramVec hvσ).continuous.measurable
    rw [← integral_map hX.aemeasurable hsc.aestronglyMeasurable, hmap,
      integral_map hg.aemeasurable hsc.aestronglyMeasurable]
  rw [hm]
  set m := ∫ z, Finset.univ.sup' hn (gramVec v z) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
  have hmeas : MeasurableSet {x : Fin n → ℝ | u ≤ Finset.univ.sup' hn x - m} :=
    measurableSet_le measurable_const (hsc.measurable.sub measurable_const)
  have e := measureReal_preimage_eq hX hmap hmeas
  simp only [preimage_setOf_eq] at e
  rw [e]
  exact borellTIS_finiteMax hn v hvσ hu

namespace GaussBorellVectorExample

/-- The hypotheses of `borellTIS_gaussianVector` hold for the centred Gaussian vector on `ℝ` whose
single coordinate is the standard Gaussian variable, with `σ = 1`. -/
example {u : ℝ} (hu : 0 ≤ u) :=
  have hX : HasGaussianLaw (fun ω : ℝ => fun _ : Fin 1 => ω) (stdGaussian ℝ) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℝ)).map_fun
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
  have hvar : Var[fun ω : ℝ => ω; stdGaussian ℝ] = 1 := by
    have h : Var[fun ω : ℝ => ω; stdGaussian ℝ] = ‖ContinuousLinearMap.id ℝ ℝ‖ ^ 2 :=
      variance_dual_stdGaussian (ContinuousLinearMap.id ℝ ℝ)
    rw [h]
    simp
  borellTIS_gaussianVector (n := 1) Finset.univ_nonempty hX (fun _ => by simp) zero_le_one
    (by simp [hvar]) hu

end GaussBorellVectorExample

end LatticeProb.GaussConc
