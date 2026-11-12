/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.ConcentrationVector at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.ConcentrationDZZ
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittVector

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Random-vector forms of `GaussConc.dzz_lemma21_gram` and `GaussConc.borellTIS_finiteMax`.
A centered Gaussian vector `X : Ω → (Fin n → ℝ)` (`HasGaussianLaw X P`, `E X_i = 0`) has the law
of `(⟪v i, Z⟫)_i` with `Z` standard Gaussian and `‖v i‖² = Var X_i`
(`exists_gramVec_of_centered`, from `Pitt.exists_gram_map_eq`; this is DZZ's `X = A Z`).

* `dzz_lemma21`: J. Ding, O. Zeitouni, F. Zhang, arXiv:1807.00422, Lemma 2.1 (LaTeX lines
  326–348), as stated there (with prefactor `C`).
* `dfgps_lemma42`: Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, Lemma 4.2
  (`lqg-metric-estimates-final.tex`, lines 2537–2546): strict inequality, no prefactor.
* `borellTIS_gaussianVector`: Adler–Taylor, *Random Fields and Geometry*, Thm 2.1.1 for finite
  `T` (p. 56).

Here `min_{x ∈ B} |X - x|_∞` is `Metric.infDist (X ω) B` for the sup metric of `Fin n → ℝ`, and
`σ² = max_i Var X_i` is `σ ^ 2 = ⨆ i, Var[X_i]` with `σ ≥ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace GaussConc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}

/-- A centered Gaussian vector is `A Z` in law, with rows of norm `√Var X_i`. -/
theorem exists_gramVec_of_centered (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n),
      (∀ i, ‖v i‖ ^ 2 = Var[fun ω => X ω i; P]) ∧
      P.map X = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (gramVec v) := by
  obtain ⟨v, hv, hmap⟩ := Pitt.exists_gram_map_eq hX
  refine ⟨v, fun i => ?_, ?_⟩
  · rw [← real_inner_self_eq_norm_sq, hv, covariance_self]
    exact (measurable_pi_apply i).comp_aemeasurable hX.aemeasurable
  · rw [hmap]
    congr 1
    funext x
    ext i
    simp [gramVec, h0]

lemma norm_le_of_sq_eq_iSup {v : Fin n → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ i, ‖v i‖ ^ 2 = Var[fun ω => X ω i; P]) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ2 : σ ^ 2 = ⨆ i, Var[fun ω => X ω i; P]) (i : Fin n) : ‖v i‖ ≤ σ := by
  have h : ‖v i‖ ^ 2 ≤ σ ^ 2 := by
    rw [hv, hσ2]; exact le_ciSup (f := fun i => Var[fun ω => X ω i; P]) (Finite.bddAbove_range _) i
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h

/-- Transfer of probabilities of measurable events along the representation. -/
lemma measureReal_preimage_eq {v : Fin n → EuclideanSpace ℝ (Fin n)} (hX : HasGaussianLaw X P)
    (hmap : P.map X = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (gramVec v))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    P.real (X ⁻¹' S) = (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gramVec v ⁻¹' S) := by
  have hg : Measurable (gramVec v) :=
    (continuous_pi fun i => continuous_const.inner continuous_id).measurable
  rw [measureReal_def, measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable hS,
    hmap, Measure.map_apply hg hS]

/-- **Borell–TIS inequality for a centered Gaussian vector** (Adler–Taylor, Thm 2.1.1, finite
`T`): with `σ² = max_i Var X_i` and `u ≥ 0`,
`P(max_i X_i - E max_i X_i ≥ u) ≤ exp (-u² / (2σ²))`. -/
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

end GaussConc

end LQGMetric
