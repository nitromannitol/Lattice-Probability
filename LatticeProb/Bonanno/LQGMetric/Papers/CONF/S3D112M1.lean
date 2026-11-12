/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112M1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108K1
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.LQGMetric.Field.MarkovExt
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.MarkovNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-boundary GFF extended by `0` (`IsZBExtField`): affine invariance, the Markov version

Tools for `CONFZBExtOfMarkov` (S3D112L3; CONF C:1187–1190, LM Lemma 2.1):

* `zeroGFFTestCov_affine_ind` : `⟨1_{AU} φ∘A⁻¹, 1_{AU} ψ∘A⁻¹⟩_{H⁻¹(AU)} = r⁴ ⟨1_U φ, 1_U ψ⟩_{H⁻¹(U)}`
  for `φ, ψ ∈ 𝓓(ℂ)` (the computation of `zeroGFFTestCov_affine`, Field/ZeroBoundaryAffine, for
  the bounded densities `1_U φ` in place of test functions on `U`: Sheffield math/0312099 §2.2,
  conformal invariance of the Dirichlet inner product);
* `isZBExtField_affineComp` : `IsZBExtField` is preserved by `k ↦ k(r · + z)`;
* `isZBExtField_of_zbExt` : a distribution-valued version of `MarkovExt.zbExt` (the extension by
  zero of the zero-boundary part, LM Lemma 2.1's construction) is an `IsZBExtField`;
* `IsZBExtField.congr` : `IsZBExtField` only depends on the pairings up to null sets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric.CONF

open QuantumZipper

section Affine

variable {r : ℝ} {z : ℂ}

lemma coe_testAffinePull_eq (hr : r ≠ 0) (φ : TestC) :
    ⇑(testAffinePull r z φ) = (φ : ℂ → ℝ) ∘ affMap r z := by
  funext x
  simp only [testAffinePull, hr, dite_false]
  rfl

lemma indicator_affOpens_comp (U : Opens ℂ) (φ : ℂ → ℝ) :
    (affOpens r z U : Set ℂ).indicator (φ ∘ affMap r z) =
      ((U : Set ℂ).indicator φ) ∘ affMap r z := by
  funext x
  simp only [Function.comp_apply]
  by_cases hx : affMap r z x ∈ (U : Set ℂ)
  · rw [indicator_of_mem (show x ∈ (affOpens r z U : Set ℂ) from hx), indicator_of_mem hx]
    rfl
  · rw [indicator_of_notMem (show x ∉ (affOpens r z U : Set ℂ) from hx), indicator_of_notMem hx]

lemma integrable_indicator_test (U : Opens ℂ) (φ : TestC) :
    Integrable ((U : Set ℂ).indicator (φ : ℂ → ℝ)) :=
  (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).indicator
    U.isOpen.measurableSet

lemma affRel_gen (hr : r ≠ 0) (U : Opens ℂ) {ρ : ℂ → ℝ} (hρm : Measurable ρ) (hρ : Integrable ρ)
    (hρ' : Integrable (ρ ∘ affMap r z)) (hρU : ∀ x ∉ (U : Set ℂ), ρ x = 0) :
    AffRel r z U (testMeasPos (ρ ∘ affMap r z)) (testMeasPos ρ) := by
  refine ⟨isFiniteMeasure_withDensity_ofReal hρ'.2, isFiniteMeasure_withDensity_ofReal hρ.2,
    K3.withDensity_compl_null U.isOpen.measurableSet
      (fun x hx => by simp [hρU x hx]), fun f hf _ => ?_⟩
  have hA := (continuous_affFwd r z).measurable
  rw [integral_map hA.aemeasurable hf.aestronglyMeasurable]
  have h1 := K3.integral_testMeasPos_K3 (hρm.comp (continuous_affMap r z).measurable) f
  have h2 := K3.integral_testMeasPos_K3 hρm (fun y => f (affFwd r z y))
  rw [h1, h2]
  have e : ∫ y, max (ρ y) 0 * f (affFwd r z y) =
      ∫ y, (fun w => max ((ρ ∘ affMap r z) w) 0 * f w) (affFwd r z y) := by
    simp only [Function.comp_apply, affMap_affFwd hr]
  rw [e, integral_comp_affFwd (r := r) (z := z) (fun w => max ((ρ ∘ affMap r z) w) 0 * f w),
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]

lemma indicator_testAffinePull (hr : r ≠ 0) (U : Opens ℂ) (φ : TestC) :
    (affOpens r z U : Set ℂ).indicator (testAffinePull r z φ) =
      ((U : Set ℂ).indicator φ) ∘ affMap r z := by
  rw [coe_testAffinePull_eq hr, indicator_affOpens_comp]

lemma affRel_ind_pos (hr : r ≠ 0) (U : Opens ℂ) (φ : TestC) :
    AffRel r z U (testMeasPos ((affOpens r z U : Set ℂ).indicator (testAffinePull r z φ)))
      (testMeasPos ((U : Set ℂ).indicator φ)) := by
  have hi' := integrable_indicator_test (affOpens r z U) (testAffinePull r z φ)
  rw [indicator_testAffinePull hr] at hi' ⊢
  exact affRel_gen hr U (φ.continuous.measurable.indicator U.isOpen.measurableSet)
    (integrable_indicator_test U φ) hi'
    fun x hx => indicator_of_notMem hx _

lemma affRel_ind_neg (hr : r ≠ 0) (U : Opens ℂ) (φ : TestC) :
    AffRel r z U (testMeasNeg ((affOpens r z U : Set ℂ).indicator (testAffinePull r z φ)))
      (testMeasNeg ((U : Set ℂ).indicator φ)) := by
  have hi' := integrable_indicator_test (affOpens r z U) (testAffinePull r z φ)
  rw [indicator_testAffinePull hr] at hi' ⊢
  exact affRel_gen (ρ := fun x => -(U : Set ℂ).indicator φ x) hr U
    (φ.continuous.measurable.indicator U.isOpen.measurableSet).neg
    (integrable_indicator_test U φ).neg hi'.neg
    fun x hx => by simp [indicator_of_notMem hx]

/-- **Scaling of the covariance of the extension by `0`**:
`⟨1_{AU} φ∘A⁻¹, 1_{AU} ψ∘A⁻¹⟩_{H⁻¹(AU)} = r⁴ ⟨1_U φ, 1_U ψ⟩_{H⁻¹(U)}` (as `zeroGFFTestCov_affine`) -/
theorem zeroGFFTestCov_affine_ind (hr : r ≠ 0) (U : Opens ℂ) (φ ψ : TestC) :
    zeroGFFTestCov (affOpens r z U) ((affOpens r z U : Set ℂ).indicator (testAffinePull r z φ))
        ((affOpens r z U : Set ℂ).indicator (testAffinePull r z ψ)) =
      r ^ 4 * zeroGFFTestCov U ((U : Set ℂ).indicator φ) ((U : Set ℂ).indicator ψ) := by
  unfold zeroGFFTestCov
  rw [dualCov_affine hr (affRel_ind_pos hr U φ) (affRel_ind_pos hr U ψ),
    dualCov_affine hr (affRel_ind_pos hr U φ) (affRel_ind_neg hr U ψ),
    dualCov_affine hr (affRel_ind_neg hr U φ) (affRel_ind_pos hr U ψ),
    dualCov_affine hr (affRel_ind_neg hr U φ) (affRel_ind_neg hr U ψ)]
  ring

end Affine

section Law

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- `IsZBExtField` only depends on the pairings up to null sets -/
theorem IsZBExtField.congr {U : Opens ℂ} {X Y : Ω → DistC} (hX : IsZBExtField U X P)
    (hY : Measurable Y) (hae : ∀ φ : TestC, (fun ω => Y ω φ) =ᵐ[P] fun ω => X ω φ) :
    IsZBExtField U Y P where
  measurable := hY
  gaussian := hX.gaussian.congr fun φ => (hae φ).symm
  centered := fun φ => by rw [integral_congr_ae (hae φ), hX.centered]
  covariance_eq := fun φ ψ => by
    rw [CircleAvg.covariance_congr_ae (hae φ) (hae ψ), hX.covariance_eq]

/-- **Affine invariance**: if `X` is the zero-boundary GFF on `rU + z` extended by `0`, then
`X(r · + z)` is the zero-boundary GFF on `U` extended by `0` -/
theorem isZBExtField_affineComp {r : ℝ} {z : ℂ} (hr : r ≠ 0) {U : Opens ℂ} {X : Ω → DistC}
    (hX : IsZBExtField (affOpens r z U) X P) :
    IsZBExtField U (fun ω => affineComp r z (X ω)) P where
  measurable := (measurable_affineComp r z).comp hX.measurable
  gaussian := by
    have := (hX.gaussian.comp_right (testAffinePull r z)).smul (fun _ => (r ^ 2)⁻¹)
    exact this
  centered := fun φ => by
    simp only [GFFInv.affineComp_apply]
    rw [integral_const_mul, hX.centered, mul_zero]
  covariance_eq := fun φ ψ => by
    simp only [GFFInv.affineComp_apply]
    rw [covariance_const_mul_left, covariance_const_mul_right, hX.covariance_eq,
      zeroGFFTestCov_affine_ind hr]
    field_simp

/-- a distribution-valued version of the extension by zero `MarkovExt.zbExt` of the zero-boundary
part (bounded `U`) is the zero-boundary GFF extended by `0` -/
theorem isZBExtField_of_zbExt [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {U : Opens ℂ}
    (hU : Bornology.IsBounded (U : Set ℂ)) {hz : Ω → DistC} (hzm : Measurable hz)
    (hzae : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] MarkovExt.zbExt hh U φ) :
    IsZBExtField U hz P where
  measurable := hzm
  gaussian := by
    have := (MarkovExt.isGaussianProcess_zbExt_sumElim hh U).comp_right
      (Sum.inl : TestC → TestC ⊕ TestC0)
    exact this.congr fun φ => (hzae φ).symm
  centered := fun φ => by rw [integral_congr_ae (hzae φ), MarkovExt.integral_zbExt]
  covariance_eq := fun φ ψ => by
    rw [CircleAvg.covariance_congr_ae (hzae φ) (hzae ψ), MarkovExt.covariance_zbExt hh hU]

end Law

end LQGMetric.CONF
