/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovWeylInt at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Integrals of bounded continuous families of test functions (task P2-MKA, toward leaf (H))

Generalization of `TestIntegral.exists_testIntegral` (`CircleAvgIntegral.lean`, interval
integrals of continuous curves) to an arbitrary finite measure `μ` on a (second countable,
metrizable) parameter space `X` and a continuous family `F : X → 𝓓_K` that is bounded in each
seminorm: the pointwise integral `y ↦ ∫ F θ y dμ(θ)` is again in `𝓓_K` and every continuous
linear functional `T` on `𝓓_K` satisfies `T (∫ F dμ) = ∫ T (F θ) dμ(θ)`
(`exists_testIntegral_measure`).

This is the step "a distribution commutes with integrals of test functions" in the proof of
Weyl's lemma by mollification (e.g. Hörmander, *The Analysis of Linear PDO I*, Thm 2.1.3 and
§4.1 (regularization `u * φ`)): `T(φ * ρ)
= ∫ φ(y) T(ρ(· − y)) dy`. The proof is the one of `exists_testIntegral` (finite jets, Hahn–Banach,
differentiation under the integral sign, mathlib `hasFDerivAt_integral_of_dominated_of_fderiv_le`).
-/

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped Distributions BoundedContinuousFunction

namespace LQGMetric
namespace MarkovWeyl

open TestIntegral

variable {K : Compacts ℂ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [PseudoMetrizableSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsFiniteMeasure μ] {F : X → 𝓓^{⊤}_{K}(ℂ, ℝ)}

omit [OpensMeasurableSpace X] [PseudoMetrizableSpace X] [SecondCountableTopology X]
  [IsFiniteMeasure μ] in
lemma integral_comp_lie_m {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (e : E ≃ₗᵢ[ℝ] G) (f : X → E) : ∫ θ, e (f θ) ∂μ = e (∫ θ, f θ ∂μ) :=
  e.toLinearIsometry.integral_comp_comm f

/-- `∫ D^i (F θ) y dμ(θ)`. -/
def mDeriv (F : X → 𝓓^{⊤}_{K}(ℂ, ℝ)) (i : ℕ) (y : ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ :=
  ∫ θ, iteratedFDeriv ℝ i (F θ) y ∂μ

lemma continuous_iteratedFDeriv_fam (hF : Continuous F) (i : ℕ) (y : ℂ) :
    Continuous fun θ => iteratedFDeriv ℝ i (F θ) y := by
  have := ((BoundedContinuousFunction.evalCLM ℝ y).continuous.comp
    ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous.comp hF))
  refine this.congr fun θ => ?_
  simp

lemma norm_iteratedFDeriv_fam_le {i : ℕ} {B : ℝ}
    (hB : ∀ θ, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)‖ ≤ B) (θ : X) (y : ℂ) :
    ‖iteratedFDeriv ℝ i (F θ) y‖ ≤ B := by
  refine le_trans ?_ (hB θ)
  have := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)).norm_coe_le_norm y
  simpa [ContDiffMapSupportedIn.structureMapCLM_top_apply] using this

lemma integrable_iteratedFDeriv_fam (hF : Continuous F)
    (hB : ∀ i, ∃ B, ∀ θ, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)‖ ≤ B)
    (i : ℕ) (y : ℂ) : Integrable (fun θ => iteratedFDeriv ℝ i (F θ) y) μ := by
  obtain ⟨B, hB⟩ := hB i
  exact Integrable.of_bound (continuous_iteratedFDeriv_fam hF i y).aestronglyMeasurable B
    (Eventually.of_forall fun θ => norm_iteratedFDeriv_fam_le hB θ y)

lemma hasFDerivAt_mDeriv (hF : Continuous F)
    (hB : ∀ i, ∃ B, ∀ θ, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)‖ ≤ B)
    (i : ℕ) (y₀ : ℂ) :
    HasFDerivAt (mDeriv μ F i) (∫ θ, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y₀ ∂μ) y₀ := by
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
  have hF' : ∀ θ y, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y =
      e (iteratedFDeriv ℝ (i + 1) (F θ) y) := by
    intro θ y
    rw [fderiv_iteratedFDeriv]
    rfl
  obtain ⟨B, hB1⟩ := hB (i + 1)
  show HasFDerivAt (fun y => ∫ θ, iteratedFDeriv ℝ i (F θ) y ∂μ) _ y₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => B)
    (F' := fun y θ => fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y) (s := univ) Filter.univ_mem
  · exact Eventually.of_forall fun y =>
      (continuous_iteratedFDeriv_fam hF i y).aestronglyMeasurable
  · exact integrable_iteratedFDeriv_fam μ hF hB i y₀
  · simp_rw [hF']
    exact (e.continuous.comp (continuous_iteratedFDeriv_fam hF (i + 1) y₀)).aestronglyMeasurable
  · refine Eventually.of_forall fun θ y _ => ?_
    rw [norm_fderiv_iteratedFDeriv]
    exact norm_iteratedFDeriv_fam_le hB1 θ y
  · exact integrable_const _
  · refine Eventually.of_forall fun θ y _ => ?_
    have hlt : ((i : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast ENat.natCast_lt_top i
    exact (((F θ).contDiff.differentiable_iteratedFDeriv hlt).differentiableAt).hasFDerivAt

lemma iteratedFDeriv_mFun (hF : Continuous F)
    (hB : ∀ i, ∃ B, ∀ θ, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)‖ ≤ B) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => ∫ θ, F θ y ∂μ) = mDeriv μ F i := by
  induction i with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [mDeriv, Function.comp_apply]
    rw [← integral_comp_lie_m μ (E := ℝ) (G := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℂ) ℝ)
      (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm (fun θ => F θ y)]
    congr 1
  | succ i ih =>
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left, ih, Function.comp_apply,
      (hasFDerivAt_mDeriv μ hF hB i y).fderiv]
    set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
    have hF' : ∀ θ, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y =
        e (iteratedFDeriv ℝ (i + 1) (F θ) y) := by
      intro θ
      rw [fderiv_iteratedFDeriv]
      rfl
    simp_rw [hF']
    rw [integral_comp_lie_m μ (E := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => ℂ) ℝ)
      (G := ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ) e
      (fun θ => iteratedFDeriv ℝ (i + 1) (F θ) y), LinearIsometryEquiv.symm_apply_apply]
    rfl

/-- **Integral of a bounded continuous family in `𝓓_K`.** The pointwise integral is in `𝓓_K`
and every continuous linear functional commutes with the integral. -/
theorem exists_testIntegral_measure (hF : Continuous F)
    (hB : ∀ i, ∃ B, ∀ θ, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (F θ)‖ ≤ B) :
    ∃ I : 𝓓^{⊤}_{K}(ℂ, ℝ), (∀ y, I y = ∫ θ, F θ y ∂μ) ∧
      ∀ T : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] ℝ, T I = ∫ θ, T (F θ) ∂μ := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ θ, F θ y ∂μ) := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
    rw [iteratedFDeriv_mFun μ hF hB m]
    exact fun y => (hasFDerivAt_mDeriv μ hF hB m y).differentiableAt
  have hsupp : Function.support (fun y => ∫ θ, F θ y ∂μ) ⊆ K := by
    intro y hy
    by_contra hK
    apply hy
    simp only
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (Eventually.of_forall fun θ =>
      (F θ).zero_on_compl hK)]
    simp
  set I := ContDiffMapSupportedIn.of_support_subset hcd hsupp
  refine ⟨I, fun y => rfl, fun T => ?_⟩
  obtain ⟨s, S, hS⟩ := exists_jet_factor T
  have hjc : Continuous fun θ => jet K s (F θ) := (jet K s).continuous.comp hF
  have hji : Integrable (fun θ => jet K s (F θ)) μ := by
    choose B hB using hB
    refine Integrable.of_bound hjc.aestronglyMeasurable (∑ i ∈ s, |B i|)
      (Eventually.of_forall fun θ => ?_)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => abs_nonneg (B j)) i.2)
    refine le_trans ?_ (le_abs_self _)
    refine le_trans (le_of_eq ?_) (hB i θ)
    rfl
  have key : ∀ (i : s) (y : ℂ),
      jetProj s i (jet K s I) y = jetProj s i (∫ θ, jet K s (F θ) ∂μ) y := by
    intro i y
    have hev := ((BoundedContinuousFunction.evalCLM ℝ y).comp
      (jetProj s i)).integral_comp_comm hji
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      BoundedContinuousFunction.evalCLM_apply] at hev
    rw [← hev, jet_apply]
    simp_rw [jet_apply]
    exact congrFun (iteratedFDeriv_mFun μ hF hB (i : ℕ)) y
  have hjet : jet K s I = ∫ θ, jet K s (F θ) ∂μ :=
    funext fun i => BoundedContinuousFunction.ext (key i)
  rw [hS, hjet, ← S.integral_comp_comm hji]
  simp_rw [← hS]

end MarkovWeyl
end LQGMetric
