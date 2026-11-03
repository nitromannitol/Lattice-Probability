/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CircleAvgIntegral at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Integrals of continuous curves of test functions commute with distributions

For a compact `K ⊆ ℂ` and a continuous curve `F : ℝ → 𝓓_K(ℂ, ℝ)`, the pointwise integral
`y ↦ ∫_a^b F θ y dθ` is again an element `I` of `𝓓_K`, and every continuous linear functional
`T` on `𝓓_K` satisfies `T I = ∫_a^b T (F θ) dθ` (`exists_testIntegral`).

This is the standard "a distribution commutes with integrals of test functions depending
continuously on a parameter" (e.g. Hörmander, *The Analysis of Linear Partial Differential
Operators I*, Thm 2.1.3 / Schwartz's Riemann-sum argument). We do not follow the Riemann-sum
proof: we use instead (own argument, short and standard) that a continuous functional on the
Fréchet space `𝓓_K` is bounded by finitely many of its defining seminorms
(`WithSeminorms.bound_of_continuous`), hence factors through the Banach space of finite jets
`Jet s = Π i ∈ s, ℂ →ᵇ (ℂ [×i]→L ℝ)` (Hahn–Banach, `exists_extension_norm_eq`), where Bochner
integrals commute with continuous functionals. The derivatives of `I` are computed by
differentiation under the integral sign (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions BoundedContinuousFunction

namespace LQGMetric
namespace TestIntegral

/-- The Banach space of finite jets indexed by `s` (a `def`, so that only its normed
structure is seen by instance search). -/
def Jet (s : Finset ℕ) : Type :=
  ∀ i : s, ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ)

instance (s : Finset ℕ) : NormedAddCommGroup (Jet s) := Pi.normedAddCommGroup
instance (s : Finset ℕ) : NormedSpace ℝ (Jet s) := Pi.normedSpace
instance (s : Finset ℕ) : CompleteSpace (Jet s) :=
  inferInstanceAs
    (CompleteSpace (∀ i : s, ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ)))

/-- The `i`-th component of a jet. -/
def jetProj (s : Finset ℕ) (i : s) :
    Jet s →L[ℝ] ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ) :=
  ContinuousLinearMap.proj (R := ℝ)
    (φ := fun i : s => ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ)) i

lemma norm_jetProj_le (s : Finset ℕ) (v : Jet s) (i : s) : ‖jetProj s i v‖ ≤ ‖v‖ :=
  norm_le_pi_norm (G := fun i : s => ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ))
    v i

variable {K : Compacts ℂ}

/-- The jet map `φ ↦ (D^i φ)_{i ∈ s}`. -/
def jet (K : Compacts ℂ) (s : Finset ℕ) : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] Jet s :=
  ContinuousLinearMap.pi
    (φ := fun i : s => ℂ →ᵇ (ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => ℂ) ℝ))
    fun i => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)

lemma jet_apply (s : Finset ℕ) (φ : 𝓓^{⊤}_{K}(ℂ, ℝ)) (i : s) (y : ℂ) :
    jetProj s i (jet K s φ) y = iteratedFDeriv ℝ (i : ℕ) φ y := by
  show (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) φ) y = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]

/-- Every continuous linear functional on `𝓓_K` factors through a finite jet space. -/
theorem exists_jet_factor (T : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] ℝ) :
    ∃ (s : Finset ℕ) (S : StrongDual ℝ (Jet s)), ∀ φ, T φ = S (jet K s φ) := by
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K) ((normSeminorm ℝ ℝ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  have hbound : ∀ φ, ‖T φ‖ ≤ (C : ℝ) * ‖jet K s φ‖ := by
    intro φ
    have h1 := hle φ
    simp only [Seminorm.comp_apply, coe_normSeminorm, smul_apply,
      NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
    rw [ContDiffMapSupportedIn.seminorm_apply]
    exact norm_jetProj_le s (jet K s φ) ⟨i, hi⟩
  let J := (jet K s).toLinearMap
  have hker : LinearMap.ker J ≤ LinearMap.ker T.toLinearMap := by
    intro φ hφ
    simp only [LinearMap.mem_ker] at hφ ⊢
    have := hbound φ
    rw [show jet K s φ = 0 from hφ] at this
    simpa using this
  let f₀ : LinearMap.range J →ₗ[ℝ] ℝ :=
    ((LinearMap.ker J).liftQ T.toLinearMap hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hf₀ : ∀ φ, f₀ ⟨J φ, LinearMap.mem_range_self J φ⟩ = T φ := by
    intro φ
    simp only [f₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let f : StrongDual ℝ (LinearMap.range J) := f₀.mkContinuous C (by
    rintro ⟨v, φ, rfl⟩
    rw [hf₀]
    exact hbound φ)
  obtain ⟨S, hS, -⟩ := exists_extension_norm_eq (LinearMap.range J) f
  refine ⟨s, S, fun φ => ?_⟩
  have := hS ⟨J φ, LinearMap.mem_range_self J φ⟩
  rw [← hf₀ φ]
  exact this.symm

/-! ## Integrals of continuous curves -/

lemma integral_comp_lie {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] (a b : ℝ) (e : E ≃ₗᵢ[ℝ] G)
    (f : ℝ → E) : ∫ θ in a..b, e (f θ) = e (∫ θ in a..b, f θ) :=
  e.toLinearIsometry.intervalIntegral_comp_comm f

variable (F : ℝ → 𝓓^{⊤}_{K}(ℂ, ℝ)) (a b : ℝ)

/-- `∫_a^b D^i (F θ) y dθ`. -/
def intDeriv (i : ℕ) (y : ℂ) : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ :=
  ∫ θ in a..b, iteratedFDeriv ℝ i (F θ) y

variable {F}

lemma continuous_iteratedFDeriv_curve (hF : Continuous F) (i : ℕ) (y : ℂ) :
    Continuous fun θ => iteratedFDeriv ℝ i (F θ) y := by
  have := ((BoundedContinuousFunction.evalCLM ℝ y).continuous.comp
    ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous.comp hF))
  refine this.congr fun θ => ?_
  simp

lemma hasFDerivAt_intDeriv (hF : Continuous F) (i : ℕ) (y₀ : ℂ) :
    HasFDerivAt (intDeriv F a b i)
      (∫ θ in a..b, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y₀) y₀ := by
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
  have hF' : ∀ θ y, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y = e (iteratedFDeriv ℝ (i + 1) (F θ) y) := by
    intro θ y
    rw [fderiv_iteratedFDeriv]
    rfl
  have hcont : Continuous fun θ => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F θ) :=
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1)).continuous.comp hF
  obtain ⟨B, hB⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (f := fun θ => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F θ)) hcont.continuousOn
  show HasFDerivAt (fun y => ∫ θ in a..b, iteratedFDeriv ℝ i (F θ) y) _ y₀
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => B)
    (F' := fun y θ => fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y) (s := univ) Filter.univ_mem
  · exact Eventually.of_forall fun y =>
      (continuous_iteratedFDeriv_curve hF i y).aestronglyMeasurable
  · exact (continuous_iteratedFDeriv_curve hF i y₀).intervalIntegrable _ _
  · simp_rw [hF']
    exact (e.continuous.comp (continuous_iteratedFDeriv_curve hF (i + 1) y₀)).aestronglyMeasurable
  · refine Eventually.of_forall fun θ hθ y _ => ?_
    rw [norm_fderiv_iteratedFDeriv]
    refine le_trans ?_ (hB θ (uIoc_subset_uIcc hθ))
    have := (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i + 1) (F θ)).norm_coe_le_norm y
    simpa [ContDiffMapSupportedIn.structureMapCLM_top_apply] using this
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun θ _ y _ => ?_
    have hlt : ((i : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast ENat.natCast_lt_top i
    exact (((F θ).contDiff.differentiable_iteratedFDeriv hlt).differentiableAt).hasFDerivAt

lemma iteratedFDeriv_intFun (hF : Continuous F) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => ∫ θ in a..b, F θ y) = intDeriv F a b i := by
  induction i with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [intDeriv, Function.comp_apply]
    rw [← integral_comp_lie (E := ℝ) (G := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℂ) ℝ)
      a b (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm (fun θ => F θ y)]
    congr 1
  | succ i ih =>
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left, ih, Function.comp_apply,
      (hasFDerivAt_intDeriv a b hF i y).fderiv]
    set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
    have hF' : ∀ θ, fderiv ℝ (iteratedFDeriv ℝ i (F θ)) y =
        e (iteratedFDeriv ℝ (i + 1) (F θ) y) := by
      intro θ
      rw [fderiv_iteratedFDeriv]
      rfl
    simp_rw [hF']
    rw [integral_comp_lie (E := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => ℂ) ℝ)
      (G := ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ) a b e
      (fun θ => iteratedFDeriv ℝ (i + 1) (F θ) y), LinearIsometryEquiv.symm_apply_apply]
    rfl

/-- **Integral of a continuous curve in `𝓓_K`.** The pointwise integral is in `𝓓_K` and every
continuous linear functional commutes with the integral. -/
theorem exists_testIntegral (hF : Continuous F) :
    ∃ I : 𝓓^{⊤}_{K}(ℂ, ℝ), (∀ y, I y = ∫ θ in a..b, F θ y) ∧
      ∀ T : 𝓓^{⊤}_{K}(ℂ, ℝ) →L[ℝ] ℝ, T I = ∫ θ in a..b, T (F θ) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ θ in a..b, F θ y) := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
    rw [iteratedFDeriv_intFun a b hF m]
    exact fun y => (hasFDerivAt_intDeriv a b hF m y).differentiableAt
  have hsupp : Function.support (fun y => ∫ θ in a..b, F θ y) ⊆ K := by
    intro y hy
    by_contra hK
    apply hy
    simp only
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ _ =>
      (F θ).zero_on_compl hK]
    simp
  set I := ContDiffMapSupportedIn.of_support_subset hcd hsupp
  refine ⟨I, fun y => rfl, fun T => ?_⟩
  obtain ⟨s, S, hS⟩ := exists_jet_factor T
  have hjc : Continuous fun θ => jet K s (F θ) := (jet K s).continuous.comp hF
  have hji : IntervalIntegrable (fun θ => jet K s (F θ)) volume a b := hjc.intervalIntegrable a b
  have key : ∀ (i : s) (y : ℂ),
      jetProj s i (jet K s I) y = jetProj s i (∫ θ in a..b, jet K s (F θ)) y := by
    intro i y
    have hev := ((BoundedContinuousFunction.evalCLM ℝ y).comp
      (jetProj s i)).intervalIntegral_comp_comm hji
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      BoundedContinuousFunction.evalCLM_apply] at hev
    rw [← hev, jet_apply]
    simp_rw [jet_apply]
    exact congrFun (iteratedFDeriv_intFun a b hF (i : ℕ)) y
  have hjet : jet K s I = ∫ θ in a..b, jet K s (F θ) :=
    funext fun i => BoundedContinuousFunction.ext (key i)
  rw [hS, hjet, ← S.intervalIntegral_comp_comm hji]
  simp_rw [← hS]

end TestIntegral
end LQGMetric
