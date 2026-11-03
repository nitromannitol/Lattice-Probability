/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.RandomDistComplete at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish

/-!
# `𝓓_K(ℂ)` is a Fréchet space: completeness and the Banach–Steinhaus theorem

Berestycki–Powell, arXiv:2404.16642, appendix (`SLE.tex` l. 482–515) use that the test function
spaces are separable Fréchet spaces and apply the Banach–Steinhaus theorem in Fréchet spaces
(their reference [TVS, Thm 11.9.1]). Mathlib (pin) has the topology of `𝓓_K` but not its
completeness; we prove it here:

* `completeSpace_testK`: `𝓓_K` is complete. Its topology is the one induced by the uniform
  embedding `f ↦ (Dⁱf)ᵢ` into `Πᵢ (ℂ →ᵇ M_i)` (mathlib `isUniformEmbedding_pi_structureMapCLM`),
  and the range is closed: if `Dⁱf_k → g_i` uniformly for every `i`, then `g_0` is smooth with
  `Dⁱ g_0 = g_i` (uniform limits of derivatives, mathlib `hasFDerivAt_of_tendstoUniformly`).
* `barrelledSpace_testK`: hence `𝓓_K` is a Baire, hence barrelled, space (mathlib).

Own elementary proof of a standard fact (e.g. Trèves, *TVS, Distributions and Kernels*, Ch. 14).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Topology Set Filter
open scoped Distributions

namespace LQGMetric

section
variable (K : TopologicalSpace.Compacts ℂ)

/-- `𝓓_K(ℂ)` is complete -/
instance completeSpace_testK : CompleteSpace 𝓓^{⊤}_{K}(ℂ, ℝ) := by
  have hΦ := ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ (E := ℂ) (F := ℝ)
    (n := ⊤) (K := K)
  rw [completeSpace_iff_isComplete_range hΦ.isUniformInducing]
  apply IsClosed.isComplete
  refine isClosed_of_closure_subset fun g hg => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hg
  choose f hf using hu
  have hconv : ∀ i, TendstoUniformly (fun k x => iteratedFDeriv ℝ i (f k) x) (g i) atTop := by
    intro i
    have h1 : TendstoUniformly (fun k => ⇑(u k i)) (g i) atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1
        (((continuous_apply i).tendsto g).comp hlim)
    have h2 : (fun k => ⇑(u k i)) = fun k x => iteratedFDeriv ℝ i (f k) x := by
      funext k x
      rw [← hf k]
      simp
    rwa [h2] at h1
  let F : ℂ → ℝ := fun x => g 0 x 0
  have hptw : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (F x)) := by
    intro x
    have := ((continuous_eval_const (0 : Fin 0 → ℂ)).tendsto _).comp
      ((hconv 0).tendsto_at x)
    simpa [F, Function.comp_def, iteratedFDeriv_zero_apply] using this
  let e : ∀ i : ℕ, (ℂ [×(i + 1)]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (ℂ →L[ℝ] (ℂ [×i]→L[ℝ] ℝ)) := fun i =>
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
  have hfd : ∀ (k i : ℕ) (y : ℂ),
      fderiv ℝ (iteratedFDeriv ℝ i (f k)) y = e i (iteratedFDeriv ℝ (i + 1) (f k) y) := by
    intro k i y
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp [e]
  have hD : ∀ i y, HasFDerivAt (fun z => g i z) (e i (g (i + 1) y)) y := by
    intro i
    refine hasFDerivAt_of_tendstoUniformly (f := fun k z => iteratedFDeriv ℝ i (f k) z)
      (f' := fun k z => e i (iteratedFDeriv ℝ (i + 1) (f k) z))
      ((e i).isometry.uniformContinuous.comp_tendstoUniformly (hconv (i + 1))) ?_
      (fun z => (hconv i).tendsto_at z)
    intro k z
    rw [← hfd]
    exact (((f k).contDiff.differentiable_iteratedFDeriv
      (by exact_mod_cast WithTop.coe_lt_top _)) z).hasFDerivAt
  have hI : ∀ i, iteratedFDeriv ℝ i F = fun y => g i y := by
    intro i
    induction i with
    | zero =>
      funext y
      ext m
      rw [iteratedFDeriv_zero_apply, Subsingleton.elim m 0]
    | succ i ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext y
      simp only [Function.comp_apply, (hD i y).fderiv]
      exact (e i).symm_apply_apply _
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    contDiff_of_differentiable_iteratedFDeriv fun m _ => by
      rw [hI m]; exact fun y => (hD m y).differentiableAt
  have hz : EqOn F 0 (K : Set ℂ)ᶜ := fun x hx =>
    tendsto_nhds_unique (hptw x) (by simp [(f _).zero_on_compl hx])
  let fLim : 𝓓^{⊤}_{K}(ℂ, ℝ) := ⟨F, hcd, hz⟩
  refine ⟨fLim, funext fun i => ?_⟩
  ext y : 1
  simp only [ContinuousLinearMap.pi_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrFun (hI i) y

instance isCountablyGenerated_uniformity_testK :
    (uniformity 𝓓^{⊤}_{K}(ℂ, ℝ)).IsCountablyGenerated := by
  have h := congrArg (fun u : UniformSpace 𝓓^{⊤}_{K}(ℂ, ℝ) => @uniformity _ u)
    (ContDiffMapSupportedIn.uniformSpace_eq_iInf (E := ℂ) (F := ℝ) (n := ⊤) (K := K))
  simp only [iInf_uniformity, uniformity_comap] at h
  rw [h]
  infer_instance

/-- `𝓓_K(ℂ)` is barrelled (Baire), so the Banach–Steinhaus theorem applies -/
instance barrelledSpace_testK : BarrelledSpace ℝ 𝓓^{⊤}_{K}(ℂ, ℝ) := inferInstance

end

end LQGMetric
