/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.StandardBorelExt at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Tools for `StandardBorelSpace (DistOn U)`

* `exists_clm_extend`: an additive functional on a dense additive subgroup of a real topological
  vector space, dominated by a continuous seminorm, extends to a continuous linear functional
  (uniform extension, mathlib `uniformly_extend_of_ind`; additive + continuous ⇒ `ℝ`-linear,
  mathlib `AddMonoidHom.toRealLinearMap`). This is the density-extension step of the proof that
  `𝒟'` is a Lusin space (L. Schwartz, *Radon measures on arbitrary topological spaces and
  cylindrical measures*, Part II; Trèves, *TVS, Distributions and Kernels*, Ch. 13–14).
* `inclK`, `continuous_inclK`: the continuous inclusion `𝓓_K ⊆ 𝓓_{K'}` for `K ⊆ K'`.
* `standardBorelSpace_of_measurableEquiv`: standard Borel transfers along measurable equivalences.

Own elementary proofs of standard facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Topology Set TopologicalSpace Filter
open scoped Distributions

namespace LQGMetric

section ext
variable {X : Type*} [AddCommGroup X] [Module ℝ X] [UniformSpace X] [IsUniformAddGroup X]
  [ContinuousSMul ℝ X]

/-- density extension of a seminorm-dominated additive functional -/
theorem exists_clm_extend (p : Seminorm ℝ X) (hp : Continuous p) (S : AddSubgroup X)
    (hS : Dense (S : Set X)) (g : S →+ ℝ) (C : ℝ) (hg : ∀ s : S, |g s| ≤ C * p s) :
    ∃ T : X →L[ℝ] ℝ, ∀ s : S, T s = g s := by
  have hgc : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero]
    have h0 : Tendsto (fun s : S => C * p s) (𝓝 0) (𝓝 0) := by
      have := ((hp.comp continuous_subtype_val).tendsto (0 : S)).const_mul C
      simpa using this
    exact squeeze_zero_norm (fun s => by simpa [Real.norm_eq_abs] using hg s) h0
  have hu : UniformContinuous g := uniformContinuous_addMonoidHom_of_continuous hgc
  have he : IsUniformInducing (Subtype.val : S → X) := isUniformInducing_val _
  have hd : DenseRange (Subtype.val : S → X) := hS.denseRange_val
  have hT0c : Continuous ((he.isDenseInducing hd).extend g) :=
    (uniformContinuous_uniformly_extend he hd hu).continuous
  have hT0 : ∀ s : S, (he.isDenseInducing hd).extend g s = g s := uniformly_extend_of_ind he hd hu
  set T0 := (he.isDenseInducing hd).extend g
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := by
    intro x y
    refine hd.induction_on₂ (p := fun x y => T0 (x + y) = T0 x + T0 y) ?_ ?_ x y
    · exact isClosed_eq (hT0c.comp (continuous_fst.add continuous_snd))
        ((hT0c.comp continuous_fst).add (hT0c.comp continuous_snd))
    · intro a b
      have := hT0 (a + b)
      rw [AddSubgroup.coe_add] at this
      rw [this, hT0 a, hT0 b, map_add]
  refine ⟨(AddMonoidHom.mk' T0 hadd).toRealLinearMap hT0c, fun s => ?_⟩
  exact hT0 s

end ext

/-- the inclusion `𝓓_K ⊆ 𝓓_{K'}` -/
def inclK {K K' : Compacts ℂ} (h : (K : Set ℂ) ⊆ K') (ψ : 𝓓^{⊤}_{K}(ℂ, ℝ)) :
    𝓓^{⊤}_{K'}(ℂ, ℝ) where
  toFun := ψ
  contDiff' := ψ.contDiff
  zero_on_compl' := fun _ hx => ψ.zero_on_compl fun hxK => hx (h hxK)

theorem continuous_inclK {K K' : Compacts ℂ} (h : (K : Set ℂ) ⊆ K') :
    Continuous (inclK h) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  have : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ inclK h) =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext ψ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rfl
  rw [this]
  exact (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

/-- standard Borel transfers along measurable equivalences -/
theorem standardBorelSpace_of_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [hβ : StandardBorelSpace β] (e : α ≃ᵐ β) : StandardBorelSpace α := by
  obtain ⟨τ, hb, hp⟩ := hβ.polish
  let tα : TopologicalSpace α := TopologicalSpace.induced e τ
  have hpα : PolishSpace α := e.toEquiv.polishSpace_induced
  refine ⟨⟨tα, ⟨?_⟩, hpα⟩⟩
  show _ = @borel α (TopologicalSpace.induced e τ)
  rw [borel_comap, ← hb.measurable_eq]
  refine le_antisymm (fun s hs => ⟨e.symm ⁻¹' s, e.symm.measurable hs, ?_⟩)
    e.measurable.comap_le
  ext x; simp

end LQGMetric
