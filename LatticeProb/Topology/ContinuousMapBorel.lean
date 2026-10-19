/-
Adapted from Mathlib's `Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousMap.lean` (commit a4c8ef0a), which is not in the Mathlib version LP pins.
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# A measurable space structure on the type of continuous maps

In this file we endow the type `C(X, Y)` of continuous maps from `X` to `Y` with the Borel
sigma-algebra coming from the compact-open topology. We show that, under some assumptions on
`X` and `Y`, this is equal to the restriction of the product sigma-algebra over `X → Y`. This
means that a function `g : Z → C(X, Y)` is measurable if and only if, for all `x : X`,
`z ↦ g z x` is measurable. We then use this to build a measurable equivalence between
`{f : X → Y // Continuous f}` and `C(X, Y)`.

## Main definition

* `MeasurableEquiv.continuousMapToFun X Y`: A measurable equivalence between
  `C(X, Y)` and `{f : X → Y // Continuous f}`.

## Main statements

* `borel_eq_iSup_comap_eval`: The sigma-algebra over `C(X, Y)` is the coarsest that makes
  the maps `f ↦ f x` measurable for all `x : X`.
* `measurable_iff_eval`: A function `g : Z → C(X, Y)` is measurable if and only if,
  for all `x : X`, `z ↦ g z x` is measurable.

## References

* <https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr>

## Tags

continuous map, sigma-algebra
-/

namespace LatticeProb

open MeasurableSpace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The Borel sigma-algebra of the compact-open topology on the continuous maps `C(X, Y)`. -/
instance continuousMapMeasurableSpace : MeasurableSpace C(X, Y) := borel _

end LatticeProb

namespace LatticeProb.ContinuousMapBorel

open MeasurableSpace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The sigma-algebra on `C(X, Y)` is the Borel sigma-algebra of the compact-open topology. -/
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl

/-- For each point `x : X`, the evaluation map `f ↦ f x` is measurable. -/
lemma ContinuousMap.measurable_eval [MeasurableSpace Y] [BorelSpace Y] (x : X) :
    Measurable (fun f : C(X, Y) ↦ f x) :=
  Continuous.measurable (by fun_prop)

/-- The coarsest sigma-algebra over `C(X, Y)` making the evaluation maps `f ↦ f x` is
smaller than the Borel sigma-algebra coming from the compact-open topology. -/
lemma ContinuousMap.iSup_comap_le_borel :
    ⨆ x : X, (borel Y).comap (fun f ↦ f x) ≤ borel C(X, Y) := by
  borelize Y
  simp_rw [iSup_le_iff, ← measurable_iff_comap_le]
  exact ContinuousMap.measurable_eval

variable [SecondCountableTopology X] [SecondCountableTopology Y]
  [LocallyCompactSpace X] [RegularSpace Y]

namespace ContinuousMap

/-- The sigma-algebra over `C(X, Y)` is the coarsest that makes the maps `f ↦ f x` measurable
for all `x : X`.

The proof follows the one presented on <https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr>. -/
theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  refine le_antisymm ?_ iSup_comap_le_borel
  -- Denote `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable
  -- for the coarsest sigma-algebra that makes the maps `f ↦ f x` measurable for all `x : X`.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  apply generateFrom_le
  rintro - ⟨K, hK, U, hU, rfl⟩
  obtain rfl | ⟨x, hx⟩ := U.eq_empty_or_nonempty
  · simp
  -- Let `V` be the finite unions of sets of `countableBasis Y`; it is countable.
  let V := Set.sUnion '' {f : Set (Set Y) | f.Finite ∧ f ⊆ countableBasis Y}
  have cV : V.Countable :=
    (Set.countable_setOf_finite_subset (countable_countableBasis Y)).image _
  -- Because `Y` is regular, every point of `U` has a basis set whose closure lies in `U`.
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, finitely many of
  -- these basis sets cover `f '' K`; their finite union `v` lies in `V` and `f '' K ⊆ v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ v ∈ V, closure v ⊆ U ∧ K.MapsTo f (closure v) := by
    let W : Set (Set Y) := {b | b ∈ countableBasis Y ∧ closure b ⊆ U}
    have hWcov : f '' K ⊆ ⋃ b ∈ W, b := by
      rintro - ⟨y, hy, rfl⟩
      obtain ⟨b, hb, hyb, hbU⟩ :=
        (isBasis_countableBasis Y).exists_closure_subset (hU.mem_nhds (hf hy))
      exact Set.mem_biUnion ⟨hb, hbU⟩ hyb
    obtain ⟨t, ht⟩ := (hK.image f.continuous).elim_finite_subcover
      (fun b : W ↦ (b : Set Y)) (fun b ↦ isOpen_of_mem_countableBasis b.2.1) fun y hy ↦ by
        obtain ⟨b, hbW, hyb⟩ := Set.mem_iUnion₂.1 (hWcov hy)
        exact Set.mem_iUnion.2 ⟨⟨b, hbW⟩, hyb⟩
    let F : Set (Set Y) := (fun b : W ↦ (b : Set Y)) '' ↑t
    have hFfin : F.Finite := t.finite_toSet.image _
    have hFsub : F ⊆ countableBasis Y := by
      rintro - ⟨b, -, rfl⟩
      exact b.2.1
    have hcl : closure (⋃₀ F) ⊆ U := by
      rw [Set.sUnion_eq_biUnion, hFfin.closure_biUnion]
      refine Set.iUnion₂_subset fun b hb ↦ ?_
      obtain ⟨b', -, rfl⟩ := hb
      exact b'.2.2
    refine ⟨⋃₀ F, ⟨F, ⟨hFfin, hFsub⟩, rfl⟩, hcl, fun x hx ↦ subset_closure ?_⟩
    obtain ⟨b, hbt, hxb⟩ := Set.mem_iUnion₂.1 (ht ⟨x, hx, rfl⟩)
    exact ⟨(b : Set Y), ⟨b, hbt, rfl⟩, hxb⟩
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{u ∈ V, closure u ⊆ U}, M(K, closure u)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃ u ∈ V, ⋃ (_ : closure u ⊆ U), {f : C(X, Y) | K.MapsTo f (closure u)} := by
    ext f
    simpa using ⟨by grind, fun ⟨u, hu1, hu2, hu3⟩ ↦ hu3.mono_right hu1⟩
  simp_rw [this]
  -- In particular, because `V` is countable, this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  refine .biUnion cV (fun v hv1 ↦ .iUnion (fun hv2 ↦ ?_))
  -- Consider now `v ∈ V` such that `closure v ⊆ U`.
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, hQ, cQ, dQ⟩ : ∃ Q ⊆ K, Q.Countable ∧ K ⊆ closure Q := by
    obtain ⟨t, htc, htd⟩ := exists_countable_dense (α := K)
    refine ⟨Subtype.val '' t, Subtype.coe_image_subset K t, htc.image _, fun x hx ↦ ?_⟩
    have hx' := htd ⟨x, hx⟩
    rwa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hx'
  -- Because `f` is continuous and `closure v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ closure v` is the same as `f '' Q ⊆ closure v`.
  have : {f : C(X, Y) | K.MapsTo f (closure v)} = {f : C(X, Y) | Q.MapsTo f (closure v)} := by
    ext f
    refine ⟨fun h ↦ h.mono_left hQ, fun h ↦ ?_⟩
    simpa using h.closure f.continuous |>.mono_left dQ
  -- We can write `M(Q, closure v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (closure v)`.
  have : {f : C(X, Y) | K.MapsTo f (closure v)} = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (closure v) := by
    ext f
    rw [this, Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `closure v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  borelize Y
  refine .biInter cQ fun q hq ↦ .preimage measurableSet_closure (.le (le_iSup _ q) ?_)
  rw [BorelSpace.measurable_eq (α := Y)]
  exact comap_measurable _

variable [mY : MeasurableSpace Y] [BorelSpace Y]

/-- The sigma-algebra over `C(X, Y)` is the coarsest that makes the maps `f ↦ f x` measurable
for all `x : X`, stated for the ambient sigma-algebra of `Y`. -/
lemma measurableSpace_eq_iSup_comap_eval :
    continuousMapMeasurableSpace = ⨆ a : X, mY.comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

/-- A function `g : Z → C(X, Y)` is measurable if and only if,
for all `x : X`, `z ↦ g z x` is measurable. -/
lemma measurable_iff_eval {Z : Type*} [MeasurableSpace Z] {g : Z → C(X, Y)} :
    Measurable g ↔ ∀ (x : X), Measurable fun a ↦ g a x := by
  rw [measurableSpace_eq_iSup_comap_eval]
  simp_rw [measurable_iff_comap_le, comap_iSup, iSup_le_iff, comap_comp, Function.comp_def]

end ContinuousMap

namespace MeasurableEquiv

variable [MeasurableSpace Y] [BorelSpace Y]

variable (X Y) in
/-- A measurable equivalence between `C(X, Y)` and `{f : X → Y // Continuous f}`. -/
def continuousMapToFun : C(X, Y) ≃ᵐ {f : X → Y // Continuous f} where
  toFun f := ⟨f, f.continuous⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun :=
    .subtype_mk (measurable_pi_lambda _ fun x ↦ (continuous_eval_const x).measurable)
  measurable_invFun :=
    ContinuousMap.measurable_iff_eval.2 fun x ↦ by simpa using measurable_subtype_coe.eval

/-- `continuousMapToFun X Y` sends `f` to the subtype element `⟨f, f.continuous⟩`. -/
@[simp]
lemma continuousMapToFun_apply (f : C(X, Y)) :
    continuousMapToFun X Y f = ⟨f, f.continuous⟩ := rfl

/-- The inverse of `continuousMapToFun X Y` sends `f` to its underlying function. -/
@[simp]
lemma symm_continuousMapToFun_apply (f : {g : X → Y // Continuous g}) :
    (continuousMapToFun X Y).symm f = ⟨f.1, f.2⟩ := rfl

/-- Evaluating the underlying function of `continuousMapToFun X Y f` at `x` gives `f x`. -/
lemma continuousMapToFun_apply_apply (f : C(X, Y)) (x : X) :
    (continuousMapToFun X Y f).1 x = f x := rfl

/-- Evaluating the inverse of `continuousMapToFun X Y` at `x` gives `f.1 x`. -/
lemma symm_continuousMapToFun_apply_apply (f : {g : X → Y // Continuous g}) (x : X) :
    (continuousMapToFun X Y).symm f x = f.1 x := rfl

end MeasurableEquiv

end LatticeProb.ContinuousMapBorel
