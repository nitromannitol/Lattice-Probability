/-
Nonzero determinants characterize rooted selections of original incidence columns.
-/

import LatticeProb.Graph.CopiedGraph.IncidenceSpan
import LatticeProb.Graph.CopiedGraph.RootedForest
import LatticeProb.Graph.CopiedGraph.ComponentKernel
import Mathlib.LinearAlgebra.LinearIndependent.Basic



namespace LatticeProb.Graph.CopiedGraph

open scoped Classical BigOperators
noncomputable section
variable {V E A : Type*}

/-- Distinct vertices have distinct integer coordinate columns, even on an empty carrier. -/
theorem unitColumn_injective : Function.Injective (unitColumn (V := V)) := by
  intro x y h
  by_contra hxy
  have hx := congrFun h x
  change (if x = x then (1 : ℤ) else 0) = (if x = y then 1 else 0) at hx
  rw [if_pos rfl, if_neg hxy] at hx
  exact one_ne_zero hx

/-- An erased-copy walk puts that copy's column in the span of the other columns,
contradicting independence. This also excludes selected loops and parallel-copy cycles. -/
theorem isForest_of_linearIndependent_incidenceColumn (J : CopiedGraph V E) (F : Finset E)
    (hli : LinearIndependent ℤ (fun f : F => J.incidenceColumn f.val)) : J.IsForest F := by
  intro e he hwalk
  let s : Set F := {f | f.val ≠ e}
  have hout : (⟨e, he⟩ : F) ∉ s := fun h => h rfl
  apply hli.notMem_span_image hout
  have hsub : Set.range (fun f : F.erase e => J.incidenceColumn f.val) ⊆
      (fun f : F => J.incidenceColumn f.val) '' s := by
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨f.val, Finset.mem_of_mem_erase f.property⟩,
      (Finset.mem_erase.mp f.property).1, rfl⟩
  exact Submodule.span_mono hsub (J.unitColumn_sub_mem_span_of_reaches (F.erase e) hwalk)

/-- The actual erased-copy walk is a witness of dependence of the original-copy columns. -/
theorem not_linearIndependent_incidenceColumn_of_reaches_erase
    (J : CopiedGraph V E) (F : Finset E) (e : E) (he : e ∈ F)
    (hwalk : J.reaches (F.erase e) (J.left e) (J.right e)) :
    ¬LinearIndependent ℤ (fun f : F => J.incidenceColumn f.val) :=
  fun hli => J.isForest_of_linearIndependent_incidenceColumn F hli e he hwalk

/-- Independence after deleting root coordinates forces any connected pair of roots to agree.
The full integer walk difference is in the incidence span, which is disjoint from the
kernel of restriction. -/
theorem eq_of_reaches_roots_of_linearIndependent_nonrootIncidence
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (hli : LinearIndependent ℤ (J.nonrootIncidence F R).col)
    {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hwalk : J.reaches F x y) : x = y := by
  let q : (V → ℤ) →ₗ[ℤ] ({v : V // v ∉ R} → ℤ) :=
    LinearMap.funLeft ℤ ℤ Subtype.val
  have hdj : Disjoint
      (Submodule.span ℤ (Set.range (fun f : F => J.incidenceColumn f.val)))
      (LinearMap.ker q) := Submodule.range_ker_disjoint hli
  have hk : unitColumn x - unitColumn y ∈ LinearMap.ker q := by
    change q (unitColumn x - unitColumn y) = 0
    ext v
    have hvx : v.val ≠ x := fun h => v.property (h.symm ▸ hx)
    have hvy : v.val ≠ y := fun h => v.property (h.symm ▸ hy)
    change (if v.val = x then (1 : ℤ) else 0) - (if v.val = y then 1 else 0) = 0
    rw [if_neg hvx, if_neg hvy, sub_self]
  have hz : unitColumn x - unitColumn y = 0 :=
    (Submodule.disjoint_def.mp hdj) _ (J.unitColumn_sub_mem_span_of_reaches F hwalk) hk
  exact unitColumn_injective (sub_eq_zero.mp hz)

/-- A walk between distinct roots gives dependence of the actual restricted copy columns. -/
theorem not_linearIndependent_nonrootIncidence_of_connected_roots
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V) {x y : V}
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) (hwalk : J.reaches F x y) :
    ¬LinearIndependent ℤ (J.nonrootIncidence F R).col :=
  fun hli => hxy (J.eq_of_reaches_roots_of_linearIndependent_nonrootIncidence
    F R hli hx hy hwalk)

/-- Column independence of a square minor gives independence on the actual nonroot carrier. -/
theorem linearIndependent_nonrootIncidence_of_det_ne_zero
    [Fintype A] [DecidableEq A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F)
    (hdet : ((J.nonrootIncidence F R).submatrix a b).det ≠ 0) :
    LinearIndependent ℤ (J.nonrootIncidence F R).col := by
  let q : ({v : V // v ∉ R} → ℤ) →ₗ[ℤ] (A → ℤ) := LinearMap.funLeft ℤ ℤ a
  have hcomp : LinearIndependent ℤ (q ∘ ((J.nonrootIncidence F R).col ∘ b)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  exact (linearIndependent_equiv b).mp (LinearIndependent.of_comp q hcomp)

/-- A nonzero literal nonroot incidence minor forces the selected original copies to form
the exact rooted forest: acyclicity, root coverage and uniqueness are all derived. -/
theorem isRootedForest_of_det_nonrootIncidence_ne_zero [Fintype V]
    [Fintype A] [DecidableEq A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F)
    (hdet : ((J.nonrootIncidence F R).submatrix a b).det ≠ 0) :
    J.IsRootedForest (R : Set V) F := by
  have hli := J.linearIndependent_nonrootIncidence_of_det_ne_zero F R a b hdet
  let q : (V → ℤ) →ₗ[ℤ] ({v : V // v ∉ R} → ℤ) :=
    LinearMap.funLeft ℤ ℤ Subtype.val
  refine ⟨J.isForest_of_linearIndependent_incidenceColumn F
    (LinearIndependent.of_comp q hli), ?_⟩
  intro x
  have hcover : ∃ r ∈ R, J.reaches F x r := by
    by_contra h
    push Not at h
    exact hdet (J.det_nonroot_incidence_eq_zero_of_missing_root
      (K := ℤ) F R a b x h)
  obtain ⟨r, hr, hxr⟩ := hcover
  refine ⟨r, hr, hxr, ?_⟩
  intro s hs hxs
  exact J.eq_of_reaches_roots_of_linearIndependent_nonrootIncidence F R hli hs hr
    ((J.reaches_symm hxs).trans hxr)

/-- Every selection that fails the exact rooted-forest predicate has zero nonroot minor. -/
theorem det_nonrootIncidence_eq_zero_of_not_isRootedForest [Fintype V]
    [Fintype A] [DecidableEq A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F)
    (hF : ¬J.IsRootedForest (R : Set V) F) :
    ((J.nonrootIncidence F R).submatrix a b).det = 0 := by
  by_contra hdet
  exact hF (J.isRootedForest_of_det_nonrootIncidence_ne_zero F R a b hdet)

/-- A copied cycle, witnessed by the actual erased-copy walk, makes a square minor vanish. -/
theorem det_nonrootIncidence_eq_zero_of_reaches_erase [Fintype V]
    [Fintype A] [DecidableEq A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F) (e : E) (he : e ∈ F)
    (hwalk : J.reaches (F.erase e) (J.left e) (J.right e)) :
    ((J.nonrootIncidence F R).submatrix a b).det = 0 :=
  J.det_nonrootIncidence_eq_zero_of_not_isRootedForest F R a b
    (fun hroot => hroot.1 e he hwalk)

/-- Two distinct supplied roots in one copied component give dependent nonroot columns. -/
theorem det_nonrootIncidence_eq_zero_of_connected_roots [Fintype V]
    [Fintype A] [DecidableEq A] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F) {x y : V}
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) (hwalk : J.reaches F x y) :
    ((J.nonrootIncidence F R).submatrix a b).det = 0 := by
  by_contra hdet
  exact hxy (J.eq_of_reaches_roots_of_linearIndependent_nonrootIncidence F R
    (J.linearIndependent_nonrootIncidence_of_det_ne_zero F R a b hdet) hx hy hwalk)

/-- Connected roots would put their nonzero coordinate difference in both disjoint spans. -/
theorem eq_of_reaches_roots_of_linearIndependent_augmentedIncidence
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (hli : LinearIndependent ℤ (J.augmentedIncidence F R).col)
    {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hwalk : J.reaches F x y) : x = y := by
  have hdj := (linearIndependent_sum.mp hli).2.2
  have hxspan : unitColumn x ∈
      Submodule.span ℤ (Set.range ((J.augmentedIncidence F R).col ∘ Sum.inr)) :=
    Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  have hyspan : unitColumn y ∈
      Submodule.span ℤ (Set.range ((J.augmentedIncidence F R).col ∘ Sum.inr)) :=
    Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
  have hz : unitColumn x - unitColumn y = 0 :=
    (Submodule.disjoint_def.mp hdj) _
      (J.unitColumn_sub_mem_span_of_reaches F hwalk) (Submodule.sub_mem _ hxspan hyspan)
  exact unitColumn_injective (sub_eq_zero.mp hz)

/-- A walk between distinct roots gives dependence of the copy and root-unit columns. -/
theorem not_linearIndependent_augmentedIncidence_of_connected_roots
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V) {x y : V}
    (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) (hwalk : J.reaches F x y) :
    ¬LinearIndependent ℤ (J.augmentedIncidence F R).col :=
  fun hli => hxy (J.eq_of_reaches_roots_of_linearIndependent_augmentedIncidence
    F R hli hx hy hwalk)

/-- Nonzero determinant of a literal square copy-plus-root-unit matrix forces exactly the
existing rooted-forest predicate, with no forest or coverage premise. -/
theorem isRootedForest_of_det_augmentedIncidence_ne_zero [Fintype V] [DecidableEq V]
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V) (e : V ≃ F ⊕ R)
    (hdet : ((J.augmentedIncidence F R).submatrix id e).det ≠ 0) :
    J.IsRootedForest (R : Set V) F := by
  have hli : LinearIndependent ℤ (J.augmentedIncidence F R).col :=
    (linearIndependent_equiv e).mp (Matrix.linearIndependent_cols_of_det_ne_zero hdet)
  refine ⟨J.isForest_of_linearIndependent_incidenceColumn F
    (linearIndependent_sum.mp hli).1, ?_⟩
  intro x
  have hcover : ∃ r ∈ R, J.reaches F x r := by
    by_contra h
    push Not at h
    apply hdet
    have hz := J.det_augmented_incidence_eq_zero_of_missing_root (K := ℤ) F R e x h
    convert hz using 1
    congr 1
    ext v j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, augmentedIncidence]
    cases e j with
    | inl f =>
      simp only [Sum.elim_inl]
      unfold incidenceColumn
      split_ifs <;> rfl
    | inr r =>
      simp only [Sum.elim_inr]
      unfold unitColumn
      split_ifs <;> rfl
  obtain ⟨r, hr, hxr⟩ := hcover
  refine ⟨r, hr, hxr, ?_⟩
  intro s hs hxs
  exact J.eq_of_reaches_roots_of_linearIndependent_augmentedIncidence F R hli hs hr
    ((J.reaches_symm hxs).trans hxr)

/-- Every nonrooted selection makes its square augmented original-copy matrix singular. -/
theorem det_augmentedIncidence_eq_zero_of_not_isRootedForest [Fintype V] [DecidableEq V]
    (J : CopiedGraph V E) (F : Finset E) (R : Finset V) (e : V ≃ F ⊕ R)
    (hF : ¬J.IsRootedForest (R : Set V) F) :
    ((J.augmentedIncidence F R).submatrix id e).det = 0 := by
  by_contra hdet
  exact hF (J.isRootedForest_of_det_augmentedIncidence_ne_zero F R e hdet)

/-- Integer vanishing transports through every integer cast, preserving the literal minor. -/
theorem det_map_nonrootIncidence_eq_zero_of_not_isRootedForest {K : Type*} [CommRing K]
    [Fintype V] [Fintype A] [DecidableEq A] (J : CopiedGraph V E)
    (F : Finset E) (R : Finset V) (a : A ≃ {v : V // v ∉ R}) (b : A ≃ F)
    (hF : ¬J.IsRootedForest (R : Set V) F) :
    (((J.nonrootIncidence F R).submatrix a b).map (fun z : ℤ => (z : K))).det = 0 := by
  rw [← Int.cast_det, J.det_nonrootIncidence_eq_zero_of_not_isRootedForest F R a b hF,
    Int.cast_zero]

/-- **Incidence determinant converse.** Integer vanishing also transports for the full augmented copy/root-unit square. -/
theorem det_map_augmentedIncidence_eq_zero_of_not_isRootedForest {K : Type*} [CommRing K]
    [Fintype V] [DecidableEq V] (J : CopiedGraph V E) (F : Finset E) (R : Finset V)
    (e : V ≃ F ⊕ R) (hF : ¬J.IsRootedForest (R : Set V) F) :
    (((J.augmentedIncidence F R).submatrix id e).map (fun z : ℤ => (z : K))).det = 0 := by
  rw [← Int.cast_det, J.det_augmentedIncidence_eq_zero_of_not_isRootedForest F R e hF,
    Int.cast_zero]

end
end LatticeProb.Graph.CopiedGraph
