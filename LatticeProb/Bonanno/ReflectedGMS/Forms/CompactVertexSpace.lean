/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompactVertexSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact evaluation closure of bounded vertex functions

This is the topological part of the countable regular-core construction. It uses
mathlib's product topology and closure, with vertex indicators as extra coordinates.
It does not assert form-norm density, regularity of the full form, or a Hunt realization.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace ReflectedGMS.CompactVertexSpace

variable {V I : Type*}

/-- A compact product with one indicator coordinate per vertex and bounded features. -/
abbrev Ambient (V : Type*) {I : Type*} (bound : I → ℝ) :=
  (V → Icc (0 : ℝ) 1) × (∀ i, Icc (-bound i) (bound i))

variable (feature : I → V → ℝ) (bound : I → ℝ)
  (hbound : ∀ i x, |feature i x| ≤ bound i)

/-- Joint evaluation of all vertex indicators and the supplied bounded functions. -/
noncomputable def evaluation (x : V) : Ambient V bound := by
  classical
  exact (fun y => ⟨if x = y then 1 else 0, by split_ifs <;> norm_num⟩,
    fun i => ⟨feature i x, abs_le.mp (hbound i x)⟩)

/-- The actual closed evaluation space, with its inherited topology. -/
def Space := closure (range (evaluation feature bound hbound))

instance : CompactSpace (Space feature bound hbound) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance : T2Space (Space feature bound hbound) := inferInstanceAs (T2Space {x // x ∈ _})

/-- Every vertex is a point of the compact evaluation closure. -/
noncomputable def vertex (x : V) : Space feature bound hbound :=
  ⟨evaluation feature bound hbound x, subset_closure (mem_range_self x)⟩

theorem vertex_injective : Function.Injective (vertex feature bound hbound) := by
  classical
  intro x y h
  have hxy := congrArg (fun z : Space feature bound hbound => (z.1.1 x : ℝ)) h
  by_contra hne
  simpa [vertex, evaluation, Ne.symm hne] using hxy

theorem closure_coordinate_dichotomy (x : V) (z : Space feature bound hbound) :
    z.1 = evaluation feature bound hbound x ∨ (z.1.1 x : ℝ) = 0 := by
  classical
  have hc : IsClosed ({evaluation feature bound hbound x} ∪
      {p : Ambient V bound | (p.1 x : ℝ) = 0}) :=
    isClosed_singleton.union (isClosed_eq
      (continuous_subtype_val.comp ((continuous_apply x).comp continuous_fst)) continuous_const)
  apply hc.closure_subset_iff.mpr ?_ z.2
  rintro _ ⟨y, rfl⟩
  by_cases hy : y = x
  · subst y; exact Or.inl rfl
  · exact Or.inr (by simp [evaluation, hy])

/-- Every supplied feature extends continuously to the evaluation closure. -/
noncomputable def coordinate (i : I) : C(Space feature bound hbound, ℝ) where
  toFun z := z.1.2 i
  continuous_toFun := continuous_subtype_val.comp ((continuous_apply i).comp
    (continuous_snd.comp continuous_subtype_val))

@[simp] theorem coordinate_vertex (i : I) (x : V) :
    coordinate feature bound hbound i (vertex feature bound hbound x) = feature i x := rfl

end ReflectedGMS.CompactVertexSpace
