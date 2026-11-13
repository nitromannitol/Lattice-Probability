/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.EndLabelConstruction at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds

/-!
# Constructing end labels from local finite-cut stabilization

At a nonvertex time, suppose that for every finite vertex cut all nearby vertex
values eventually lie in one component of the complement.  Dense vertex times
make that component unique.  The choices for nested cuts are then automatically
compatible, hence form a mathlib graph end.  This gives the unique end-labelled
lift of the original `Option`-valued path.

The reflected-walk API supplies dense vertex times almost surely (see
`SpatialInfinityAvoidance.dense_vertices_ae_of_isReflectedWalk`).  Its present
right-continuity axioms only exclude individual fixed vertices near a nonvertex
time; deriving the common-component finite-cut premise below remains a separate
process-law obligation.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal

universe u

namespace ReflectedGMS.EndLabelConstruction

open SpatialEnds

variable {V : Type u}

/-- Near `t`, every vertex value of `X` eventually lies in the component `C`
outside the finite cut `K`. -/
def EventuallyInComponent (F : IndexedCells V) (X : ℝ≥0 → Option V) (t : ℝ≥0)
    (K : Finset V) (C : F.graph.toSimpleGraph.ComponentCompl K) : Prop :=
  ∀ᶠ s in 𝓝 t, ∀ v, X s = some v → v ∈ C

/-- The sole pathwise existence premise: at each nonvertex time and each finite
cut, the nearby vertex values stabilize in some complement component. -/
def HasFiniteCutStabilization (F : IndexedCells V) (X : ℝ≥0 → Option V) : Prop :=
  ∀ t, X t = none → ∀ K : Finset V,
    ∃ C : F.graph.toSimpleGraph.ComponentCompl K, EventuallyInComponent F X t K C

/-- Dense vertex times make an eventual component at a fixed finite cut unique. -/
theorem eventuallyInComponent_unique (F : IndexedCells V) (X : ℝ≥0 → Option V)
    (hdense : Dense {s | ∃ v, X s = some v}) {t : ℝ≥0} {K : Finset V}
    {C D : F.graph.toSimpleGraph.ComponentCompl K}
    (hC : EventuallyInComponent F X t K C)
    (hD : EventuallyInComponent F X t K D) : C = D := by
  have hboth : {s | (∀ v, X s = some v → v ∈ C) ∧
      ∀ v, X s = some v → v ∈ D} ∈ 𝓝 t := by
    filter_upwards [hC, hD] with s hsC hsD
    exact ⟨hsC, hsD⟩
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hboth
  obtain ⟨s, ⟨v, hv⟩, hsU⟩ := hdense.exists_mem_open hUopen ⟨t, htU⟩
  have hs := hUsub hsU
  exact (hs.1 v hv).choose_spec.symm.trans (hs.2 v hv).choose_spec

section Construction

variable (F : IndexedCells V) (X : ℝ≥0 → Option V)
  (hstab : HasFiniteCutStabilization F X)

/-- The unique eventual component selected by a nonvertex time and a finite cut. -/
noncomputable def chosenComponent (t : ℝ≥0) (ht : X t = none) (K : Finset V) :
    F.graph.toSimpleGraph.ComponentCompl K :=
  Classical.choose (hstab t ht K)

theorem chosenComponent_spec (t : ℝ≥0) (ht : X t = none) (K : Finset V) :
    EventuallyInComponent F X t K (chosenComponent F X hstab t ht K) :=
  Classical.choose_spec (hstab t ht K)

/-- Component choices at nested finite cuts are compatible.  This is derived
from density rather than included in the stabilization premise. -/
theorem chosenComponent_hom (hdense : Dense {s | ∃ v, X s = some v})
    (t : ℝ≥0) (ht : X t = none) {K L : Finset V} (hKL : K ⊆ L) :
    (chosenComponent F X hstab t ht L).hom hKL = chosenComponent F X hstab t ht K := by
  apply eventuallyInComponent_unique F X hdense
  · filter_upwards [chosenComponent_spec F X hstab t ht L] with s hs
    intro v hv
    exact SimpleGraph.ComponentCompl.subset_hom _ hKL (hs v hv)
  · exact chosenComponent_spec F X hstab t ht K

/-- The mathlib graph end approached at a nonvertex time. -/
noncomputable def endAt (hdense : Dense {s | ∃ v, X s = some v})
    (t : ℝ≥0) (ht : X t = none) : GraphEnd F :=
  ⟨fun K => chosenComponent F X hstab t ht K.unop, by
    intro K L f
    change (chosenComponent F X hstab t ht K.unop).hom
        (CategoryTheory.le_of_op_hom f) = chosenComponent F X hstab t ht L.unop
    exact chosenComponent_hom F X hstab hdense t ht (CategoryTheory.le_of_op_hom f)⟩

theorem endAt_eventually (hdense : Dense {s | ∃ v, X s = some v})
    (t : ℝ≥0) (ht : X t = none) (K : Finset V) :
    ∀ᶠ s in 𝓝 t, ∀ v, X s = some v → v ∈ endComponent F (endAt F X hstab hdense t ht) K :=
  chosenComponent_spec F X hstab t ht K

/-- Keep vertex values and replace each nonvertex value by its forced graph end. -/
noncomputable def endLabelLift (hdense : Dense {s | ∃ v, X s = some v}) :
    ℝ≥0 → State F := fun t =>
  match ht : X t with
  | some v => Sum.inl v
  | none => Sum.inr (endAt F X hstab hdense t ht)

theorem collapse_endLabelLift (hdense : Dense {s | ∃ v, X s = some v}) (t : ℝ≥0) :
    collapse (endLabelLift F X hstab hdense t) = X t := by
  rw [endLabelLift]
  split <;> simp_all [collapse]

theorem endLabelLift_of_none (hdense : Dense {s | ∃ v, X s = some v})
    (t : ℝ≥0) (ht : X t = none) :
    endLabelLift F X hstab hdense t = Sum.inr (endAt F X hstab hdense t ht) := by
  rw [endLabelLift]
  split
  · simp_all
  · rfl

theorem endLabelLift_isEndLabeling (hdense : Dense {s | ∃ v, X s = some v}) :
    IsEndLabeling F (endLabelLift F X hstab hdense) := by
  intro t e hte K
  rw [endLabelLift] at hte
  split at hte
  · contradiction
  · rename_i ht
    have he : e = endAt F X hstab hdense t ht := Sum.inr.inj hte.symm
    subst e
    filter_upwards [endAt_eventually F X hstab hdense t ht K] with s hs
    intro v hsv
    apply hs v
    rw [← collapse_endLabelLift F X hstab hdense s, hsv]
    rfl

end Construction

theorem collapse_eq_some_iff {F : IndexedCells V} {x : State F} {v : V} :
    collapse x = some v ↔ x = Sum.inl v := by
  cases x with
  | inl w => simp [collapse]
  | inr e => simp [collapse]

/-- Any correctly labelled lift with the prescribed collapse equals the
constructed lift. -/
theorem endLabelLift_unique (F : IndexedCells V) (X : ℝ≥0 → Option V)
    (hdense : Dense {s | ∃ v, X s = some v})
    (hstab : HasFiniteCutStabilization F X) (Y : ℝ≥0 → State F)
    (hcollapse : ∀ t, collapse (Y t) = X t) (hlabel : IsEndLabeling F Y) :
    Y = endLabelLift F X hstab hdense := by
  funext t
  cases hXt : X t with
  | some v =>
      have hY : Y t = Sum.inl v := collapse_eq_some_iff.mp ((hcollapse t).trans hXt)
      have hLift : endLabelLift F X hstab hdense t = Sum.inl v :=
        collapse_eq_some_iff.mp ((collapse_endLabelLift F X hstab hdense t).trans hXt)
      exact hY.trans hLift.symm
  | none =>
      cases hYt : Y t with
      | inl v =>
          have : some v = none := by simpa [collapse, hYt] using (hcollapse t).trans hXt
          contradiction
      | inr e =>
          rw [endLabelLift_of_none F X hstab hdense t hXt]
          apply congrArg Sum.inr
          apply Subtype.ext
          funext Kop
          apply eventuallyInComponent_unique F X hdense
          · filter_upwards [hlabel t e hYt Kop.unop] with s hs
            intro v hv
            apply hs v
            apply collapse_eq_some_iff.mp
            exact (hcollapse s).trans hv
          · exact endAt_eventually F X hstab hdense t hXt Kop.unop

/-- Existence and uniqueness of the simultaneous end-labelled lift. -/
theorem existsUnique_endLabelLift (F : IndexedCells V) (X : ℝ≥0 → Option V)
    (hdense : Dense {s | ∃ v, X s = some v})
    (hstab : HasFiniteCutStabilization F X) :
    ∃! Y : ℝ≥0 → State F,
      (∀ t, collapse (Y t) = X t) ∧ IsEndLabeling F Y := by
  refine ⟨endLabelLift F X hstab hdense, ⟨collapse_endLabelLift F X hstab hdense,
    endLabelLift_isEndLabeling F X hstab hdense⟩, ?_⟩
  intro Y hY
  exact endLabelLift_unique F X hdense hstab Y hY.1 hY.2

end ReflectedGMS.EndLabelConstruction
