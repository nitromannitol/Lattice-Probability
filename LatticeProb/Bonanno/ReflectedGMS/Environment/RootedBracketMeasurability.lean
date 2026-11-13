/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.RootedBracketMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicLawIngredients
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots

/-!
# Environment measurability of the rooted ordinary-edge bracket

`HarmonicLawIngredients.IntegrableBracket` and `meanCovariance` both read the
entry `e ↦ rootedGamma (decode e) (Φ.at e) 0 i j`.  Integrability of that map is
one of the conclusions of the reflected invariance principle, and the
measurability half of it was, until now, carried as an open input `hΓmeas` of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`.  This
module discharges it from the manuscript's own mass-transport hypothesis, and
from nothing else.

## Why measurability is not immediate

The vertex type `Vertex e.val` varies with the environment, so
`rootedGamma (decode e) (Φ.at e) 0` is not a composition of the measurable
coordinate maps of the code space in any direct way: the root vertex is selected
by a *geometric* test (which cell has the origin in its interior), and the
bracket then sums conductances over the neighbours of that vertex.

## The route

Everything is transported to the fixed label set `ℕ` of the code.

* `labelBracketDensity` is the bracket density written at a code label: the
  inverse area of the cell stored in slot `n`, times the series over *all*
  labels `m` of `c n m (Φ_m - Φ_n)_i (Φ_m - Φ_n)_j`.  Absent labels carry zero
  conductance by the `absent` clause of `Code.AdmissibleConductance`, so this
  agrees with `StatementIngredients.bracketDensity` of the decoded environment
  at every active label (`labelBracketDensity_eq_bracketDensity`).  Its
  measurability in `e` uses mathlib's `Measurable.tsum`, together with
  `Spatial.measurable_cellVolume` and `Spatial.measurable_slotCell`.
* `rootLabelSet n` is the event that slot `n` is present and its cell has the
  origin in its interior; it is measurable by `Spatial.measurableSet_cellInterior`
  and `Spatial.measurableSet_slotIsSome`.  The disjoint-interiors clause of
  `Geometry`, which holds for *every* `e : Env`, makes these events pairwise
  disjoint, so the sum over `n` of the corresponding indicators has at most one
  nonzero term.
* That sum, `rootedGammaRepr`, is therefore measurable, and it agrees with
  `rootedGamma (decode e) (Φ.at e) 0 i j` at every environment whose origin
  avoids the global boundary mask — which is almost every environment under mass
  transport, by the checked
  `Spatial.ae_notMem_boundaryMask_of_massTransport`.

The end product is `aestronglyMeasurable_rootedGamma`.  It is unconditional
given `MassTransport ν`, which is a hypothesis of the main theorem itself, not
an open obligation.
-/

set_option autoImplicit false

open MeasureTheory Set Function
open scoped ENNReal

namespace ReflectedGMS.RootedBracketMeasurability

open Code EnvironmentFields EnvironmentLaws RootDensities StatementIngredients Spatial

/-! ## Reading the code slots measurably -/

/-- The compact cell stored in code slot `n`.  An absent slot reads as the fixed
`Spatial.referenceCell`; it is never used, because every statement below is
guarded by presence of the slot. -/
noncomputable def slotCellAt (e : Env) (n : ℕ) : CompactCell :=
  (e.val.1 n).getD referenceCell

/-- At an active label the slot cell is the decoded cell. -/
theorem slotCellAt_eq_cell (e : Env) (v : Vertex e.val) :
    slotCellAt e v.val = (decode e).cell v := by
  have h : e.val.1 v.val = some ((decode e).cell v) :=
    (Option.some_get v.property).symm
  simp [slotCellAt, h]

theorem measurable_slot (n : ℕ) : Measurable fun e : Env => e.val.1 n :=
  (measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)

theorem measurable_conductance (n m : ℕ) : Measurable fun e : Env => e.val.2 n m :=
  (measurable_pi_apply m).comp
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_inclusion))

theorem measurable_slotCellAt (n : ℕ) : Measurable fun e : Env => slotCellAt e n :=
  measurable_slotCell.comp (measurable_slot n)

/-- Coordinate evaluation on the plane is continuous. -/
theorem continuous_planeCoord (i : Fin 2) : Continuous fun y : Plane => y i := by
  first
    | exact PiLp.continuous_apply _ _ i
    | fun_prop

/-! ## The bracket density at a code label -/

/-- The ordinary-edge bracket density read at a code label, as a function of the
environment.  The series runs over *all* labels; absent labels contribute
nothing because their conductance vanishes. -/
noncomputable def labelBracketDensity (Φ : CellField) (e : Env) (n : ℕ) (i j : Fin 2) : ℝ :=
  ((volume (slotCellAt e n : Set Plane)).toReal)⁻¹ *
    ∑' m : ℕ, e.val.2 n m * (Φ.value e m i - Φ.value e n i) *
      (Φ.value e m j - Φ.value e n j)

/-- The summand of `labelBracketDensity` is supported on active labels. -/
theorem support_labelBracketSummand (Φ : CellField) (e : Env) (n : ℕ) (i j : Fin 2) :
    Function.support (fun m : ℕ => e.val.2 n m * (Φ.value e m i - Φ.value e n i) *
        (Φ.value e m j - Φ.value e n j))
      ⊆ {m : ℕ | (e.val.1 m).isSome} := by
  intro m hm
  by_contra hmem
  have hnone : e.val.1 m = none := by
    rw [← Option.not_isSome_iff_eq_none]
    exact hmem
  have hc : e.val.2 n m = 0 := e.property.choose.absent n m (Or.inr hnone)
  exact hm (by simp [hc])

/-- **The label form is the decoded form.**  At an active label,
`labelBracketDensity` is `StatementIngredients.bracketDensity` of the decoded
environment. -/
theorem labelBracketDensity_eq_bracketDensity (Φ : CellField) (e : Env)
    (v : Vertex e.val) (i j : Fin 2) :
    labelBracketDensity Φ e v.val i j = bracketDensity (decode e) (Φ.at e) v i j := by
  have htsum := tsum_subtype_eq_of_support_subset
    (support_labelBracketSummand Φ e v.val i j)
  calc labelBracketDensity Φ e v.val i j
      = ((volume ((decode e).cell v : Set Plane)).toReal)⁻¹ *
          ∑' m : ℕ, e.val.2 v.val m * (Φ.value e m i - Φ.value e v.val i) *
            (Φ.value e m j - Φ.value e v.val j) := by
        rw [labelBracketDensity, slotCellAt_eq_cell]
    _ = ((volume ((decode e).cell v : Set Plane)).toReal)⁻¹ *
          ∑' w : Vertex e.val, (decode e).graph.c v w *
            (Φ.at e w i - Φ.at e v i) * (Φ.at e w j - Φ.at e v j) := by
        refine congrArg
          (fun t : ℝ => ((volume ((decode e).cell v : Set Plane)).toReal)⁻¹ * t) ?_
        exact htsum.symm
    _ = bracketDensity (decode e) (Φ.at e) v i j := rfl

theorem measurable_labelBracketDensity (Φ : CellField) (n : ℕ) (i j : Fin 2) :
    Measurable fun e : Env => labelBracketDensity Φ e n i j := by
  have harea : Measurable fun e : Env =>
      ((volume (slotCellAt e n : Set Plane)).toReal)⁻¹ :=
    ((measurable_cellVolume.comp (measurable_slotCellAt n)).ennreal_toReal).inv
  have hval : ∀ (m : ℕ) (k : Fin 2), Measurable fun e : Env => Φ.value e m k :=
    fun m k => (continuous_planeCoord k).measurable.comp (Φ.measurable_label m)
  have hterm : ∀ m : ℕ, Measurable fun e : Env =>
      e.val.2 n m * (Φ.value e m i - Φ.value e n i) * (Φ.value e m j - Φ.value e n j) :=
    fun m => ((measurable_conductance n m).mul ((hval m i).sub (hval n i))).mul
      ((hval m j).sub (hval n j))
  exact harea.mul (Measurable.tsum hterm)

/-! ## The root label -/

/-- The event that code slot `n` is present and its cell has the origin in its
interior.  Off the global boundary mask this identifies the rooted vertex. -/
def rootLabelSet (n : ℕ) : Set Env :=
  {e : Env | (e.val.1 n).isSome ∧ (0 : Plane) ∈ interior (slotCellAt e n : Set Plane)}

theorem measurableSet_rootLabelSet (n : ℕ) : MeasurableSet (rootLabelSet n) := by
  have h1 : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
    (measurable_slot n) measurableSet_slotIsSome
  have h2 : MeasurableSet
      {e : Env | (0 : Plane) ∈ interior (slotCellAt e n : Set Plane)} :=
    ((measurable_slotCellAt n).prodMk measurable_const) measurableSet_cellInterior
  exact h1.inter h2

theorem mem_rootLabelSet_of_rootAt (e : Env) {v : Vertex e.val}
    (hv : rootAt (decode e) 0 = some v) : e ∈ rootLabelSet v.val := by
  have hint : IsInteriorRoot (decode e) 0 v :=
    ((rootAt_eq_some_iff (decode e) (decode_geometry e) 0 v).mp hv).2
  refine ⟨v.property, ?_⟩
  rw [slotCellAt_eq_cell]
  exact hint

/-- **Uniqueness of the root label.**  Cell interiors are pairwise disjoint in
every valid environment, so at most one code label can have the origin in its
cell interior. -/
theorem rootLabel_unique (e : Env) {v : Vertex e.val} {n : ℕ}
    (hv : (0 : Plane) ∈ interior ((decode e).cell v : Set Plane))
    (hn : e ∈ rootLabelSet n) : n = v.val := by
  by_contra hne
  have hwint : (0 : Plane) ∈ interior ((decode e).cell ⟨n, hn.1⟩ : Set Plane) := by
    have h := hn.2
    rwa [slotCellAt_eq_cell e ⟨n, hn.1⟩] at h
  have hwv : (⟨n, hn.1⟩ : Vertex e.val) ≠ v := fun h => hne (congrArg Subtype.val h)
  exact Set.disjoint_left.mp ((decode_geometry e).2.2.2.1 hwv) hwint hv

/-! ## The measurable representative -/

/-- A measurable representative of the rooted bracket entry: the sum over code
labels of the label bracket density on the event that the label is the root.
At most one term is nonzero. -/
noncomputable def rootedGammaRepr (Φ : CellField) (i j : Fin 2) (e : Env) : ℝ :=
  ∑' n : ℕ, (rootLabelSet n).indicator
    (fun e' : Env => labelBracketDensity Φ e' n i j) e

theorem measurable_rootedGammaRepr (Φ : CellField) (i j : Fin 2) :
    Measurable (rootedGammaRepr Φ i j) :=
  Measurable.tsum fun n =>
    (measurable_labelBracketDensity Φ n i j).indicator (measurableSet_rootLabelSet n)

/-- Off the global boundary mask the representative is the rooted bracket. -/
theorem rootedGammaRepr_eq (Φ : CellField) (i j : Fin 2) (e : Env)
    (he : (0 : Plane) ∉ boundaryMask (decode e)) :
    rootedGammaRepr Φ i j e = rootedGamma (decode e) (Φ.at e) 0 i j := by
  obtain ⟨v, hv, hint⟩ :=
    rootAt_eq_some_of_not_mem_boundaryMask (decode e) (decode_geometry e) he
  have hsingle : ∀ n : ℕ, n ≠ v.val →
      (rootLabelSet n).indicator (fun e' : Env => labelBracketDensity Φ e' n i j) e = 0 := by
    intro n hn
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hn (rootLabel_unique e hint hmem)
  rw [rootedGammaRepr, tsum_eq_single v.val hsingle,
    Set.indicator_of_mem (mem_rootLabelSet_of_rootAt e hv),
    labelBracketDensity_eq_bracketDensity]
  simp [rootedGamma, hv]

/-- **Entrywise environment measurability of the rooted ordinary-edge bracket.**
This is exactly the input `hΓmeas` of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`, discharged
from the manuscript's own mass-transport hypothesis. -/
theorem aestronglyMeasurable_rootedGamma (ν : Measure Env) (hmt : MassTransport ν)
    (Φ : CellField) (i j : Fin 2) :
    AEStronglyMeasurable (fun e : Env => rootedGamma (decode e) (Φ.at e) 0 i j) ν := by
  refine ⟨rootedGammaRepr Φ i j, (measurable_rootedGammaRepr Φ i j).stronglyMeasurable, ?_⟩
  filter_upwards [ae_notMem_boundaryMask_of_massTransport ν hmt] with e he
  exact (rootedGammaRepr_eq Φ i j e he).symm

end ReflectedGMS.RootedBracketMeasurability
