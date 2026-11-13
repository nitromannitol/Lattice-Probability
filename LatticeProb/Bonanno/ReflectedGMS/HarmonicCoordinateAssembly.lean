/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.HarmonicCoordinateAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.UnmarkedCoordinateDescent
import LatticeProb.Bonanno.ReflectedGMS.HarmonicMainStatement
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureSpatialDiameterBounds
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActualUniformSublinearity
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.NestedProjectionProducers
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BaseSpecificEnergy
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualSpatialDensityBridge
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicCylinderLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLawUniqueness
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyPolarization

/-!
# Assembly of the harmonic-coordinate main theorem: a checked reduction

This module reduces the full harmonic-coordinate target
`HarmonicMainStatement.HarmonicCoordinateMainTheorem` — the conclusion
`HarmonicCoordinateConclusions (validLaw P hP)`, i.e. the existence of one measurable
unmarked `CellField` satisfying the seven clauses of `IsHarmonicCoordinate` — to a list of
**named, atomic open inputs**.  Every clause that the project's checked modules can already
discharge is discharged here; nothing below asserts that the main theorem is proved, and a
conditional reduction never certifies its inputs.

## The construction

The coordinate field is **not** an input.  It is built from the concrete block interpolants
`DyadicApproximation.phi` of the main statement, along a deterministic subsequence `ms`:

* `differenceApproximant ms j ω (Nat.pair a b) = φ_{ms j}(H_b) − φ_{ms j}(H_a)` is the marked
  *difference* approximant on paired labels (zero unless the environment lies in the good
  event `SublinearEvent` of sublinear diameter decay — where block interpolants are unique,
  so `phi` is canonical — and both labels are active);
* `markedDifferenceField ms` is its limit on the good set `LimitGood` where every paired label
  converges (`Corrector/MarkedLimitingCoordinateMeasurability`), and the zero field elsewhere;
* `unmarkedDifferenceField ms` is its descent to the environment alone through the grid
  average of the arctangent code (`Corrector/UnmarkedCoordinateDescent`, the measurability
  half of `s:prop:gridindependence`);
* `harmonicCellField ms hmeas` integrates the unmarked difference field from a canonical
  base label: the root cell when the origin is unmasked, and the least active label whose
  cell contains the origin otherwise.

Descending the *difference* field rather than the potential is what makes the covariance
clauses hold **exactly and everywhere**: the label transport `pairTransport` of a similarity is
linear and independent of the auxiliary grid, so `GridTransfer` holds in both directions and
`descentField_covariant` applies; a potential-level transport would depend on the grid at
masked roots.  Gradient covariance then needs only the cocycle identity of a difference field,
and normalized covariance uses that the base label of the translated environment is the
relabeled root (`ActualSpatialDensityBridge.rootAt_similarity`).

## What is discharged and what is open

Discharged from checked producers (see the clause table in the docstring of
`harmonicCoordinateConclusions_of_named_inputs`): the vacuity guard (6) by
`DyadicCylinderLaw.uniformGridLaw_gridMeasure`; the reduction of "every uniform grid law" in
(7) to the constructed one by `DyadicGridLawUniqueness.eq_of_uniformGridLaw`; the boundary
mask clause of (5) by `Spatial.ae_notMem_boundaryMask_of_massTransport`; the full measure of
the good event by `Spatial.ae_maxDiamHittingBall_finite_and_sublinear` and its similarity
invariance by `sublinearDiameterDecay_of_similarity`; root normalization, everywhere, from
the construction; both covariance clauses (1)(2), everywhere, from the covariance of the
interpolants on the good event;
measurability (3) and finiteness (4) of the unmarked specific energy, the latter through the
quadratic bound of `Corrector/SpecificEnergyPolarization` applied to the concrete
approximants; the block-interpolant clause of (7) — including uniqueness of block
interpolants, proved here from `existsUnique_vector_trace_minimizer` — from the spatial
maximal bound; and the representative-independent half of the sublinearity clause from its
centroid half and `s:eq:DR`.

The spatial maximal bound itself is **no longer an input**: `s:prop:maximal` for the rooted
(FE) density is discharged from the manuscript's own `s:eq:MTP` and finite (FE) moment by
`Spatial/SpatialMaximalForFiniteEnergy` (see `spatialMaximalBound_of_massTransport`), so the
three final statements carry ten open inputs rather than eleven.

Open inputs are stated as named `def`s with the audited gap they belong to.  The inputs
`Marked*` are still stated at the level of the marked limit; they are the honest residue of
this milestone and are to be pushed down to the summable-patch-energy, block-exhaustion and
specific-energy-projection inputs of `Corrector/LimitingHarmonicPotential`,
`Corrector/LimitingPotentialFreeOrthogonality` and `Corrector/SpecificEnergyLocalControl`.

**This file proves no main theorem.**  Its final statements are implications whose
hypotheses are open; a conditional reduction certifies neither its inputs nor
`HarmonicCoordinateMainTheorem`.
-/

-- Merged from `ReflectedGMS/Corrector/MarkedLimitingCoordinateMeasurability.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_MarkedLimitingCoordinateMeasurability

/-!
# The measurable marked limiting harmonic coordinate

`Corrector/MeasurableInfinitePatchMinimizer.lean` produces, for each approximation stage, a
field of anchored energy minimizers whose value at every label is a **measurable** function
of the environment. `Corrector/LimitingHarmonicPotential.lean` produces, at a **fixed**
environment, an anchored pointwise limit of such approximants along graph paths, one real
coordinate at a time. Neither says anything about the limit as a function of the
environment: the pathwise producer constructs its limit by `limUnder` after an existence
argument that is run separately at every environment, so nothing in it is measurable, and
the manuscript's marked limit `Φ` has to be a single measurable object.

This file supplies exactly that missing joint step, for the marked environment space
`HarmonicMainStatement.MarkedEnvironment = Env × Grid` used by the main statement.

* `ConvergesAt A n` is the event that the approximants converge at the canonical cell label
  `n`; it is measurable (`measurableSet_convergesAt`) because `Plane` is Polish, via
  `MeasureTheory.measurableSet_exists_tendsto`.
* `LimitGood A` is the good set on which *every* label converges — the countable
  intersection of the previous events, hence measurable.
* `limitValue A` is the limit itself, with the **canonical zero fallback** off the
  convergence event of each label. It is jointly measurable into the countable label
  product (`measurable_limitValue`), it is the pointwise limit at every label of every
  environment at which that limit exists (`tendsto_limitValue`), and it is the *unique*
  field with those two properties (`eq_limitValue`).
* Because the limit is characterised by pointwise convergence and uniqueness of limits,
  **exact** covariance passes from the approximants to the limit with no extra hypothesis:
  `limitValue_normalizedCovariant` is the `NormalizedCovariant` shape
  `Φ(e')(relabel v) = s • (Φ(e) v − Φ(e) r)` and `limitValue_gradientCovariant` is the
  `GradientCovariant` shape, both of which the main statement demands. The good set is
  invariant under such a relation (`mem_limitGood_of_covariant`), so the covariance is not
  asserted on a set that the fallback could destroy.
* `convergesAt_of_coordinates` converts the *real* coordinatewise convergence supplied by
  the pathwise producer into the `Plane`-valued convergence event used here.
* `exists_measurable_marked_limiting_coordinate` is the packaged statement, and
  `cellFieldAtGrid` records how a marked field of this shape yields the
  `EnvironmentFields.CellField` demanded by `HarmonicCoordinateMainTheorem`.

## Scope

Nothing here proves that the concrete `DyadicApproximation.phi` approximants are measurable,
that they converge, or that the limit does not depend on the auxiliary dyadic grid. Those
are the separate producers (measurable block interpolation, the summable-gradient input of
`s:prop:limit`, and the unmarking by independent copies). This file is the joint
measurability/covariance step between them, and it assumes no covariance of the limit: only
covariance of the given approximants, from which covariance of the limit is *derived*.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace MarkedLimitingCoordinateMeasurability

open Filter Topology MeasureTheory
open Code EnvironmentFields DyadicApproximation HarmonicMainStatement

/-! ### The convergence events and the limit with canonical zero fallback -/

section Core

variable {Ω : Type*}

/-- **The convergence event at one canonical cell label.** -/
def ConvergesAt (A : ℕ → Ω → ℕ → Plane) (n : ℕ) : Set Ω :=
  {ω | ∃ c : Plane, Tendsto (fun m => A m ω n) atTop (𝓝 c)}

/-- **The good set of the marked limit**: the approximants converge at every label. -/
def LimitGood (A : ℕ → Ω → ℕ → Plane) : Set Ω :=
  ⋂ n : ℕ, ConvergesAt A n

theorem mem_convergesAt_of_mem_limitGood {A : ℕ → Ω → ℕ → Plane} {ω : Ω}
    (hω : ω ∈ LimitGood A) (n : ℕ) : ω ∈ ConvergesAt A n :=
  Set.mem_iInter.1 hω n

theorem mem_limitGood_iff {A : ℕ → Ω → ℕ → Plane} {ω : Ω} :
    ω ∈ LimitGood A ↔ ∀ n : ℕ, ω ∈ ConvergesAt A n :=
  Set.mem_iInter

/-- **The marked limiting coordinate.** At a label at which the approximants converge it is
their limit; at every other label it is the canonical value zero. -/
noncomputable def limitValue (A : ℕ → Ω → ℕ → Plane) (ω : Ω) (n : ℕ) : Plane :=
  (ConvergesAt A n).indicator (fun ω' => limUnder atTop fun m => A m ω' n) ω

/-- **The defining property**: the limit value is the limit wherever the limit exists. -/
theorem limitValue_eq_of_tendsto {A : ℕ → Ω → ℕ → Plane} {ω : Ω} {n : ℕ} {c : Plane}
    (hc : Tendsto (fun m => A m ω n) atTop (𝓝 c)) : limitValue A ω n = c := by
  have hmem : ω ∈ ConvergesAt A n := ⟨c, hc⟩
  rw [limitValue, Set.indicator_of_mem hmem, hc.limUnder_eq]

theorem tendsto_limitValue {A : ℕ → Ω → ℕ → Plane} {ω : Ω} {n : ℕ}
    (hω : ω ∈ ConvergesAt A n) :
    Tendsto (fun m => A m ω n) atTop (𝓝 (limitValue A ω n)) := by
  obtain ⟨c, hc⟩ := hω
  rw [limitValue_eq_of_tendsto hc]
  exact hc

/-- **The canonical zero fallback.** -/
theorem limitValue_of_notMem {A : ℕ → Ω → ℕ → Plane} {ω : Ω} {n : ℕ}
    (hω : ω ∉ ConvergesAt A n) : limitValue A ω n = 0 :=
  Set.indicator_of_notMem hω _

/-- Labels at which every approximant vanishes — in particular absent canonical labels, by
the shared coding convention — keep the value zero in the limit. -/
theorem limitValue_eq_zero_of_approximants_zero {A : ℕ → Ω → ℕ → Plane} {ω : Ω} {n : ℕ}
    (h : ∀ m : ℕ, A m ω n = 0) : limitValue A ω n = 0 := by
  refine limitValue_eq_of_tendsto ?_
  simp only [h]
  exact tendsto_const_nhds

end Core

/-! ### Measurability -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {A : ℕ → Ω → ℕ → Plane}

/-- **The convergence event at a label is measurable.** `Plane` is Polish, so this is the
standard Borel convergence set of a sequence of measurable functions. -/
theorem measurableSet_convergesAt (hA : ∀ (m n : ℕ), Measurable fun ω => A m ω n) (n : ℕ) :
    MeasurableSet (ConvergesAt A n) :=
  measurableSet_exists_tendsto (fun m => hA m n)

/-- **The good set is measurable**, being a countable intersection of label events. -/
theorem measurableSet_limitGood (hA : ∀ (m n : ℕ), Measurable fun ω => A m ω n) :
    MeasurableSet (LimitGood A) :=
  MeasurableSet.iInter fun n => measurableSet_convergesAt hA n

theorem measurable_limUnder_label (hA : ∀ (m n : ℕ), Measurable fun ω => A m ω n) (n : ℕ) :
    Measurable fun ω => limUnder atTop fun m => A m ω n :=
  (MeasureTheory.StronglyMeasurable.limUnder
    (fun m => (hA m n).stronglyMeasurable)).measurable

/-- **The marked limit is measurable at every label.** -/
theorem measurable_limitValue_label (hA : ∀ (m n : ℕ), Measurable fun ω => A m ω n) (n : ℕ) :
    Measurable fun ω => limitValue A ω n :=
  (measurable_limUnder_label hA n).indicator (measurableSet_convergesAt hA n)

/-- **Joint measurability of the marked limit** into the countable label product, which is
the form the `CellField` interface of the main statement requires. -/
theorem measurable_limitValue (hA : ∀ (m n : ℕ), Measurable fun ω => A m ω n) :
    Measurable (limitValue A) :=
  Measurable.of_eval fun n => measurable_limitValue_label hA n

end Measurability

/-! ### Exact covariance passes to the limit -/

section Covariance

variable {Ω : Type*} {A : ℕ → Ω → ℕ → Plane}

end Covariance

/-! ### From real coordinatewise convergence to the plane-valued event -/

section Coordinates

variable {Ω : Type*}

end Coordinates

/-! ### The packaged marked limiting coordinate -/

section Marked

end Marked

end MarkedLimitingCoordinateMeasurability

end ReflectedGMS

end Merged_MarkedLimitingCoordinateMeasurability

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace ReflectedGMS.HarmonicCoordinateAssembly

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open MarkedLimitingCoordinateMeasurability UnmarkedCoordinateDescent
open NonmacroscopicSelectedBlocks Spatial PatchCentroidTraceFiniteEnergy

/-! ### The uniform grid law: clause (6) and the collapse of the `∀ σ` quantifier -/

/-- The uniform dyadic grid law constructed in `Forms/DyadicGridLaw` and identified as the
manuscript's uniform marking in `Forms/DyadicCylinderLaw`. -/
noncomputable abbrev gridLaw : Measure Grid := DyadicGridLaw.gridMeasure

instance gridLaw_isProbabilityMeasure : IsProbabilityMeasure gridLaw :=
  DyadicGridLaw.isProbabilityMeasure_gridMeasure

theorem uniformGridLaw_gridLaw : UniformGridLaw gridLaw :=
  DyadicCylinderLaw.uniformGridLaw_gridMeasure

/-- **Clause (6) of `IsHarmonicCoordinate` is inhabited**: the main theorem is not vacuous. -/
theorem exists_uniformGridLaw : ∃ σ : Measure Grid, UniformGridLaw σ :=
  ⟨gridLaw, uniformGridLaw_gridLaw⟩

/-- Every uniform grid law is the constructed one, so clause (7) need only be proved for
`gridLaw`. -/
theorem eq_gridLaw_of_uniformGridLaw {σ : Measure Grid} (h : UniformGridLaw σ) : σ = gridLaw :=
  DyadicGridLawUniqueness.eq_of_uniformGridLaw h uniformGridLaw_gridLaw

/-! ### Transfer of almost-sure statements between the environment law and the marked law -/

/-- A property of the environment alone holds for the marked law once it holds for the
environment law. -/
theorem ae_marked_of_ae_env (ν : Measure Env) [SFinite ν] {p : Env → Prop}
    (h : ∀ᵐ e ∂ν, p e) : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, p ω.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := gridLaw)).tendsto_ae.eventually h

/-- A property of the environment alone that holds for the marked law holds for the
environment law: the grid law is a probability measure, so the grid-conditional statement is
not vacuous. -/
theorem ae_env_of_ae_marked (ν : Measure Env) [SFinite ν] {p : Env → Prop}
    (h : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, p ω.1) : ∀ᵐ e ∂ν, p e := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with e he
  obtain ⟨_, hD⟩ := he.exists
  exact hD

/-! ### The canonical base label -/

/-- Reading a code slot: an active cell of the decoded environment is the cell stored in its
slot. -/
theorem decode_cell_eq_getD (e : Env) (v : Vertex e.val) :
    (decode e).cell v = (e.val.1 v.val).getD Spatial.referenceCell := by
  obtain ⟨n, hn⟩ := v
  show (e.val.1 n).get hn = (e.val.1 n).getD Spatial.referenceCell
  revert hn
  cases e.val.1 n with
  | none => intro hn; exact absurd hn (by simp)
  | some K => intro _; rfl

/-- The base-label predicate: an active label whose cell contains the origin. -/
def IsBaseLabel (e : Env) (n : ℕ) : Prop :=
  (e.val.1 n).isSome ∧
    (0 : Plane) ∈ (((e.val.1 n).getD Spatial.referenceCell : CompactCell) : Set Plane)

/-- Every coded environment has an active label: its cell graph is connected, hence its
vertex type is nonempty. -/
theorem exists_isSome_slot (e : Env) : ∃ n : ℕ, (e.val.1 n).isSome := by
  obtain ⟨v⟩ := (Geometry.graph_connected (decode_geometry e)).nonempty
  exact ⟨v.val, v.property⟩

/-- The totalised base-label predicate: an active label whose cell contains the origin, or,
when no cell contains the origin, any active label.

The second branch is new.  The covering clause of `Geometry` only asks that the uncovered
set be `H¹`-null, so the origin itself need not lie in any cell, and the plain predicate
`IsBaseLabel` can be unsatisfiable.  Totalising it here keeps `baseLabel` total, which is
what all its consumers need; the consumers that actually use the origin do so through
`baseLabel_eq_of_rootAt`, whose hypothesis puts the origin in a cell interior and hence
selects the first branch. -/
def IsBaseLabelOrLeast (e : Env) (n : ℕ) : Prop :=
  IsBaseLabel e n ∨ ((¬ ∃ m : ℕ, IsBaseLabel e m) ∧ (e.val.1 n).isSome)

theorem exists_isBaseLabelOrLeast (e : Env) : ∃ n : ℕ, IsBaseLabelOrLeast e n := by
  by_cases h : ∃ m : ℕ, IsBaseLabel e m
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, Or.inl hm⟩
  · obtain ⟨n, hn⟩ := exists_isSome_slot e
    exact ⟨n, Or.inr ⟨h, hn⟩⟩

/-- **The canonical base label**: the least active label whose cell contains the origin, or
the least active label if none does.  Off the boundary mask it is the label of the root cell
`H₀` (`baseLabel_eq_of_rootAt`). -/
noncomputable def baseLabel (e : Env) : ℕ := Nat.find (exists_isBaseLabelOrLeast e)

theorem isBaseLabelOrLeast_baseLabel (e : Env) : IsBaseLabelOrLeast e (baseLabel e) :=
  Nat.find_spec (exists_isBaseLabelOrLeast e)

/-- The base label is always active. -/
theorem isSome_baseLabel (e : Env) : (e.val.1 (baseLabel e)).isSome := by
  rcases isBaseLabelOrLeast_baseLabel e with h | h
  · exact h.1
  · exact h.2

/-- When some cell does contain the origin, the base label is the least label of such a
cell. -/
theorem isBaseLabel_baseLabel (e : Env) (h : ∃ n : ℕ, IsBaseLabel e n) :
    IsBaseLabel e (baseLabel e) := by
  rcases isBaseLabelOrLeast_baseLabel e with hb | hb
  · exact hb
  · exact absurd h hb.1

theorem baseLabel_le {e : Env} {n : ℕ} (hn : IsBaseLabel e n) : baseLabel e ≤ n :=
  Nat.find_min' (exists_isBaseLabelOrLeast e) (Or.inl hn)

theorem baseLabel_eq_iff (e : Env) (k : ℕ) :
    baseLabel e = k ↔ IsBaseLabelOrLeast e k ∧ ∀ n < k, ¬ IsBaseLabelOrLeast e n :=
  Nat.find_eq_iff (exists_isBaseLabelOrLeast e)

/-- The base vertex. -/
noncomputable def baseVertex (e : Env) : Vertex e.val :=
  ⟨baseLabel e, isSome_baseLabel e⟩

@[simp] theorem baseVertex_val (e : Env) : (baseVertex e).val = baseLabel e := rfl

theorem zero_mem_cell_baseVertex (e : Env) (h : ∃ n : ℕ, IsBaseLabel e n) :
    (0 : Plane) ∈ ((decode e).cell (baseVertex e) : Set Plane) := by
  rw [decode_cell_eq_getD]
  exact (isBaseLabel_baseLabel e h).2

/-- **Off the mask the base label is the root label.**  The root cell contains the origin in
its interior, and any other cell containing the origin would put the origin on its frontier,
hence in the boundary mask. -/
theorem baseLabel_eq_of_rootAt {e : Env} {v : Vertex e.val} (h : rootAt (decode e) 0 = some v) :
    baseLabel e = v.val := by
  obtain ⟨hmask, hint⟩ := (rootAt_eq_some_iff (decode e) (decode_geometry e) 0 v).1 h
  have hv0 : (0 : Plane) ∈ ((decode e).cell v : Set Plane) := interior_subset hint
  have hvbase : IsBaseLabel e v.val := by
    refine ⟨v.property, ?_⟩
    rw [← decode_cell_eq_getD]
    exact hv0
  have hex : ∃ n : ℕ, IsBaseLabel e n := ⟨v.val, hvbase⟩
  apply le_antisymm
  · exact baseLabel_le hvbase
  · by_contra hlt
    push_neg at hlt
    have hne : baseVertex e ≠ v := by
      intro hwv
      have : (baseVertex e).val = v.val := congrArg Subtype.val hwv
      rw [baseVertex_val] at this
      exact absurd this hlt.ne
    have hdisj := (decode_geometry e).2.2.2.1 hne
    have hnot : (0 : Plane) ∉ interior ((decode e).cell (baseVertex e) : Set Plane) :=
      fun h0 => Set.disjoint_left.1 hdisj h0 hint
    have hfr : (0 : Plane) ∈ frontier ((decode e).cell (baseVertex e) : Set Plane) := by
      rw [frontier, ((decode e).cell (baseVertex e)).isCompact.isClosed.closure_eq]
      exact ⟨zero_mem_cell_baseVertex e hex, hnot⟩
    exact hmask (Set.mem_union_left _ (Set.mem_iUnion.2 ⟨baseVertex e, hfr⟩))

theorem measurable_slot (n : ℕ) : Measurable fun e : Env => e.val.1 n :=
  (measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)

theorem measurable_markedSlot (n : ℕ) : Measurable fun ω : MarkedEnvironment => ω.1.val.1 n :=
  (measurable_slot n).comp measurable_fst

theorem measurableSet_isBaseLabel (n : ℕ) : MeasurableSet {e : Env | IsBaseLabel e n} := by
  have h1 : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
    measurable_slot n Spatial.measurableSet_slotIsSome
  have hm : Measurable fun e : Env =>
      ((((e.val.1 n).getD Spatial.referenceCell : CompactCell)), (0 : Plane)) :=
    (Spatial.measurable_slotCell.comp (measurable_slot n)).prodMk measurable_const
  have h2 : MeasurableSet {e : Env |
      (0 : Plane) ∈ (((e.val.1 n).getD Spatial.referenceCell : CompactCell) : Set Plane)} :=
    hm Spatial.measurableSet_cellMem
  exact h1.inter h2

theorem measurableSet_isBaseLabelOrLeast (n : ℕ) :
    MeasurableSet {e : Env | IsBaseLabelOrLeast e n} := by
  have hsome : MeasurableSet {e : Env | (e.val.1 n).isSome} :=
    measurable_slot n Spatial.measurableSet_slotIsSome
  have hany : MeasurableSet {e : Env | ∃ m : ℕ, IsBaseLabel e m} := by
    have hrw : {e : Env | ∃ m : ℕ, IsBaseLabel e m}
        = ⋃ m : ℕ, {e : Env | IsBaseLabel e m} := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hrw]
    exact MeasurableSet.iUnion fun m => measurableSet_isBaseLabel m
  have hrw : {e : Env | IsBaseLabelOrLeast e n}
      = {e : Env | IsBaseLabel e n} ∪
        ({e : Env | ∃ m : ℕ, IsBaseLabel e m}ᶜ ∩ {e : Env | (e.val.1 n).isSome}) := by
    ext e
    simp only [IsBaseLabelOrLeast, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff]
  rw [hrw]
  exact (measurableSet_isBaseLabel n).union (hany.compl.inter hsome)

theorem measurable_baseLabel : Measurable baseLabel := by
  refine measurable_to_countable' fun k => ?_
  have hset : baseLabel ⁻¹' {k} = {e : Env | IsBaseLabelOrLeast e k} ∩
      ⋂ n : ℕ, ⋂ _ : n < k, {e : Env | IsBaseLabelOrLeast e n}ᶜ := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff, baseLabel_eq_iff, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hset]
  exact (measurableSet_isBaseLabelOrLeast k).inter
    (MeasurableSet.iInter fun n =>
      MeasurableSet.iInter fun _ => (measurableSet_isBaseLabelOrLeast n).compl)

/-! ### The good event of the construction

The concrete interpolant `phi` is a `Classical.choose` over block interpolants, and block
interpolants are unique exactly under sublinear diameter decay `s:eq:DR`
(`isBlockInterpolation_unique` below).  On an environment without that decay two
similarity-related choices need not correspond, so an *everywhere* covariance input for
`phi` would be undischargeable.  The construction is therefore switched off outside the event
`SublinearEvent`.  That event has full measure by the checked
`ae_maxDiamHittingBall_finite_and_sublinear`, and its similarity invariance is proved here
(`sublinearDiameterDecay_of_similarity`).  Its measurability is never needed on its own: the
construction only sees the event through the gated interpolant `gatedApproximant`, whose
measurability is the input `hmeas`. -/

/-- The good event: sublinear diameter decay of the cells hitting large balls, `s:eq:DR`. -/
def SublinearEvent : Set Env := {e | SublinearDiameterDecay (decode e)}

theorem mem_sublinearEvent_iff (e : Env) :
    e ∈ SublinearEvent ↔ SublinearDiameterDecay (decode e) := Iff.rfl

/-- The good event has full measure under mass transport and the (FE) moment. -/
theorem ae_mem_sublinearEvent (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    ∀ᵐ e ∂ν, e ∈ SublinearEvent := by
  filter_upwards [ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE] with e he
  exact he.2.1

/-- The inverse of a similarity relabeling is a similarity relabeling. -/
theorem isSimilarityRelabel_symm {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' relabel) :
    IsSimilarityRelabel s⁻¹ (-s • u) (inv_pos.2 hs) e' e relabel.symm := by
  refine ⟨fun v' => ?_, fun v' w' => ?_⟩
  · apply SetLike.coe_injective
    have hcell := h.1 (relabel.symm v')
    rw [Equiv.apply_symm_apply] at hcell
    rw [coe_transformCell, hcell, coe_transformCell, Set.image_image]
    have hid : (fun z : Plane => positiveSimilarity s⁻¹ (-s • u) (positiveSimilarity s u z)) = id :=
      funext fun z => positiveSimilarity_inverse_left s u z hs
    rw [hid, Set.image_id]
  · have := h.2 (relabel.symm v') (relabel.symm w')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm

/-- A similarity scales the diameters of the cells hitting a ball by `s`, and every cell of
the image hitting `B(0, R)` comes from a cell hitting `B(0, ‖u‖ + R/s)`. -/
theorem maxDiamHittingBall_le_of_similarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' relabel)
    (R : ℝ) :
    maxDiamHittingBall (decode e') R
      ≤ ENNReal.ofReal s * maxDiamHittingBall (decode e) (‖u‖ + R / s) := by
  refine iSup_le fun v' => ?_
  obtain ⟨v', hv'⟩ := v'
  have hcell : (decode e').cell v'
      = transformCell s u hs ((decode e).cell (relabel.symm v')) := by
    have := h.1 (relabel.symm v')
    rwa [Equiv.apply_symm_apply] at this
  have hdiam : Metric.diam ((decode e').cell v' : Set Plane)
      = s * Metric.diam ((decode e).cell (relabel.symm v') : Set Plane) := by
    rw [hcell, coe_transformCell, diam_image_positiveSimilarity s u hs]
  have hhits : Hits (decode e) (Metric.closedBall (0 : Plane) (‖u‖ + R / s))
      (relabel.symm v') := by
    obtain ⟨z', hz'cell, hz'ball⟩ := hv'
    rw [hcell, coe_transformCell] at hz'cell
    obtain ⟨z, hz, rfl⟩ := hz'cell
    refine ⟨z, hz, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz'ball ⊢
    have hzu : ‖z - u‖ ≤ R / s := by
      rw [positiveSimilarity, norm_smul, Real.norm_of_nonneg hs.le] at hz'ball
      rwa [le_div_iff₀ hs, mul_comm]
    calc ‖z‖ = ‖u + (z - u)‖ := by rw [add_sub_cancel]
      _ ≤ ‖u‖ + ‖z - u‖ := norm_add_le _ _
      _ ≤ ‖u‖ + R / s := by linarith
  calc ENNReal.ofReal (Metric.diam ((decode e').cell v' : Set Plane))
      = ENNReal.ofReal s
          * ENNReal.ofReal (Metric.diam ((decode e).cell (relabel.symm v') : Set Plane)) := by
        rw [hdiam, ENNReal.ofReal_mul hs.le]
    _ ≤ ENNReal.ofReal s * maxDiamHittingBall (decode e) (‖u‖ + R / s) := by
        gcongr
        exact le_iSup (fun w : {w : Vertex e.val //
          Hits (decode e) (Metric.closedBall (0 : Plane) (‖u‖ + R / s)) w} =>
            ENNReal.ofReal (Metric.diam ((decode e).cell w.1 : Set Plane))) ⟨relabel.symm v', hhits⟩

/-- **Sublinear diameter decay `s:eq:DR` is similarity invariant.** -/
theorem sublinearDiameterDecay_of_similarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' relabel)
    (hsub : SublinearDiameterDecay (decode e)) : SublinearDiameterDecay (decode e') := by
  intro ε hε
  obtain ⟨R₀, hR₀, hbound⟩ := hsub (ε / 2) (by positivity)
  refine ⟨max (s * R₀) (max (s * ‖u‖) 1), by positivity, fun R hR => ?_⟩
  have hsR₀ : s * R₀ ≤ R := le_trans (le_max_left _ _) hR
  have hsu : s * ‖u‖ ≤ R := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hR)
  have hR' : R₀ ≤ ‖u‖ + R / s := by
    have : R₀ ≤ R / s := by rwa [le_div_iff₀ hs, mul_comm]
    linarith [norm_nonneg u]
  have hkey := maxDiamHittingBall_le_of_similarity h R
  have hb := hbound (‖u‖ + R / s) hR'
  have hs0 : s ≠ 0 := hs.ne'
  calc maxDiamHittingBall (decode e') R
      ≤ ENNReal.ofReal s * maxDiamHittingBall (decode e) (‖u‖ + R / s) := hkey
    _ ≤ ENNReal.ofReal s * ENNReal.ofReal (ε / 2 * (‖u‖ + R / s)) := by gcongr
    _ = ENNReal.ofReal (s * (ε / 2 * (‖u‖ + R / s))) := (ENNReal.ofReal_mul hs.le).symm
    _ ≤ ENNReal.ofReal (ε * R) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsR : s * (R / s) = R := by field_simp
        have h1 : s * (ε / 2 * (‖u‖ + R / s))
            = ε / 2 * (s * ‖u‖) + ε / 2 * (s * (R / s)) := by ring
        rw [h1, hsR]
        linarith [mul_le_mul_of_nonneg_left hsu (by positivity : (0:ℝ) ≤ ε / 2)]

/-- Similarity-related environments are in the good event together. -/
theorem mem_sublinearEvent_iff_of_similarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} (h : IsSimilarityRelabel s u hs e e' relabel) :
    e ∈ SublinearEvent ↔ e' ∈ SublinearEvent :=
  ⟨sublinearDiameterDecay_of_similarity h,
    sublinearDiameterDecay_of_similarity (isSimilarityRelabel_symm h)⟩

/-! ### The marked difference approximants along a deterministic subsequence -/

/-- **The gated interpolant**: the concrete `approximationAtLabel` on the good event and `0`
off it.  Measurability of *this* function is the input `hmeas` below: on the good event
`phi` is the unique block interpolant, so it agrees there with any measurable selection of
block minimizers; off the event `phi` is an uncontrolled `Classical.choose`, and asking for
its measurability would be asking for something no producer can supply. -/
noncomputable def gatedApproximant (m : ℕ) (ω : MarkedEnvironment) (n : ℕ) : Plane :=
  if ω.1 ∈ SublinearEvent then approximationAtLabel m ω n else 0

theorem gatedApproximant_of_mem (m : ℕ) {ω : MarkedEnvironment} (hG : ω.1 ∈ SublinearEvent)
    (n : ℕ) : gatedApproximant m ω n = approximationAtLabel m ω n := by
  unfold gatedApproximant
  rw [if_pos hG]

theorem gatedApproximant_of_notMem (m : ℕ) {ω : MarkedEnvironment} (hG : ω.1 ∉ SublinearEvent)
    (n : ℕ) : gatedApproximant m ω n = 0 := by
  unfold gatedApproximant
  rw [if_neg hG]

/-- On the marked law the gated interpolant is the concrete one almost surely. -/
theorem ae_gatedApproximant_eq (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (m n : ℕ) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, gatedApproximant m ω n = approximationAtLabel m ω n := by
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE)] with ω hG
  exact gatedApproximant_of_mem m hG n

/-- **The concrete difference approximants.**  At the paired label `Nat.pair a b` this is
`φ_{ms j}(H_b) − φ_{ms j}(H_a)` for the block interpolant of the main statement, when the
environment is in the good event and both labels are active, and `0` otherwise. -/
noncomputable def differenceApproximant (ms : ℕ → ℕ) (j : ℕ) (ω : MarkedEnvironment) (k : ℕ) :
    Plane :=
  if (ω.1.val.1 (Nat.unpair k).1).isSome ∧ (ω.1.val.1 (Nat.unpair k).2).isSome then
    gatedApproximant (ms j) ω (Nat.unpair k).2 - gatedApproximant (ms j) ω (Nat.unpair k).1
  else 0

theorem approximationAtLabel_vertex (m : ℕ) (ω : MarkedEnvironment) (v : Vertex ω.1.val) :
    approximationAtLabel m ω v.val = phi (decode ω.1) ω.2 m v := by
  unfold approximationAtLabel
  rw [dif_pos v.property]

theorem differenceApproximant_pair (ms : ℕ → ℕ) (j : ℕ) (ω : MarkedEnvironment)
    (hG : ω.1 ∈ SublinearEvent) (v w : Vertex ω.1.val) :
    differenceApproximant ms j ω (Nat.pair v.val w.val)
      = phi (decode ω.1) ω.2 (ms j) w - phi (decode ω.1) ω.2 (ms j) v := by
  unfold differenceApproximant
  rw [Nat.unpair_pair]
  simp only [v.property, w.property, and_self, if_true]
  rw [gatedApproximant_of_mem _ hG, gatedApproximant_of_mem _ hG,
    approximationAtLabel_vertex, approximationAtLabel_vertex]

theorem differenceApproximant_of_not (ms : ℕ → ℕ) (j : ℕ) (ω : MarkedEnvironment) (k : ℕ)
    (hk : ¬ (ω.1 ∈ SublinearEvent ∧
      (ω.1.val.1 (Nat.unpair k).1).isSome ∧ (ω.1.val.1 (Nat.unpair k).2).isSome)) :
    differenceApproximant ms j ω k = 0 := by
  unfold differenceApproximant
  by_cases hG : ω.1 ∈ SublinearEvent
  · have hs : ¬ ((ω.1.val.1 (Nat.unpair k).1).isSome ∧ (ω.1.val.1 (Nat.unpair k).2).isSome) :=
      fun h => hk ⟨hG, h⟩
    rw [if_neg hs]
  · rw [gatedApproximant_of_notMem _ hG, gatedApproximant_of_notMem _ hG, sub_self, ite_self]

/-- Off the good event the approximants vanish identically. -/
theorem differenceApproximant_eq_zero_of_notMem (ms : ℕ → ℕ) (j : ℕ) (ω : MarkedEnvironment)
    (hG : ω.1 ∉ SublinearEvent) : differenceApproximant ms j ω = 0 :=
  funext fun k => differenceApproximant_of_not ms j ω k fun h => hG h.1

theorem measurable_differenceApproximant (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (j k : ℕ) : Measurable fun ω => differenceApproximant ms j ω k := by
  unfold differenceApproximant
  refine Measurable.ite ?_ ((hmeas _ _).sub (hmeas _ _)) measurable_const
  exact (measurable_markedSlot _ Spatial.measurableSet_slotIsSome).inter
    (measurable_markedSlot _ Spatial.measurableSet_slotIsSome)

/-- **The marked limiting difference field**: the limit of the difference approximants on
the good set where every paired label converges, and the zero field elsewhere. -/
noncomputable def markedDifferenceField (ms : ℕ → ℕ) : MarkedEnvironment → ℕ → Plane :=
  Set.indicator (LimitGood (differenceApproximant ms)) (limitValue (differenceApproximant ms))

theorem markedDifferenceField_of_mem (ms : ℕ → ℕ) {ω : MarkedEnvironment}
    (h : ω ∈ LimitGood (differenceApproximant ms)) :
    markedDifferenceField ms ω = limitValue (differenceApproximant ms) ω :=
  Set.indicator_of_mem h _

theorem markedDifferenceField_of_notMem (ms : ℕ → ℕ) {ω : MarkedEnvironment}
    (h : ω ∉ LimitGood (differenceApproximant ms)) :
    markedDifferenceField ms ω = 0 :=
  Set.indicator_of_notMem h _

theorem measurable_markedDifferenceField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable (markedDifferenceField ms) :=
  (measurable_limitValue (measurable_differenceApproximant ms hmeas)).indicator
    (measurableSet_limitGood (measurable_differenceApproximant ms hmeas))

/-- A paired-label field is a difference field on an environment: it vanishes on the
diagonal and is additive along triples of active labels. -/
def IsDifferenceField (e : Env) (g : ℕ → Plane) : Prop :=
  (∀ v : Vertex e.val, g (Nat.pair v.val v.val) = 0) ∧
    ∀ v w x : Vertex e.val,
      g (Nat.pair v.val x.val) = g (Nat.pair v.val w.val) + g (Nat.pair w.val x.val)

theorem isDifferenceField_zero (e : Env) : IsDifferenceField e 0 :=
  ⟨fun _ => rfl, fun _ _ _ => by simp⟩

theorem isDifferenceField_limitValue (ms : ℕ → ℕ) {ω : MarkedEnvironment}
    (h : ω ∈ LimitGood (differenceApproximant ms)) :
    IsDifferenceField ω.1 (limitValue (differenceApproximant ms) ω) := by
  by_cases hG : ω.1 ∈ SublinearEvent
  · refine ⟨fun v => ?_, fun v w x => ?_⟩
    · refine limitValue_eq_zero_of_approximants_zero fun j => ?_
      rw [differenceApproximant_pair ms j ω hG, sub_self]
    · have h1 := tendsto_limitValue (mem_convergesAt_of_mem_limitGood h (Nat.pair v.val x.val))
      have h2 := tendsto_limitValue (mem_convergesAt_of_mem_limitGood h (Nat.pair v.val w.val))
      have h3 := tendsto_limitValue (mem_convergesAt_of_mem_limitGood h (Nat.pair w.val x.val))
      refine tendsto_nhds_unique h1 ?_
      have hfun : (fun j => differenceApproximant ms j ω (Nat.pair v.val x.val))
          = fun j => differenceApproximant ms j ω (Nat.pair v.val w.val)
            + differenceApproximant ms j ω (Nat.pair w.val x.val) := by
        funext j
        rw [differenceApproximant_pair ms j ω hG, differenceApproximant_pair ms j ω hG,
          differenceApproximant_pair ms j ω hG]
        abel
      rw [hfun]
      exact h2.add h3
  · have hz : limitValue (differenceApproximant ms) ω = 0 := by
      funext k
      exact limitValue_eq_zero_of_approximants_zero fun j =>
        differenceApproximant_of_not ms j ω k fun h' => hG h'.1
    rw [hz]
    exact isDifferenceField_zero ω.1

theorem isDifferenceField_markedDifferenceField (ms : ℕ → ℕ) (ω : MarkedEnvironment) :
    IsDifferenceField ω.1 (markedDifferenceField ms ω) := by
  by_cases h : ω ∈ LimitGood (differenceApproximant ms)
  · rw [markedDifferenceField_of_mem ms h]
    exact isDifferenceField_limitValue ms h
  · rw [markedDifferenceField_of_notMem ms h]
    exact isDifferenceField_zero ω.1

/-! ### Descent to the unmarked difference field -/

/-- **The unmarked difference field**: the descent of the marked difference field through the
grid average of the arctangent code, on the descent-good set, and zero elsewhere. -/
noncomputable def unmarkedDifferenceField (ms : ℕ → ℕ) : Env → ℕ → Plane :=
  descentField gridLaw (markedDifferenceField ms)

theorem measurable_unmarkedDifferenceField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    Measurable (unmarkedDifferenceField ms) :=
  measurable_descentField gridLaw (measurable_markedDifferenceField ms hmeas)

/-- On the descent-good set the descended value is the value at some grid. -/
theorem exists_unmarkedValue_eq (Ψ : MarkedEnvironment → ℕ → Plane) {e : Env}
    (he : e ∈ DescentGood gridLaw Ψ) : ∃ D : Grid, unmarkedValue gridLaw Ψ e = Ψ (e, D) := by
  obtain ⟨D, hD⟩ := ((mem_descentGood_iff gridLaw Ψ e).1 he).exists
  exact ⟨D, hD.symm⟩

theorem isDifferenceField_unmarkedDifferenceField (ms : ℕ → ℕ) (e : Env) :
    IsDifferenceField e (unmarkedDifferenceField ms e) := by
  unfold unmarkedDifferenceField
  by_cases he : e ∈ DescentGood gridLaw (markedDifferenceField ms)
  · rw [descentField_of_mem gridLaw _ he]
    obtain ⟨D, hD⟩ := exists_unmarkedValue_eq (markedDifferenceField ms) he
    rw [hD]
    exact isDifferenceField_markedDifferenceField ms (e, D)
  · rw [descentField_of_notMem gridLaw _ he]
    exact isDifferenceField_zero e

/-! ### The harmonic coordinate field -/

/-- **The candidate harmonic coordinate**: the unmarked difference field integrated from the
canonical base label, zero at absent labels. -/
noncomputable def harmonicCellField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n) :
    CellField where
  value e n :=
    if (e.val.1 n).isSome then unmarkedDifferenceField ms e (Nat.pair (baseLabel e) n) else 0
  measurable_value := by
    refine measurable_pi_iff.mpr fun n => ?_
    refine Measurable.ite (measurable_slot n Spatial.measurableSet_slotIsSome) ?_ measurable_const
    have hF : Measurable fun q : Env × ℕ => unmarkedDifferenceField ms q.1 (Nat.pair q.2 n) :=
      measurable_from_prod_countable_left fun k =>
        (measurable_pi_apply (Nat.pair k n)).comp (measurable_unmarkedDifferenceField ms hmeas)
    exact hF.comp (measurable_id.prodMk measurable_baseLabel)
  absent_zero := by
    intro e n hn
    simp [hn]

theorem harmonicCellField_at (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (e : Env) (v : Vertex e.val) :
    (harmonicCellField ms hmeas).at e v
      = unmarkedDifferenceField ms e (Nat.pair (baseLabel e) v.val) := by
  show (if (e.val.1 v.val).isSome then _ else _) = _
  rw [if_pos v.property]

/-- **Root normalization holds everywhere**: at the root label the field is the diagonal
value of a difference field. -/
theorem rootNormalized_harmonicCellField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (e : Env) : RootNormalized (harmonicCellField ms hmeas) e := by
  intro v hv
  rw [harmonicCellField_at, baseLabel_eq_of_rootAt hv]
  exact (isDifferenceField_unmarkedDifferenceField ms e).1 v

/-- The marked potential: the marked difference field integrated from the base label.  On
the event `markedDifferenceField ms ω = unmarkedDifferenceField ms ω.1` it is exactly
`(harmonicCellField ms hmeas).at ω.1`. -/
noncomputable def markedPotential (ms : ℕ → ℕ) (ω : MarkedEnvironment) :
    Vertex ω.1.val → Plane :=
  fun v => markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val)

theorem harmonicCellField_at_eq_markedPotential (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    {ω : MarkedEnvironment} (h : markedDifferenceField ms ω = unmarkedDifferenceField ms ω.1) :
    (harmonicCellField ms hmeas).at ω.1 = markedPotential ms ω := by
  funext v
  rw [harmonicCellField_at, markedPotential, h]

/-! ### Similarity covariance: clauses (1) and (2) -/

/-- **OPEN INPUT (audited gap 1, exact covariance of the construction).**  On the good
event, the gradients of the concrete block interpolants commute with every physical
similarity, for a measure preserving action of the similarity on uniform grids.  This is the
manuscript's "its gradient construction commutes with translations and positive dilations"
for the approximants `φ_m`.  It is restricted to `SublinearEvent` because only there are
block interpolants unique (`isBlockInterpolation_unique`), so only there is the
`Classical.choose` in `phi` determined by the specification; its producer is the covariance of
`IsBlockInterpolation` under `transformCell`, together with the checked grid actions
`Geometry/UniformGridDilationInvariance.dilate` and `Geometry/DyadicGridTranslation.translate`
and their measure preservation (`map_dilate_gridMeasure`, `map_translate_gridMeasure`). -/
def ApproximantGradientCovariant (ms : ℕ → ℕ) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env) (relabel : Vertex e.val ≃ Vertex e'.val),
    IsSimilarityRelabel s u hs e e' relabel → e ∈ SublinearEvent →
      ∃ act : Grid → Grid, MeasurePreserving act gridLaw gridLaw ∧
        ∀ (D : Grid) (j : ℕ) (v w : Vertex e.val),
          phi (decode e') (act D) (ms j) (relabel w) - phi (decode e') (act D) (ms j) (relabel v)
            = s • (phi (decode e) D (ms j) w - phi (decode e) D (ms j) v)

/-- The label transport of a similarity on paired labels: relabel both components backwards
and scale by `s`; zero on pairs that are not both active in the target environment. -/
noncomputable def pairTransport (s : ℝ) {e e' : Env} (relabel : Vertex e.val ≃ Vertex e'.val)
    (c : ℕ → Plane) (k : ℕ) : Plane :=
  if h : (e'.val.1 (Nat.unpair k).1).isSome ∧ (e'.val.1 (Nat.unpair k).2).isSome then
    s • c (Nat.pair (relabel.symm ⟨(Nat.unpair k).1, h.1⟩).val
      (relabel.symm ⟨(Nat.unpair k).2, h.2⟩).val)
  else 0

theorem pairTransport_zero (s : ℝ) {e e' : Env} (relabel : Vertex e.val ≃ Vertex e'.val) :
    pairTransport s relabel 0 = 0 := by
  funext k
  unfold pairTransport
  split_ifs <;> simp

theorem pairTransport_pair (s : ℝ) {e e' : Env} (relabel : Vertex e.val ≃ Vertex e'.val)
    (c : ℕ → Plane) (v w : Vertex e.val) :
    pairTransport s relabel c (Nat.pair (relabel v).val (relabel w).val)
      = s • c (Nat.pair v.val w.val) := by
  unfold pairTransport
  have hk : (Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).1 = (relabel v).val ∧
      (Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).2 = (relabel w).val := by
    rw [Nat.unpair_pair]
    exact ⟨rfl, rfl⟩
  have hpos : (e'.val.1 (Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).1).isSome ∧
      (e'.val.1 (Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).2).isSome := by
    rw [hk.1, hk.2]
    exact ⟨(relabel v).property, (relabel w).property⟩
  rw [dif_pos hpos]
  have h1 : (⟨(Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).1, hpos.1⟩ : Vertex e'.val)
      = relabel v := Subtype.ext hk.1
  have h2 : (⟨(Nat.unpair (Nat.pair (relabel v).val (relabel w).val)).2, hpos.2⟩ : Vertex e'.val)
      = relabel w := Subtype.ext hk.2
  rw [h1, h2, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The difference approximants transform by the label transport: on the good event by the
covariance of the interpolants, and off it because both sides vanish. -/
theorem differenceApproximant_pairTransport (ms : ℕ → ℕ) {s : ℝ} {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val}
    (hGG : e ∈ SublinearEvent ↔ e' ∈ SublinearEvent) {act : Grid → Grid}
    (hact : e ∈ SublinearEvent → ∀ (D : Grid) (j : ℕ) (v w : Vertex e.val),
      phi (decode e') (act D) (ms j) (relabel w) - phi (decode e') (act D) (ms j) (relabel v)
        = s • (phi (decode e) D (ms j) w - phi (decode e) D (ms j) v))
    (D : Grid) (j k : ℕ) :
    differenceApproximant ms j (e', act D) k
      = pairTransport s relabel (differenceApproximant ms j (e, D)) k := by
  by_cases hG : e ∈ SublinearEvent
  · have hG' : e' ∈ SublinearEvent := hGG.1 hG
    by_cases hk : (e'.val.1 (Nat.unpair k).1).isSome ∧ (e'.val.1 (Nat.unpair k).2).isSome
    · have hR : pairTransport s relabel (differenceApproximant ms j (e, D)) k
          = s • differenceApproximant ms j (e, D)
            (Nat.pair (relabel.symm ⟨(Nat.unpair k).1, hk.1⟩).val
              (relabel.symm ⟨(Nat.unpair k).2, hk.2⟩).val) := by
        unfold pairTransport
        rw [dif_pos hk]
      rw [hR, differenceApproximant_pair ms j (e, D) hG]
      have hL : differenceApproximant ms j (e', act D) k
          = phi (decode e') (act D) (ms j) (relabel (relabel.symm ⟨(Nat.unpair k).2, hk.2⟩))
            - phi (decode e') (act D) (ms j) (relabel (relabel.symm ⟨(Nat.unpair k).1, hk.1⟩)) := by
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        have hkeq : k = Nat.pair (Nat.unpair k).1 (Nat.unpair k).2 := (Nat.pair_unpair k).symm
        conv_lhs => rw [hkeq]
        exact differenceApproximant_pair ms j (e', act D) hG' ⟨(Nat.unpair k).1, hk.1⟩
          ⟨(Nat.unpair k).2, hk.2⟩
      rw [hL, hact hG]
    · have hR : pairTransport s relabel (differenceApproximant ms j (e, D)) k = 0 := by
        unfold pairTransport
        rw [dif_neg hk]
      rw [hR]
      exact differenceApproximant_of_not ms j (e', act D) k fun h => hk h.2
  · have hG' : e' ∉ SublinearEvent := fun h => hG (hGG.2 h)
    rw [differenceApproximant_eq_zero_of_notMem ms j (e', act D) hG',
      differenceApproximant_eq_zero_of_notMem ms j (e, D) hG, pairTransport_zero]

/-- A scalar exact relation between approximants passes to the marked limit, whether or not
the approximants converge. -/
theorem limitValue_smul_of_forall {Ω : Type*} {A : ℕ → Ω → ℕ → Plane} {ω ω' : Ω} {k k' : ℕ}
    {s : ℝ} (hs : s ≠ 0) (h : ∀ j, A j ω' k' = s • A j ω k) :
    limitValue A ω' k' = s • limitValue A ω k := by
  by_cases hk : ω ∈ ConvergesAt A k
  · obtain ⟨c, hc⟩ := hk
    rw [limitValue_eq_of_tendsto hc]
    refine limitValue_eq_of_tendsto ?_
    simp only [h]
    exact hc.const_smul s
  · have hk' : ω' ∉ ConvergesAt A k' := by
      rintro ⟨c, hc⟩
      refine hk ⟨s⁻¹ • c, ?_⟩
      have hfun : (fun j => A j ω k) = fun j => s⁻¹ • A j ω' k' := by
        funext j
        rw [h j, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [hfun]
      exact hc.const_smul _
    rw [limitValue_of_notMem hk, limitValue_of_notMem hk', smul_zero]

/-- The good set is invariant under the label transport relation. -/
theorem mem_limitGood_iff_of_pairTransport (ms : ℕ → ℕ) {s : ℝ} (hs : s ≠ 0) {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} {D D' : Grid}
    (hrel : ∀ j k, differenceApproximant ms j (e', D') k
      = pairTransport s relabel (differenceApproximant ms j (e, D)) k) :
    (e, D) ∈ LimitGood (differenceApproximant ms)
      ↔ (e', D') ∈ LimitGood (differenceApproximant ms) := by
  constructor
  · intro hg
    rw [mem_limitGood_iff]
    intro k'
    by_cases hk : (e'.val.1 (Nat.unpair k').1).isSome ∧ (e'.val.1 (Nat.unpair k').2).isSome
    · have hrel' : ∀ j, differenceApproximant ms j (e', D') k'
          = s • differenceApproximant ms j (e, D)
            (Nat.pair (relabel.symm ⟨(Nat.unpair k').1, hk.1⟩).val
              (relabel.symm ⟨(Nat.unpair k').2, hk.2⟩).val) := by
        intro j
        rw [hrel j k']
        unfold pairTransport
        rw [dif_pos hk]
      obtain ⟨c, hc⟩ := mem_limitGood_iff.1 hg _
      refine ⟨s • c, ?_⟩
      simp only [hrel']
      exact hc.const_smul s
    · refine ⟨0, ?_⟩
      have hfun : (fun j => differenceApproximant ms j (e', D') k') = fun _ => 0 :=
        funext fun j => differenceApproximant_of_not ms j (e', D') k' fun h => hk h.2
      rw [hfun]
      exact tendsto_const_nhds
  · intro hg'
    rw [mem_limitGood_iff]
    intro k
    by_cases hk : (e.val.1 (Nat.unpair k).1).isSome ∧ (e.val.1 (Nat.unpair k).2).isSome
    · have hkeq : k = Nat.pair (⟨(Nat.unpair k).1, hk.1⟩ : Vertex e.val).val
          (⟨(Nat.unpair k).2, hk.2⟩ : Vertex e.val).val := (Nat.pair_unpair k).symm
      have hrel' : ∀ j, differenceApproximant ms j (e', D')
          (Nat.pair (relabel ⟨(Nat.unpair k).1, hk.1⟩).val (relabel ⟨(Nat.unpair k).2, hk.2⟩).val)
            = s • differenceApproximant ms j (e, D) k := by
        intro j
        rw [hrel, pairTransport_pair, ← hkeq]
      obtain ⟨c, hc⟩ := mem_limitGood_iff.1 hg' _
      refine ⟨s⁻¹ • c, ?_⟩
      have hfun : (fun j => differenceApproximant ms j (e, D) k)
          = fun j => s⁻¹ • differenceApproximant ms j (e', D')
            (Nat.pair (relabel ⟨(Nat.unpair k).1, hk.1⟩).val
              (relabel ⟨(Nat.unpair k).2, hk.2⟩).val) := by
        funext j
        rw [hrel' j, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [hfun]
      exact hc.const_smul _
    · refine ⟨0, ?_⟩
      have hfun : (fun j => differenceApproximant ms j (e, D) k) = fun _ => 0 :=
        funext fun j => differenceApproximant_of_not ms j (e, D) k fun h => hk h.2
      rw [hfun]
      exact tendsto_const_nhds

/-- The marked difference field transforms by the label transport. -/
theorem markedDifferenceField_pairTransport (ms : ℕ → ℕ) {s : ℝ} (hs : s ≠ 0) {e e' : Env}
    {relabel : Vertex e.val ≃ Vertex e'.val} {D D' : Grid}
    (hrel : ∀ j k, differenceApproximant ms j (e', D') k
      = pairTransport s relabel (differenceApproximant ms j (e, D)) k) :
    markedDifferenceField ms (e', D')
      = pairTransport s relabel (markedDifferenceField ms (e, D)) := by
  by_cases hg : (e, D) ∈ LimitGood (differenceApproximant ms)
  · have hg' := (mem_limitGood_iff_of_pairTransport ms hs hrel).1 hg
    rw [markedDifferenceField_of_mem ms hg', markedDifferenceField_of_mem ms hg]
    funext k'
    by_cases hk : (e'.val.1 (Nat.unpair k').1).isSome ∧ (e'.val.1 (Nat.unpair k').2).isSome
    · have hR : pairTransport s relabel (limitValue (differenceApproximant ms) (e, D)) k'
          = s • limitValue (differenceApproximant ms) (e, D)
            (Nat.pair (relabel.symm ⟨(Nat.unpair k').1, hk.1⟩).val
              (relabel.symm ⟨(Nat.unpair k').2, hk.2⟩).val) := by
        unfold pairTransport
        rw [dif_pos hk]
      rw [hR]
      refine limitValue_smul_of_forall hs fun j => ?_
      rw [hrel j k']
      unfold pairTransport
      rw [dif_pos hk]
    · have hR : pairTransport s relabel (limitValue (differenceApproximant ms) (e, D)) k' = 0 := by
        unfold pairTransport
        rw [dif_neg hk]
      rw [hR]
      exact limitValue_eq_zero_of_approximants_zero
        fun j => differenceApproximant_of_not ms j (e', D') k' fun h => hk h.2
  · have hg' : (e', D') ∉ LimitGood (differenceApproximant ms) :=
      fun h => hg ((mem_limitGood_iff_of_pairTransport ms hs hrel).2 h)
    rw [markedDifferenceField_of_notMem ms hg', markedDifferenceField_of_notMem ms hg,
      pairTransport_zero]

/-- **The unmarked difference field is exactly covariant** under every similarity: on the
good event through the covariance input and the grid actions, off it with the identity grid
action, both sides being zero. -/
theorem unmarkedDifferenceField_similarity (ms : ℕ → ℕ)
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms) {s : ℝ}
    {u : Plane} {hs : 0 < s} {e e' : Env} {relabel : Vertex e.val ≃ Vertex e'.val}
    (h : IsSimilarityRelabel s u hs e e' relabel) :
    unmarkedDifferenceField ms e' = pairTransport s relabel (unmarkedDifferenceField ms e) := by
  have hGG := mem_sublinearEvent_iff_of_similarity h
  have hGG' : e' ∈ SublinearEvent ↔ e ∈ SublinearEvent := hGG.symm
  by_cases hG : e ∈ SublinearEvent
  · obtain ⟨act, hactmp, hact⟩ := hcov s u hs e e' relabel h hG
    obtain ⟨act', hactmp', hact'⟩ :=
      hcov s⁻¹ (-s • u) (inv_pos.2 hs) e' e relabel.symm (isSimilarityRelabel_symm h) (hGG.1 hG)
    have htr : GridTransfer gridLaw (markedDifferenceField ms) (pairTransport s relabel) e e' :=
      ⟨act, hactmp, fun D =>
        markedDifferenceField_pairTransport ms hs.ne'
          (differenceApproximant_pairTransport ms hGG (fun _ => hact) D)⟩
    have htr' : GridTransfer gridLaw (markedDifferenceField ms)
        (pairTransport s⁻¹ relabel.symm) e' e :=
      ⟨act', hactmp', fun D =>
        markedDifferenceField_pairTransport ms (inv_ne_zero hs.ne')
          (differenceApproximant_pairTransport ms hGG' (fun _ => hact') D)⟩
    exact descentField_covariant gridLaw (measurable_markedDifferenceField ms hmeas) htr htr'
      (pairTransport_zero s relabel)
  · have hG' : e' ∉ SublinearEvent := fun h' => hG (hGG.2 h')
    have htr : GridTransfer gridLaw (markedDifferenceField ms) (pairTransport s relabel) e e' :=
      ⟨id, MeasurePreserving.id _, fun D =>
        markedDifferenceField_pairTransport ms hs.ne'
          (differenceApproximant_pairTransport ms hGG (act := id)
            (fun h' => absurd h' hG) D)⟩
    have htr' : GridTransfer gridLaw (markedDifferenceField ms)
        (pairTransport s⁻¹ relabel.symm) e' e :=
      ⟨id, MeasurePreserving.id _, fun D =>
        markedDifferenceField_pairTransport ms (inv_ne_zero hs.ne')
          (differenceApproximant_pairTransport ms hGG' (act := id)
            (fun h' => absurd h' hG') D)⟩
    exact descentField_covariant gridLaw (measurable_markedDifferenceField ms hmeas) htr htr'
      (pairTransport_zero s relabel)

/-- **Clause (1): gradient covariance**, exactly and everywhere. -/
theorem gradientCovariant_harmonicCellField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms) :
    GradientCovariant (harmonicCellField ms hmeas) := by
  intro s u hs e e' relabel h v w
  have hG := unmarkedDifferenceField_similarity ms hmeas hcov h
  have hD := isDifferenceField_unmarkedDifferenceField ms e
  simp only [CellField.gradient, harmonicCellField_at]
  rw [hG]
  set b₀ : Vertex e.val := relabel.symm (baseVertex e') with hb₀
  have hb : baseLabel e' = (relabel b₀).val := by
    rw [hb₀, Equiv.apply_symm_apply, baseVertex_val]
  rw [hb, pairTransport_pair, pairTransport_pair]
  have h1 : unmarkedDifferenceField ms e (Nat.pair (baseLabel e) w.val)
      = unmarkedDifferenceField ms e (Nat.pair (baseLabel e) b₀.val)
        + unmarkedDifferenceField ms e (Nat.pair b₀.val w.val) := hD.2 (baseVertex e) b₀ w
  have h2 : unmarkedDifferenceField ms e (Nat.pair (baseLabel e) v.val)
      = unmarkedDifferenceField ms e (Nat.pair (baseLabel e) b₀.val)
        + unmarkedDifferenceField ms e (Nat.pair b₀.val v.val) := hD.2 (baseVertex e) b₀ v
  rw [h1, h2, add_sub_add_left_eq_sub, smul_sub]

/-- **Clause (2): normalized covariance**, exactly, wherever the translated root is unmasked. -/
theorem normalizedCovariant_harmonicCellField (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms) :
    NormalizedCovariant (harmonicCellField ms hmeas) := by
  intro s u hs e e' relabel h r hr v
  have hG := unmarkedDifferenceField_similarity ms hmeas hcov h
  have hD := isDifferenceField_unmarkedDifferenceField ms e
  have hr' : rootAt (decode e') 0 = some (relabel r) := by
    have hsim := ActualSpatialDensityBridge.rootAt_similarity h u
    rw [hr] at hsim
    have h0 : positiveSimilarity s u u = 0 := by simp [positiveSimilarity]
    rw [h0] at hsim
    simpa using hsim
  rw [harmonicCellField_at, harmonicCellField_at, harmonicCellField_at, hG,
    baseLabel_eq_of_rootAt hr', pairTransport_pair]
  have h1 : unmarkedDifferenceField ms e (Nat.pair (baseLabel e) v.val)
      = unmarkedDifferenceField ms e (Nat.pair (baseLabel e) r.val)
        + unmarkedDifferenceField ms e (Nat.pair r.val v.val) := hD.2 (baseVertex e) r v
  rw [h1, add_sub_cancel_left]

/-! ### The block-interpolant clause of (7): existence, uniqueness, finite indices -/

/-- The spatial maximal inequality `s:prop:maximal` for the rooted (FE) density: almost
every environment has a finite random maximal constant for the ball averages.  This is
verbatim the hypothesis `hMax` carried by `Spatial/AlmostSureSpatialDiameterBounds`,
`Spatial/AlmostSureCutoffBounds` and `Recurrence/QuenchedFormulation`.

It is **no longer an open input of this file**: it is discharged from the manuscript's own
environment hypotheses by `spatialMaximalBound_of_massTransport` below. -/
def SpatialMaximalBound (ν : Measure Env) : Prop :=
  ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
    (∫⁻ x in Metric.closedBall (0 : Plane) r,
      rootedFiniteEnergyDensity (decode e) x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M

/-- **`s:prop:maximal`, discharged.**  The spatial maximal bound follows from the
manuscript's own environment hypotheses — mass transport `s:eq:MTP` and the finite (FE)
moment — with no further assumption, by
`Spatial/SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity`.

Consequently the `hMax` hypothesis carried by the predecessor version of this reduction is
gone: the three final statements below take `hν` and `hFE` only. -/
theorem spatialMaximalBound_of_massTransport (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    SpatialMaximalBound ν :=
  SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity ν hν hFE.ne

/-- **Uniqueness of block interpolants** (the uniqueness clause of `ApproximationConclusions`).
Every cell lies in a selected square, on which both interpolants are the unique full-energy
vector minimizer with the centroid trace. -/
theorem isBlockInterpolation_unique {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) (hsub : SublinearDiameterDecay F) (m : ℕ)
    {f g : V → Plane} (hf : IsBlockInterpolation F D m f) (hg : IsBlockInterpolation F D m g) :
    f = g := by
  by_cases hm : m = 0
  · subst hm
    rw [IsBlockInterpolation, if_pos rfl] at hf hg
    rw [hf, hg]
  · funext v
    obtain ⟨z, hz⟩ := (F.cell v).nonempty
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    obtain ⟨t, ht, hzt⟩ := exists_selected_mem F hF D hsub (m : ℝ) hmpos z
      (NestedProjectionProducers.notMem_uncoveredSet_of_mem_cell hz)
    have hv : v ∈ patchVertices F (square D t) := ⟨z, hz, hzt⟩
    have hfm := NestedProjectionProducers.centroidTraceMinimizer_of_isBlockInterpolation F D hm hf ht
    have hgm := NestedProjectionProducers.centroidTraceMinimizer_of_isBlockInterpolation F D hm hg ht
    have hA := rectangle_patch_boundaryAnchored F hF (square D t)
    have huniq := existsUnique_vector_trace_minimizer
      (restrictGraph F.graph (patchVertices F (square D t))) hA hfm.1
    have hfeq : (fun a : patchVertices F (square D t) => f a.1)
        = fun a : patchVertices F (square D t) => g a.1 := by
      refine huniq.unique ⟨hfm.1, fun a _ => rfl, fun g' hg' => hfm.2.2 g' ?_⟩
        ⟨hgm.1, fun a ha => ?_, fun g' hg' => hgm.2.2 g' ?_⟩
      · intro a ha
        rw [hg' a ha, hfm.2.1 a ha]
      · rw [hgm.2.1 a ha, hfm.2.1 a ha]
      · intro a ha
        rw [hg' a ha, hfm.2.1 a ha]
    exact congrFun hfeq ⟨v, hv⟩

/-- The almost-sure geometric package of the marked law: finite `D_R`, sublinear diameter
decay (`s:eq:DR`), and the `W`-bound `s:eq:Wbound` from the spatial maximal bound. -/
theorem ae_marked_geometry (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : SpatialMaximalBound ν) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      (∀ R : ℝ, 0 ≤ R → maxDiamHittingBall (decode ω.1) R < ∞) ∧
        SublinearDiameterDecay (decode ω.1) ∧ SpatialDiameterCellBounds (decode ω.1) := by
  have h1 := ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE
  have h2 := AlmostSureSpatialDiameterBounds.ae_spatialDiameterCellBounds_of_ballBound ν hν hFE hMax
  have h : ∀ᵐ e ∂ν, (∀ R : ℝ, 0 ≤ R → maxDiamHittingBall (decode e) R < ∞) ∧
      SublinearDiameterDecay (decode e) ∧ SpatialDiameterCellBounds (decode e) := by
    filter_upwards [h1, h2] with e he1 he2
    exact ⟨he1.1, he1.2.1, he2⟩
  exact ae_marked_of_ae_env ν h

/-- **The block-interpolant clause of `ApproximationConclusions`**, from the spatial maximal
bound: finite positive dyadic indices, the concrete `phi` is a block interpolant at every
stage, and it is the only one. -/
theorem ae_blockInterpolation_clause (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : SpatialMaximalBound ν) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      FinitePositiveIndices (decode ω.1) ω.2 ∧
      ∀ m : ℕ,
        IsBlockInterpolation (decode ω.1) ω.2 m (phi (decode ω.1) ω.2 m) ∧
        ∀ f : Vertex ω.1.val → Plane,
          IsBlockInterpolation (decode ω.1) ω.2 m f → f = phi (decode ω.1) ω.2 m := by
  filter_upwards [ae_marked_geometry ν hν hFE hMax] with ω hω
  obtain ⟨hfin, hsub, hW⟩ := hω
  refine ⟨finitePositiveIndices_of_geometry_of_sublinear (decode ω.1) (decode_geometry ω.1) ω.2
    hfin hsub, fun m => ?_⟩
  have hphi := isBlockInterpolation_phi_of_spatialCellBounds (decode ω.1) (decode_geometry ω.1)
    hW ω.2 m
  exact ⟨hphi, fun f hf =>
    isBlockInterpolation_unique (decode ω.1) (decode_geometry ω.1) ω.2 hsub m hf hphi⟩

/-! ### Representative independence in the sublinearity clause -/

/-- **The representative-independent half of `s:eq:sublinear`** from its centroid half and
`s:eq:DR`: any representative is within the cell diameter `≤ D_R = o(R)` of the centroid. -/
theorem uniformlySublinearError_of_representatives {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hsub : SublinearDiameterDecay F) {Φ : V → Plane}
    (hΦ : UniformlySublinearCorrector F Φ) {z : V → Plane} (hz : CellRepresentatives F z) :
    UniformlySublinearError F Φ z := by
  intro η hη
  obtain ⟨R₀, hR₀, h₀⟩ := hΦ (η / 2) (by positivity)
  obtain ⟨R₁, hR₁, h₁⟩ := hsub (η / 2) (by positivity)
  refine ⟨max R₀ R₁, lt_max_of_lt_left hR₀, fun R hR v hv => ?_⟩
  have hR0 : R₀ ≤ R := le_trans (le_max_left _ _) hR
  have hR1 : R₁ ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le hR₀ hR0
  have hd : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)) ≤ ENNReal.ofReal (η / 2 * R) := by
    refine le_trans ?_ (h₁ R hR1)
    exact le_iSup (fun w : {w : V // Hits F (Metric.closedBall (0 : Plane) R) w} =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, hv⟩
  have hd' : Metric.diam (F.cell v : Set Plane) ≤ η / 2 * R :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hd
  have hcent : ‖cellCentroid F v - z v‖ ≤ Metric.diam (F.cell v : Set Plane) := by
    rw [← dist_eq_norm]
    exact dist_cellCentroid_le_diam F hF v (hz v)
  calc ‖Φ v - z v‖ = ‖(Φ v - cellCentroid F v) + (cellCentroid F v - z v)‖ := by
        congr 1
        abel
    _ ≤ ‖Φ v - cellCentroid F v‖ + ‖cellCentroid F v - z v‖ := norm_add_le _ _
    _ ≤ η / 2 * R + Metric.diam (F.cell v : Set Plane) := add_le_add (h₀ R hR0 v hv) hcent
    _ ≤ η / 2 * R + η / 2 * R := by linarith
    _ = η * R := by ring

/-! ### Grid independence of the difference field -/

/-- **OPEN INPUT (audited gap 1, `s:prop:gridindependence`, comparison half).**  Two
independent uniform grids produce the same marked difference field almost surely.  Its
producer route is `Corrector/GridIndependenceCoupling.aeProd_marked_copies_of_orthogonality`
(from the four specific orthogonality relations and the spatial stationarity identity, both
with producer packets in flight), applied to the normalized marked limit; differences of
almost surely equal potentials are almost surely equal. -/
def DifferenceFieldGridIndependent (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ p : Env × Grid × Grid ∂ν.prod (gridLaw.prod gridLaw),
    markedDifferenceField ms (p.1, p.2.1) = markedDifferenceField ms (p.1, p.2.2)

/-- On the marked law the marked and unmarked difference fields agree almost surely. -/
theorem ae_markedDifferenceField_eq_unmarked (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      markedDifferenceField ms ω = unmarkedDifferenceField ms ω.1 := by
  have hset : MeasurableSet {ω : MarkedEnvironment |
      markedDifferenceField ms ω = unmarkedDifferenceField ms ω.1} :=
    measurableSet_fieldEq (measurable_markedDifferenceField ms hmeas)
      ((measurable_unmarkedDifferenceField ms hmeas).comp measurable_fst)
  rw [Measure.ae_prod_iff_ae_ae hset]
  exact ae_ae_eq_descentField ν gridLaw (measurable_markedDifferenceField ms hmeas) hcopies

theorem ae_harmonicCellField_at_eq_markedPotential (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) :
    ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      (harmonicCellField ms hmeas).at ω.1 = markedPotential ms ω := by
  filter_upwards [ae_markedDifferenceField_eq_unmarked ν ms hmeas hcopies] with ω hω
  exact harmonicCellField_at_eq_markedPotential ms hmeas hω

/-! ### The marked-level inputs (the residue of this milestone)

Each of the following is stated for the marked potential `markedPotential ms`, i.e. for the
limit of the concrete difference approximants along `ms`.  They are the manuscript's
`s:prop:limit` conclusions and the centroid form of `s:eq:sublinear`; their intended producers
are the checked pathwise modules `Corrector/LimitingHarmonicPotential`,
`Corrector/LimitingPotentialFreeOrthogonality`, `Corrector/SpecificEnergyLocalControl`,
`Corrector/ResidualEnergyLineVariation`, `Corrector/GoodOffsetWindowAssembly` and
`Corrector/GoodGridMaximumPrinciple`, instantiated at the concrete approximants.  None of
them mentions the unmarked field `harmonicCellField`: the passage from the marked limit to
the environment-only coordinate is proved below from `DifferenceFieldGridIndependent`. -/

/-- OPEN INPUT (gap 1, `s:prop:limit`, pointwise convergence): almost surely every pairwise
difference of the concrete interpolants converges along `ms`. -/
def MarkedDifferencesConverge (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ω ∈ LimitGood (differenceApproximant ms)

/-- OPEN INPUT (gap 1, `s:prop:limit`(d), patch energies): along `ms` the gradient error of
the marked limit tends to zero in energy on every bounded spatial patch. -/
def MarkedPatchConvergence (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ A : Set Plane, Bornology.IsBounded A →
    Tendsto (fun j => vectorEnergy (restrictGraph (decode ω.1).graph {v | Hits (decode ω.1) A v})
      (fun v => phi (decode ω.1) ω.2 (ms j) v.val - markedPotential ms ω v.val)) atTop (𝓝 0)

/-- OPEN INPUT (gap 1, `s:prop:limit`(a), `s:eq:freeorth`): the marked limit is fully
variationally harmonic on every bounded rectangle and discretely harmonic at every vertex. -/
def MarkedHarmonicity (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
    FullRectangleOrthogonality (decode ω.1) (markedPotential ms ω) ∧
    FullRectangleMinimizer (decode ω.1) (markedPotential ms ω) ∧
    ∀ v : Vertex ω.1.val, ∑' w : Vertex ω.1.val,
      (decode ω.1).graph.c v w • (markedPotential ms ω w - markedPotential ms ω v) = 0

/-- OPEN INPUT (gap 1, `s:eq:sublinear`, centroid form): the marked limit is uniformly
sublinear against cell centroids.  The representative-independent half of the sublinearity
clause is *derived* from this one and `s:eq:DR` (`uniformlySublinearError_of_representatives`);
it is that derived half, not this one, that excludes the zero field (`Potentials.lean:50-51`). -/
def MarkedCentroidSublinearity (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
    UniformlySublinearCorrector (decode ω.1) (markedPotential ms ω)

/-- The graph-neighbourhood error of clause (d) for the marked potential. -/
noncomputable def markedGraphNeighborhoodError (ms : ℕ → ℕ) (radius m : ℕ)
    (ω : MarkedEnvironment) : ℝ :=
  (rootAt (decode ω.1) 0).elim 0 fun r =>
    ⨆ v : (decode ω.1).graph.toSimpleGraph.ball r ((radius + 1 : ℕ) : ℕ∞),
      min 1 ‖normalizedPhi (decode ω.1) ω.2 r m v.val - markedPotential ms ω v.val‖

/-- The specific gradient error of clause (d) for the marked potential. -/
noncomputable def markedSpecificGradientError (ms : ℕ → ℕ) (m : ℕ) (ω : MarkedEnvironment) :
    ℝ≥0∞ :=
  rootedSpecificEnergyDensity (decode ω.1)
    (fun v => phi (decode ω.1) ω.2 m v - markedPotential ms ω v) 0

/-- **OPEN INPUT (measurability of the concrete rooted densities).**  The project has no
producer for measurability, in the environment, of `rootedSpecificEnergyDensity` or of the
graph-ball neighbourhood error (the same gap that leaves `hΓmeas` open in
`InvarianceAssembly`).  This bundles exactly the four such statements the conclusion needs,
all for the marked law: the neighbourhood errors of clause (d), the specific energy of every
stage `φ_m`, the specific gradient errors `φ_m − Φ`, and the specific energy of the marked
limit itself.  It carries no convergence, no bound and no identity. -/
def MarkedDensityMeasurability (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  (∀ radius m : ℕ, AEMeasurable (markedGraphNeighborhoodError ms radius m) (ν.prod gridLaw)) ∧
  (∀ m : ℕ, AEMeasurable (fun ω : MarkedEnvironment =>
    rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0) (ν.prod gridLaw)) ∧
  (∀ m : ℕ, AEMeasurable (markedSpecificGradientError ms m) (ν.prod gridLaw)) ∧
  AEMeasurable (fun ω : MarkedEnvironment =>
    rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0) (ν.prod gridLaw)

/-- OPEN INPUT (gap 1, `s:prop:limit`(d), convergence in probability): along the full
sequence `m`, the neighbourhood errors of the marked potential tend to zero in probability. -/
def MarkedNeighborhoodConvergence (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ radius : ℕ, TendstoInMeasure (ν.prod gridLaw)
    (fun m ω => markedGraphNeighborhoodError ms radius m ω) atTop (fun _ => 0)

/-- OPEN INPUT (gap 1, `s:eq:limitnorm` and `s:lem:e0`): every stage `φ_m` has finite
expected specific energy, and the expected specific energy of `φ_m − Φ` tends to zero along
the full sequence.  Finite expected specific energy of the limit (clause (4)) is *derived*
from this by the quadratic bound `ρ_{θ+η} ≤ 2ρ_θ + 2ρ_η`; it is not a separate input. -/
def MarkedSpecificEnergyConvergence (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  (∀ m : ℕ, (∫⁻ ω : MarkedEnvironment,
    rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0 ∂ν.prod gridLaw) < ∞) ∧
  Tendsto (fun m => ∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw)
    atTop (𝓝 0)

/-! ### Assembly of the approximation clause (7) -/

theorem approximationConclusions_harmonicCellField (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : SpatialMaximalBound ν) (ms : ℕ → ℕ) (hms : StrictMono ms)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hdens : MarkedDensityMeasurability ν ms) (hnbr : MarkedNeighborhoodConvergence ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    ApproximationConclusions ν gridLaw (harmonicCellField ms hmeas) := by
  have hat := ae_harmonicCellField_at_eq_markedPotential ν ms hmeas hcopies
  obtain ⟨hmeas₁, hmeas₂, hmeas₃, -⟩ := hdens
  obtain ⟨hfin, hlim⟩ := hspec
  refine ⟨fun m n => ?_, ae_blockInterpolation_clause ν hν hFE hMax, ?_, ?_,
    ⟨fun m => ⟨hmeas₂ m, hfin m⟩, ?_, ?_⟩, ?_⟩
  · exact (hmeas m n).aemeasurable.congr (ae_gatedApproximant_eq ν hν hFE m n)
  · intro radius m
    refine (hmeas₁ radius m).congr ?_
    filter_upwards [hat] with ω hω
    simp only [graphNeighborhoodError, markedGraphNeighborhoodError, hω]
  · intro radius
    refine (hnbr radius).congr (fun m => ?_) (Eventually.of_forall fun _ => rfl)
    filter_upwards [hat] with ω hω
    simp only [graphNeighborhoodError, markedGraphNeighborhoodError, hω]
  · intro m
    refine (hmeas₃ m).congr ?_
    filter_upwards [hat] with ω hω
    simp only [specificGradientError, markedSpecificGradientError, hω]
  · have hfun : (fun m => ∫⁻ ω : MarkedEnvironment,
        specificGradientError (harmonicCellField ms hmeas) m ω ∂ν.prod gridLaw)
        = fun m => ∫⁻ ω : MarkedEnvironment, markedSpecificGradientError ms m ω ∂ν.prod gridLaw := by
      funext m
      refine lintegral_congr_ae ?_
      filter_upwards [hat] with ω hω
      simp only [specificGradientError, markedSpecificGradientError, hω]
    rw [hfun]
    exact hlim
  · refine ⟨ms, hms, ?_⟩
    filter_upwards [hat, hpatch, hconv,
      ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent) (ae_mem_sublinearEvent ν hν hFE)]
      with ω hω hp hc hG
    refine ⟨fun A hA => ?_, fun r hr v => ?_⟩
    · have hfun : (fun j => spatialPatchError (harmonicCellField ms hmeas) (ms j) ω A)
          = fun j => vectorEnergy (restrictGraph (decode ω.1).graph {v | Hits (decode ω.1) A v})
            (fun v => phi (decode ω.1) ω.2 (ms j) v.val - markedPotential ms ω v.val) := by
        funext j
        simp only [spatialPatchError, hω]
      rw [hfun]
      exact hp A hA
    · rw [hω, markedPotential, baseLabel_eq_of_rootAt hr, markedDifferenceField_of_mem ms hc]
      have hfun : (fun j => normalizedPhi (decode ω.1) ω.2 r (ms j) v)
          = fun j => differenceApproximant ms j ω (Nat.pair r.val v.val) := by
        funext j
        rw [differenceApproximant_pair ms j ω hG]
        rfl
      rw [hfun]
      exact tendsto_limitValue (mem_convergesAt_of_mem_limitGood hc _)

/-! ### Clauses (3) and (4): measurability and finiteness of the specific energy

The specific energy of the *unmarked* field is read off the marked law: the integrand depends
on the environment alone, the grid law has mass one, and on the marked law the unmarked field
agrees almost surely with the marked potential.  Finiteness then comes from the concrete
approximants through the quadratic bound `ρ_{θ+η} ≤ 2ρ_θ + 2ρ_η` of
`Corrector/SpecificEnergyPolarization`; no separate finite-energy input is taken. -/

/-- The specific-energy density is insensitive to the sign of a difference field. -/
theorem specificEnergyDensity_sub_comm {V : Type*} (F : IndexedCells V) (a b : V → Plane)
    (v : V) :
    specificEnergyDensity F (fun u => a u - b u) v
      = specificEnergyDensity F (fun u => b u - a u) v := by
  unfold specificEnergyDensity
  congr 1
  refine tsum_congr fun w => ?_
  congr 2
  rw [show a w - b w - (a v - b v) = -((b w - a w) - (b v - a v)) by abel, norm_neg]

theorem rootedSpecificEnergyDensity_sub_comm {V : Type*} (F : IndexedCells V)
    (a b : V → Plane) (z : Plane) :
    rootedSpecificEnergyDensity F (fun u => a u - b u) z
      = rootedSpecificEnergyDensity F (fun u => b u - a u) z := by
  unfold rootedSpecificEnergyDensity
  cases rootAt F z with
  | none => rfl
  | some v => exact specificEnergyDensity_sub_comm F a b v

/-- A function of the first coordinate integrates over a product with a probability law as
over the first marginal.  (Searched: mathlib has `Measure.map_fst_prod` and `lintegral_map'`
but not this composite; `exact?` returns only this lemma.) -/
theorem lintegral_fst_marginal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (σ : Measure β) [SFinite μ] [IsProbabilityMeasure σ]
    (f : α → ℝ≥0∞) (hf : AEMeasurable f μ) :
    ∫⁻ p : α × β, f p.1 ∂μ.prod σ = ∫⁻ a, f a ∂μ := by
  have hmap : Measure.map Prod.fst (μ.prod σ) = μ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hf' : AEMeasurable f (Measure.map Prod.fst (μ.prod σ)) := by
    rw [hmap]
    exact hf
  rw [← lintegral_map' hf' measurable_fst.aemeasurable, hmap]

/-- Almost-everywhere measurability descends from the product to the first factor
(`AEStronglyMeasurable.of_comp_fst`, read for `ℝ≥0∞`-valued functions). -/
theorem aemeasurable_of_aemeasurable_comp_fst {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (σ : Measure β) [SFinite μ] [IsProbabilityMeasure σ]
    (f : α → ℝ≥0∞) (hf : AEMeasurable (fun p : α × β => f p.1) (μ.prod σ)) :
    AEMeasurable f μ :=
  (hf.aestronglyMeasurable.of_comp_fst (IsProbabilityMeasure.ne_zero σ)).aemeasurable

/-- **Clause (3)**: measurability of the unmarked rooted specific energy density, from that
of the marked potential. -/
theorem aemeasurable_rootedSpecificEnergyDensity_harmonicCellField (ν : Measure Env)
    [SFinite ν] (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) (hdens : MarkedDensityMeasurability ν ms) :
    AEMeasurable (fun e => rootedSpecificEnergyDensity (decode e)
      ((harmonicCellField ms hmeas).at e) 0) ν := by
  have hat := ae_harmonicCellField_at_eq_markedPotential ν ms hmeas hcopies
  refine aemeasurable_of_aemeasurable_comp_fst ν gridLaw _ (hdens.2.2.2.congr ?_)
  filter_upwards [hat] with ω hω
  rw [hω]

/-- Finite expected specific energy of the marked potential: `Φ = φ_m + (Φ − φ_m)` for a stage
`m` at which the expected gradient error is below one. -/
theorem lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top (ν : Measure Env)
    (ms : ℕ → ℕ) (hdens : MarkedDensityMeasurability ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    (∫⁻ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 ∂ν.prod gridLaw) < ∞ := by
  obtain ⟨-, hmeas₂, -, -⟩ := hdens
  obtain ⟨hfin, hlim⟩ := hspec
  obtain ⟨m, hm⟩ := (hlim.eventually (Iio_mem_nhds zero_lt_one)).exists
  have hpt : ∀ ω : MarkedEnvironment,
      rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0
        ≤ 2 * rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0
          + 2 * markedSpecificGradientError ms m ω := by
    intro ω
    have hsum : (fun v => phi (decode ω.1) ω.2 m v
        + (markedPotential ms ω v - phi (decode ω.1) ω.2 m v)) = markedPotential ms ω := by
      funext v
      abel
    have h2 := SpecificEnergyPolarization.rootedSpecificEnergyDensity_add_le (decode ω.1)
      (decode_geometry ω.1) (phi (decode ω.1) ω.2 m)
      (fun v => markedPotential ms ω v - phi (decode ω.1) ω.2 m v) 0
    beta_reduce at h2
    rw [hsum, rootedSpecificEnergyDensity_sub_comm] at h2
    exact h2
  calc (∫⁻ ω : MarkedEnvironment,
        rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 ∂ν.prod gridLaw)
      ≤ ∫⁻ ω : MarkedEnvironment,
          (2 * rootedSpecificEnergyDensity (decode ω.1) (phi (decode ω.1) ω.2 m) 0
            + 2 * markedSpecificGradientError ms m ω) ∂ν.prod gridLaw := lintegral_mono hpt
    _ < ∞ := by
        rw [lintegral_add_left' ((hmeas₂ m).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num), lt_top_iff_ne_top]
        exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (hfin m).ne,
          ENNReal.mul_ne_top (by norm_num) (hm.trans ENNReal.one_lt_top).ne⟩

/-- **Clause (4)**: finite expected specific energy of the unmarked field. -/
theorem finiteSpecificEnergy_harmonicCellField (ν : Measure Env) [SFinite ν] (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) (hdens : MarkedDensityMeasurability ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    FiniteSpecificEnergy ν (harmonicCellField ms hmeas) := by
  have hat := ae_harmonicCellField_at_eq_markedPotential ν ms hmeas hcopies
  have hΦmeas :=
    aemeasurable_rootedSpecificEnergyDensity_harmonicCellField ν ms hmeas hcopies hdens
  calc (∫⁻ e : Env, rootedSpecificEnergyDensity (decode e) ((harmonicCellField ms hmeas).at e) 0 ∂ν)
      = ∫⁻ ω : MarkedEnvironment, rootedSpecificEnergyDensity (decode ω.1)
          ((harmonicCellField ms hmeas).at ω.1) 0 ∂ν.prod gridLaw :=
        (lintegral_fst_marginal ν gridLaw _ hΦmeas).symm
    _ = ∫⁻ ω : MarkedEnvironment,
          rootedSpecificEnergyDensity (decode ω.1) (markedPotential ms ω) 0 ∂ν.prod gridLaw := by
        refine lintegral_congr_ae ?_
        filter_upwards [hat] with ω hω
        rw [hω]
    _ < ∞ := lintegral_rootedSpecificEnergyDensity_markedPotential_lt_top ν ms hdens hspec

/-! ### Clause (5): the almost-sure pathwise clauses -/

/-- **Clause (5)**: the boundary mask (from mass transport alone), root normalization
(everywhere), full spatial and discrete harmonicity, and both halves of the sublinearity
clause — the representative-independent half from the centroid half and `s:eq:DR`. -/
theorem ae_pathwise_clauses (ν : Measure Env) [SFinite ν] (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) (ms : ℕ → ℕ)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcopies : DifferenceFieldGridIndependent ν ms) (hharm : MarkedHarmonicity ν ms)
    (hsub : MarkedCentroidSublinearity ν ms) :
    ∀ᵐ e : Env ∂ν,
      (0 : Plane) ∉ boundaryMask (decode e) ∧
      RootNormalized (harmonicCellField ms hmeas) e ∧
      FullSpatialHarmonicity (harmonicCellField ms hmeas) e ∧
      DiscreteHarmonicity (harmonicCellField ms hmeas) e ∧
      SublinearCorrector (harmonicCellField ms hmeas) e := by
  have hmask := Spatial.ae_notMem_boundaryMask_of_massTransport ν hν
  have hgeom := ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE
  have hmarked : ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
      FullSpatialHarmonicity (harmonicCellField ms hmeas) ω.1 ∧
      DiscreteHarmonicity (harmonicCellField ms hmeas) ω.1 ∧
      UniformlySublinearCorrector (decode ω.1) ((harmonicCellField ms hmeas).at ω.1) := by
    filter_upwards [ae_harmonicCellField_at_eq_markedPotential ν ms hmeas hcopies, hharm, hsub]
      with ω hω hh hs
    refine ⟨?_, ?_, ?_⟩
    · unfold FullSpatialHarmonicity
      rw [hω]
      exact ⟨hh.1, hh.2.1⟩
    · unfold DiscreteHarmonicity CellField.gradient
      rw [hω]
      exact hh.2.2
    · rw [hω]
      exact hs
  have henv := ae_env_of_ae_marked ν (p := fun e =>
    FullSpatialHarmonicity (harmonicCellField ms hmeas) e ∧
    DiscreteHarmonicity (harmonicCellField ms hmeas) e ∧
    UniformlySublinearCorrector (decode e) ((harmonicCellField ms hmeas).at e)) hmarked
  filter_upwards [hmask, hgeom, henv] with e hm hg he
  exact ⟨hm, rootNormalized_harmonicCellField ms hmeas e, he.1, he.2.1,
    ⟨he.2.2, fun z hz =>
      uniformlySublinearError_of_representatives (decode e) (decode_geometry e) hg.2.1 he.2.2 hz⟩⟩

/-! ### The reduction -/

/-- **All seven clauses of `IsHarmonicCoordinate` for the constructed field**, from the
main theorem's own environment hypotheses and the named open inputs.  See
`harmonicCoordinateConclusions_of_named_inputs` for the input list. -/
theorem isHarmonicCoordinate_harmonicCellField (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hharm : MarkedHarmonicity ν ms) (hsub : MarkedCentroidSublinearity ν ms)
    (hdens : MarkedDensityMeasurability ν ms) (hnbr : MarkedNeighborhoodConvergence ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    IsHarmonicCoordinate ν (harmonicCellField ms hmeas) := by
  refine ⟨gradientCovariant_harmonicCellField ms hmeas hcov,
    normalizedCovariant_harmonicCellField ms hmeas hcov,
    aemeasurable_rootedSpecificEnergyDensity_harmonicCellField ν ms hmeas hcopies hdens,
    finiteSpecificEnergy_harmonicCellField ν ms hmeas hcopies hdens hspec,
    ae_pathwise_clauses ν hν hFE.ne ms hmeas hcopies hharm hsub,
    exists_uniformGridLaw, fun σ hσ => ?_⟩
  rw [eq_gridLaw_of_uniformGridLaw hσ]
  exact approximationConclusions_harmonicCellField ν hν hFE.ne
    (spatialMaximalBound_of_massTransport ν hν hFE) ms hms hmeas hcopies hconv
    hpatch hdens hnbr hspec

/-- **Reduction of `HarmonicCoordinateConclusions` to named inputs.**

This is an implication, not a proof of the harmonic-coordinate theorem: the **ten**
hypotheses `hmeas`, `hcov`, `hcopies`, `hconv`, `hpatch`, `hharm`, `hsub`, `hdens`, `hnbr`
and `hspec` are open, and nothing in this file certifies any of them.  The
coordinate field is not an input: it is the concrete `harmonicCellField ms hmeas`, built
from the block interpolants `phi` of the main statement on the good event `SublinearEvent`.

The inputs are, in order:

* `hν`, `hFE` — the manuscript's own environment hypotheses (mass transport and the finite
  (FE) moment); at `ν = validLaw P hP` these are the main theorem's hypotheses, not open
  obligations.
* `ms`, `hms` — a deterministic strictly increasing subsequence, chosen once (a parameter of
  the construction, not a mathematical claim).
* `hmeas` — measurability of the concrete block interpolants at every label and stage, gated
  by the good event (`gatedApproximant`); its producer route is a measurable selection of
  block minimizers (`Corrector/MeasurableBlockMinimizer`), which agrees with `phi` on the
  good event by `isBlockInterpolation_unique`, together with measurability of that event.
* `hcov` — exact covariance of the gradients of the block interpolants under every physical
  similarity, for a measure-preserving action on uniform grids, on the good event (where
  block interpolants are unique, so `phi` is determined by its specification).
* `hcopies` — grid independence of the marked difference field, `s:prop:gridindependence`.
* `hconv` — almost-sure convergence of every pairwise difference of the interpolants along
  `ms`, `s:prop:limit`.
* `hpatch` — patch-energy convergence of the gradients along `ms`, `s:prop:limit`(d).
* `hharm` — full variational and discrete harmonicity of the marked limit,
  `s:prop:limit`(a) and `s:eq:freeorth`.
* `hsub` — centroid sublinearity of the marked limit, `s:eq:sublinear`.
* `hdens` — measurability of the concrete rooted densities and neighbourhood errors.
* `hnbr` — convergence in probability of the neighbourhood errors, `s:prop:limit`(d).
* `hspec` — finite expected specific energy of every stage and expected specific-energy
  convergence, `s:eq:limitnorm`.

Discharged outright from the checked corpus: the spatial maximal inequality
`s:prop:maximal` (`spatialMaximalBound_of_massTransport`, from `hν` and `hFE` alone); the
vacuity guard (6); the collapse of the `∀ σ` quantifier in (7); the boundary-mask clause of
(5); root normalization everywhere; both covariance clauses (1)(2) from `hcov`;
measurability (3) and finiteness (4) of the unmarked specific energy; the block-interpolant
clause of (7), including uniqueness; and the representative-independent half of the
sublinearity clause. -/
theorem harmonicCoordinateConclusions_of_named_inputs (ν : Measure Env)
    [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (ms : ℕ → ℕ) (hms : StrictMono ms)
   
    (hmeas : ∀ m n : ℕ, Measurable fun ω : MarkedEnvironment => gatedApproximant m ω n)
    (hcov : ApproximantGradientCovariant ms)
    (hcopies : DifferenceFieldGridIndependent ν ms)
    (hconv : MarkedDifferencesConverge ν ms) (hpatch : MarkedPatchConvergence ν ms)
    (hharm : MarkedHarmonicity ν ms) (hsub : MarkedCentroidSublinearity ν ms)
    (hdens : MarkedDensityMeasurability ν ms) (hnbr : MarkedNeighborhoodConvergence ν ms)
    (hspec : MarkedSpecificEnergyConvergence ν ms) :
    HarmonicCoordinateConclusions ν :=
  ⟨harmonicCellField ms hmeas,
    isHarmonicCoordinate_harmonicCellField ν hν hFE ms hms hmeas hcov hcopies hconv hpatch
      hharm hsub hdens hnbr hspec⟩

end ReflectedGMS.HarmonicCoordinateAssembly
