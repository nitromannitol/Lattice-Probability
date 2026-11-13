/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralGMSSpecialization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Util.AssertNoSorry

/-!
# Corollary 21.1: with `Ssing = ∅` Definition 1.1 + (LCS) is exactly the GMS class

Manuscript: "Reflected scale-free invariance principle — cell configurations with singularities"
(`work/general/manuscript-text.txt`), Definition 1.1 and (LCS) at lines 53–80, **Corollary 21.1
(Recovery of GMS Theorem 1.16)** at lines 2446–2458.

The proof of Corollary 21.1 reads: *with `Ssing = ∅`, Definition 1.1 says that the cells cover `ℂ`,
are spatially locally finite, are compact and connected with nonempty interiors and pairwise
zero-area intersections, and carry an arbitrary symmetric adjacency relation between distinct
intersecting cells with finite positive symmetric conductances.  These are exactly the objects in
[GMS, Definition 1.15].  The condition (LCS) is now their connectedness-along-segments hypothesis,
with the same simultaneous quantifiers.*

This file formalizes that sentence at the level of a single cell configuration.

* `GMSGeometry C` — the deterministic hypotheses of GMS Theorem 1.16 (Definition 1.15 together with
  its segment condition), written out verbatim: connected compact cells (compactness is carried by
  `NonemptyCompacts`), nonempty interiors, pairwise Lebesgue-null intersections, **full** covering of
  the plane, spatial local finiteness (mathlib's `LocallyFinite` for the family of cells),
  adjacency ⇒ intersection, and `SegmentConnected` — `H(L)` connected for **every** horizontal or
  vertical compact segment `L`, with no avoidance condition.  Symmetry, loop-freeness and finite
  positive conductances are carried by `CellConfiguration` itself, exactly as for the general class.
* `generalGeometry_of_gmsGeometry` — every GMS configuration satisfies Definition 1.1 + (LCS), with
  the witness `Ssing = ∅` (`emptySingularSet`).
* `gmsGeometry_iff` — **Corollary 21.1, deterministic part**: `GMSGeometry C` holds **iff** `C`
  satisfies Definition 1.1 + (LCS) with a witness whose singular set is empty.  This is
  `GeneralGeometry C` clause for clause, with the singular-set clause strengthened by `S.sing = ∅`.
* `locallyFinite_cells_iff` — GMS phrase spatial local finiteness as "each compact set meets
  finitely many cells"; this is equivalent to the pointwise-neighbourhood form used here.
* `GMSGeometry.locallyFiniteGraph` — on the GMS class graph local finiteness is a consequence
  (neighbours of `H` meet the compact cell `H`), so GMS configurations are `IndexedCells`.
* `Code.ValidGMS`, `Code.validGeneral_of_validGMS` and
  `GeneralLaws.supportedOnValidGeneral_of_ae_validGMS` — the same inclusion at the level of codes
  and environment laws: a law carried by GMS codes is carried by general codes, so the main theorems
  of the general manuscript apply to it (the "include" half of Corollary 21.1).

The probabilistic half of Corollary 21.1 (recurrence of the ordinary walk, identification of the
reflected path with the ordinary path) is not part of this file.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace ReflectedGMS

namespace CellConfiguration

variable {V : Type*} (C : CellConfiguration V)

/-- **The GMS segment condition**: `H(L)` is connected for every horizontal or vertical compact
segment `L ⊂ ℂ`, with no condition on `L`.  Endpoints are arbitrary reals, exactly as in
`LineConnectedOff`. -/
def SegmentConnected : Prop :=
  (∀ a b y : ℝ, C.InducedConnected (horizontal a b y)) ∧
    ∀ x a b : ℝ, C.InducedConnected (vertical x a b)

/-- (LCS) relative to the empty singular set is the GMS segment condition. -/
theorem lineConnectedOff_empty_iff : C.LineConnectedOff ∅ ↔ C.SegmentConnected :=
  ⟨fun h => ⟨fun a b y => h.1 a b y (Set.disjoint_empty _),
      fun x a b => h.2 x a b (Set.disjoint_empty _)⟩,
    fun h => ⟨fun a b y _ => h.1 a b y, fun x a b _ => h.2 x a b⟩⟩

/-- Spatial local finiteness in the pointwise form (mathlib's `LocallyFinite` for the family of
cells) is equivalent to GMS's form: every compact subset of the plane meets only finitely many
cells. -/
theorem locallyFinite_cells_iff :
    LocallyFinite (fun v => (C.cell v : Set Plane)) ↔
      ∀ K : Set Plane, IsCompact K → {v | C.Hits K v}.Finite := by
  constructor
  · intro h K hK
    exact h.finite_nonempty_inter_compact hK
  · intro h z
    exact ⟨Metric.closedBall z 1, Metric.closedBall_mem_nhds z one_pos,
      h _ (isCompact_closedBall z 1)⟩

/-- **The empty singular-set witness** of a configuration whose cells cover the plane and are
spatially locally finite. -/
noncomputable def emptySingularSet (hcov : (⋃ v, (C.cell v : Set Plane)) = Set.univ)
    (hlf : LocallyFinite (fun v => (C.cell v : Set Plane))) : SingularSet C where
  sing := ∅
  isClosed_sing := isClosed_empty
  hausdorff_sing := measure_empty
  cover := by
    rw [hcov]
    exact Set.subset_univ _
  locallyFinite := fun z _ => hlf z

@[simp] theorem sing_emptySingularSet (hcov : (⋃ v, (C.cell v : Set Plane)) = Set.univ)
    (hlf : LocallyFinite (fun v => (C.cell v : Set Plane))) :
    (C.emptySingularSet hcov hlf).sing = ∅ := rfl

namespace SingularSet

variable {C}

/-- A witness with empty singular set forces the cells to cover the plane. -/
theorem iUnion_cell_eq_univ_of_sing_eq_empty (S : SingularSet C) (hS : S.sing = ∅) :
    (⋃ v, (C.cell v : Set Plane)) = Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  have h := S.cover
  rwa [hS, Set.compl_empty] at h

/-- A witness with empty singular set forces spatial local finiteness everywhere. -/
theorem locallyFinite_of_sing_eq_empty (S : SingularSet C) (hS : S.sing = ∅) :
    LocallyFinite (fun v => (C.cell v : Set Plane)) := fun z =>
  S.locallyFinite z (by rw [hS]; exact Set.notMem_empty z)

end SingularSet

end CellConfiguration

open CellConfiguration

/-- **The deterministic hypotheses of GMS Theorem 1.16** ([GMS, Definition 1.15] together with its
connectedness-along-segments condition), as described in the proof of Corollary 21.1.

Clause order: cells connected; interiors nonempty; distinct cells meet in a Lebesgue-null set; the
cells cover the plane; spatial local finiteness (every point has a neighbourhood meeting only
finitely many cells — equivalently every compact set meets finitely many, `locallyFinite_cells_iff`);
adjacent cells intersect; `H(L)` is connected for every horizontal or vertical compact segment.
Compactness is carried by `NonemptyCompacts`; symmetry, loop-freeness and finite positive
conductances by `CellConfiguration`. -/
def GMSGeometry {V : Type*} (C : CellConfiguration V) : Prop :=
  (∀ v, IsConnected (C.cell v : Set Plane)) ∧
    (∀ v, (interior (C.cell v : Set Plane)).Nonempty) ∧
    (∀ ⦃v w⦄, v ≠ w → volume ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)) = 0) ∧
    (⋃ v, (C.cell v : Set Plane)) = Set.univ ∧
    LocallyFinite (fun v => (C.cell v : Set Plane)) ∧
    (∀ ⦃v w⦄, C.graph.Adj v w → ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)).Nonempty) ∧
    C.SegmentConnected

namespace GMSGeometry

variable {V : Type*} {C : CellConfiguration V}

theorem iUnion_cell (h : GMSGeometry C) : (⋃ v, (C.cell v : Set Plane)) = Set.univ := h.2.2.2.1

theorem locallyFinite (h : GMSGeometry C) : LocallyFinite (fun v => (C.cell v : Set Plane)) :=
  h.2.2.2.2.1

theorem segmentConnected (h : GMSGeometry C) : C.SegmentConnected := h.2.2.2.2.2.2

/-- The empty singular-set witness of a GMS configuration. -/
noncomputable def singularSet (h : GMSGeometry C) : SingularSet C :=
  C.emptySingularSet h.iUnion_cell h.locallyFinite

@[simp] theorem sing_singularSet (h : GMSGeometry C) : h.singularSet.sing = ∅ := rfl

/-- On the GMS class **graph local finiteness is a consequence**: the neighbours of `v` meet the
compact cell of `v`, and spatial local finiteness lets only finitely many cells do so. -/
theorem locallyFiniteGraph (h : GMSGeometry C) : C.LocallyFiniteGraph := by
  intro v
  refine Set.Finite.subset
    (h.locallyFinite.finite_nonempty_inter_compact (C.cell v).isCompact) ?_
  intro w hw
  have hpos : 0 < C.c v w := lt_of_le_of_ne (C.c_nonneg v w) (Ne.symm hw)
  have hne := h.2.2.2.2.2.1 (show C.graph.Adj v w from hpos)
  rw [Set.inter_comm] at hne
  exact hne

end GMSGeometry

/-- **Every GMS configuration satisfies Definition 1.1 and (LCS)**, with the witness `Ssing = ∅`. -/
theorem generalGeometry_of_gmsGeometry {V : Type*} {C : CellConfiguration V}
    (h : GMSGeometry C) : GeneralGeometry C :=
  ⟨h.1, h.2.1, h.2.2.1,
    ⟨h.singularSet, (C.lineConnectedOff_empty_iff).2 h.segmentConnected⟩, h.2.2.2.2.2.1⟩

/-- **Corollary 21.1 (deterministic part): `Ssing = ∅` recovers GMS exactly.**

A cell configuration satisfies the hypotheses of GMS Theorem 1.16 if and only if it satisfies
Definition 1.1 and (LCS) — clause for clause `GeneralGeometry C` — with a singular-set witness whose
singular set is empty. -/
theorem gmsGeometry_iff {V : Type*} (C : CellConfiguration V) :
    GMSGeometry C ↔
      (∀ v, IsConnected (C.cell v : Set Plane)) ∧
        (∀ v, (interior (C.cell v : Set Plane)).Nonempty) ∧
        (∀ ⦃v w⦄, v ≠ w → volume ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)) = 0) ∧
        (∃ S : SingularSet C, S.sing = ∅ ∧ C.LineConnectedOff S.sing) ∧
        (∀ ⦃v w⦄, C.graph.Adj v w →
          ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)).Nonempty) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1,
      ⟨h.singularSet, rfl, (C.lineConnectedOff_empty_iff).2 h.segmentConnected⟩, h.2.2.2.2.2.1⟩
  · rintro ⟨h1, h2, h3, ⟨S, hS, hL⟩, h5⟩
    rw [hS] at hL
    exact ⟨h1, h2, h3, S.iUnion_cell_eq_univ_of_sing_eq_empty hS,
      S.locallyFinite_of_sing_eq_empty hS, h5, (C.lineConnectedOff_empty_iff).1 hL⟩

/-- The same statement with `GeneralGeometry` itself on the right: GMS configurations are exactly
the configurations satisfying Definition 1.1 + (LCS) that admit an empty singular-set witness
satisfying (LCS). -/
theorem gmsGeometry_iff_generalGeometry {V : Type*} (C : CellConfiguration V) :
    GMSGeometry C ↔ GeneralGeometry C ∧ ∃ S : SingularSet C, S.sing = ∅ ∧ C.LineConnectedOff S.sing := by
  rw [gmsGeometry_iff]
  constructor
  · rintro ⟨h1, h2, h3, ⟨S, hS, hL⟩, h5⟩
    exact ⟨⟨h1, h2, h3, ⟨S, hL⟩, h5⟩, S, hS, hL⟩
  · rintro ⟨⟨h1, h2, h3, -, h5⟩, hS⟩
    exact ⟨h1, h2, h3, hS, h5⟩

/-! ## The inclusion at the level of codes and environment laws -/

namespace Code

/-- **Pathwise validity for the GMS class**: the hypotheses of GMS Theorem 1.16 for the decoded
configuration, and least rational interior labels (as in `ValidGeneral`). -/
def ValidGMS (r : RawCode) : Prop :=
  ∃ h : RawAdmissible r, GMSGeometry (rawConfig r h) ∧ CanonicalLabels r

/-- Every GMS code is a code of the general manuscript. -/
theorem validGeneral_of_validGMS {r : RawCode} (h : ValidGMS r) : ValidGeneral r :=
  let ⟨hr, hg, hl⟩ := h
  ⟨hr, generalGeometry_of_gmsGeometry hg, hl⟩

end Code

namespace GeneralLaws

/-- **Corollary 21.1, "the assumptions of the main theorems include every GMS configuration"**: an
environment law carried by GMS codes is carried by codes satisfying Definition 1.1 + (LCS). -/
theorem supportedOnValidGeneral_of_ae_validGMS {P : Measure Code.RawCode}
    (hP : ∀ᵐ r ∂P, Code.ValidGMS r) : SupportedOnValidGeneral P :=
  hP.mono fun _ hr => Code.validGeneral_of_validGMS hr

end GeneralLaws

end ReflectedGMS

assert_no_sorry ReflectedGMS.generalGeometry_of_gmsGeometry
assert_no_sorry ReflectedGMS.gmsGeometry_iff
assert_no_sorry ReflectedGMS.gmsGeometry_iff_generalGeometry
assert_no_sorry ReflectedGMS.CellConfiguration.lineConnectedOff_empty_iff
assert_no_sorry ReflectedGMS.CellConfiguration.locallyFinite_cells_iff
assert_no_sorry ReflectedGMS.GMSGeometry.locallyFiniteGraph
assert_no_sorry ReflectedGMS.Code.validGeneral_of_validGMS
assert_no_sorry ReflectedGMS.GeneralLaws.supportedOnValidGeneral_of_ae_validGMS

#print axioms ReflectedGMS.generalGeometry_of_gmsGeometry
#print axioms ReflectedGMS.gmsGeometry_iff
#print axioms ReflectedGMS.gmsGeometry_iff_generalGeometry
#print axioms ReflectedGMS.CellConfiguration.lineConnectedOff_empty_iff
#print axioms ReflectedGMS.CellConfiguration.locallyFinite_cells_iff
#print axioms ReflectedGMS.GMSGeometry.locallyFiniteGraph
#print axioms ReflectedGMS.Code.validGeneral_of_validGMS
#print axioms ReflectedGMS.GeneralLaws.supportedOnValidGeneral_of_ae_validGMS
