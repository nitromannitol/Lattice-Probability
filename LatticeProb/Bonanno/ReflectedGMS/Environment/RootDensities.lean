/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.RootDensities at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients

/-!
Deterministic boundary-masked roots and rooted densities from the manuscript.
The exception mask is the union of every cell frontier, rather than merely the
frontier of a cell selected by an interior-membership test.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.RootDensities

variable {V : Type*}

/-- The exceptional set for rooted observables: the union of all cell frontiers, together with the
uncovered set. A point is masked even when it also belongs to another cell's interior.

The uncovered part is what the singular-set manuscript's Definition 1.1(ii) makes possible: cells
need only cover the complement of an `H¹`-null set, so a point may lie in no cell at all. It is the
manuscript's own convention that rooted cell functionals "are defined to be zero when the root is
uncovered or belongs to a cell boundary". Under the earlier full-covering hypothesis the added part
is empty, so this is the same mask as before on that class of environments.

The mask uses the canonical `uncoveredSet F`, determined by `F`, and never a chosen singular
witness: witnesses come from an existential and are not measurable functions of the environment. -/
def boundaryMask (F : IndexedCells V) : Set Plane :=
  (⋃ v : V, frontier (F.cell v : Set Plane)) ∪ uncoveredSet F

/-- Interior membership, packaged separately for the root laws. -/
def IsInteriorRoot (F : IndexedCells V) (z : Plane) (v : V) : Prop :=
  z ∈ interior (F.cell v : Set Plane)

/-- Outside the global boundary mask, choose the unique cell whose interior
contains the point. The second branch only handles malformed indexed families;
under \`Geometry F\` it is unreachable. -/
noncomputable def rootAt (F : IndexedCells V) (z : Plane) : Option V := by
  classical
  exact if hz : z ∈ boundaryMask F then none
    else if hroot : ∃! v, IsInteriorRoot F z v then some hroot.exists.choose
    else none

theorem existsUnique_interiorRoot_of_not_mem_boundaryMask [Countable V]
    (F : IndexedCells V) (hF : Geometry F) {z : Plane}
    (hz : z ∉ boundaryMask F) :
    ∃! v, IsInteriorRoot F z v := by
  rcases hF with ⟨_, _, _, hinteriors, _, _, _, _⟩
  have hzcover : z ∈ ⋃ v, (F.cell v : Set Plane) := by
    by_contra hzc
    exact hz (Set.mem_union_right _ (Set.mem_compl hzc))
  rcases Set.mem_iUnion.mp hzcover with ⟨v, hzv⟩
  have hzfrontier : z ∉ frontier (F.cell v : Set Plane) := by
    intro hzfv
    exact hz (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨v, hzfv⟩))
  have hzint : IsInteriorRoot F z v := by
    have hclosed : IsClosed (F.cell v : Set Plane) :=
      (F.cell v).isCompact.isClosed
    rw [IsInteriorRoot]
    rw [frontier, hclosed.closure_eq] at hzfrontier
    exact Classical.byContradiction (fun hznot => hzfrontier ⟨hzv, hznot⟩)
  refine ⟨v, hzint, ?_⟩
  intro w hzw
  by_contra hwv
  have hd : Disjoint (interior (F.cell w : Set Plane))
      (interior (F.cell v : Set Plane)) := hinteriors hwv
  exact (Set.disjoint_left.1 hd hzw) hzint

theorem rootAt_eq_none_of_mem_boundaryMask (F : IndexedCells V) {z : Plane}
    (hz : z ∈ boundaryMask F) :
    rootAt F z = none := by
  simp [rootAt, hz]

theorem rootAt_eq_some_of_not_mem_boundaryMask [Countable V]
    (F : IndexedCells V) (hF : Geometry F) {z : Plane}
    (hz : z ∉ boundaryMask F) :
    ∃ v, rootAt F z = some v ∧ IsInteriorRoot F z v := by
  let hroot := existsUnique_interiorRoot_of_not_mem_boundaryMask F hF hz
  let v := hroot.exists.choose
  have hv : IsInteriorRoot F z v := hroot.exists.choose_spec
  refine ⟨v, ?_, hv⟩
  simp only [rootAt, hz, ↓reduceDIte, hroot, v]

theorem rootAt_eq_none_iff [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : Plane) :
    rootAt F z = none ↔ z ∈ boundaryMask F := by
  constructor
  · intro hnone
    by_contra hz
    rcases rootAt_eq_some_of_not_mem_boundaryMask F hF hz with ⟨v, hv, _⟩
    rw [hv] at hnone
    contradiction
  · exact rootAt_eq_none_of_mem_boundaryMask F

theorem rootAt_eq_some_iff [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : Plane) (v : V) :
    rootAt F z = some v ↔
      z ∉ boundaryMask F ∧ IsInteriorRoot F z v := by
  constructor
  · intro h
    have hz : z ∉ boundaryMask F := by
      intro hz
      rw [rootAt_eq_none_of_mem_boundaryMask F hz] at h
      contradiction
    refine ⟨hz, ?_⟩
    let hroot := existsUnique_interiorRoot_of_not_mem_boundaryMask F hF hz
    have hdef : rootAt F z = some hroot.exists.choose := by
      simp [rootAt, hz, hroot]
    rw [hdef] at h
    have hv : hroot.exists.choose = v := Option.some.inj h
    rw [← hv]
    exact hroot.exists.choose_spec
  · rintro ⟨hz, hv⟩
    let hroot := existsUnique_interiorRoot_of_not_mem_boundaryMask F hF hz
    have hvuniq : hroot.exists.choose = v :=
      hroot.unique hroot.exists.choose_spec hv
    simp [rootAt, hz, hroot, hvuniq]

/-- Total conductance at a vertex. This is the existing exact
manuscript quantity on ConductanceGraph, exposed here with the cell-family
argument used by the other densities. -/
noncomputable def pi (F : IndexedCells V) (v : V) : ℝ :=
  F.graph.pi v

/-- Total reciprocal conductance at a vertex. Real inversion sends zero to
zero, so non-neighbors contribute zero exactly as in the manuscript sum over
neighbors. Geometry's local finiteness makes this a finite-support sum. -/
noncomputable def piStar (F : IndexedCells V) (v : V) : ℝ :=
  ∑' w : V, (F.graph.c v w)⁻¹

/-- The vertex integrand in (FE), lifted to ENNReal so that its expectation
retains the possibility of infinity:
d_H^2 / a_H * (pi(H) + piStar(H)). -/
noncomputable def finiteEnergyDensity (F : IndexedCells V) (v : V) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) /
      ENNReal.ofReal (StatementIngredients.cellArea F v) *
    (ENNReal.ofReal (pi F v) + ENNReal.ofReal (piStar F v))

/-- The finite-specific-energy integrand for a vector-valued coordinate:
\`(2 a_H)^{-1} sum_{H' ~ H} c(H,H') |Phi(H')-Phi(H)|^2\`. -/
noncomputable def specificEnergyDensity (F : IndexedCells V)
    (Phi : V → Plane) (v : V) : ℝ≥0∞ :=
  (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
      ENNReal.ofReal (‖Phi w - Phi v‖ ^ 2)) /
    (2 * ENNReal.ofReal (StatementIngredients.cellArea F v))

/-- Boundary-masked FE density. -/
noncomputable def rootedFiniteEnergyDensity
    (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  (rootAt F z).elim 0 (finiteEnergyDensity F)

/-- Boundary-masked specific-energy density. -/
noncomputable def rootedSpecificEnergyDensity
    (F : IndexedCells V) (Phi : V → Plane) (z : Plane) : ℝ≥0∞ :=
  (rootAt F z).elim 0 (specificEnergyDensity F Phi)

/-- Boundary-masked ordinary-edge bracket density \`Gamma(H_z)\`.
The underlying vertex observable is exactly
\`StatementIngredients.bracketDensity\`; it is not duplicated here. -/
noncomputable def rootedGamma
    (F : IndexedCells V) (Phi : V → Plane) (z : Plane) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (rootAt F z).elim 0 (StatementIngredients.bracketDensity F Phi)

theorem rootedFiniteEnergyDensity_eq_zero_of_mem_boundaryMask
    (F : IndexedCells V) {z : Plane} (hz : z ∈ boundaryMask F) :
    rootedFiniteEnergyDensity F z = 0 := by
  simp [rootedFiniteEnergyDensity, rootAt_eq_none_of_mem_boundaryMask F hz]

theorem rootedSpecificEnergyDensity_eq_zero_of_mem_boundaryMask
    (F : IndexedCells V) (Phi : V → Plane) {z : Plane}
    (hz : z ∈ boundaryMask F) :
    rootedSpecificEnergyDensity F Phi z = 0 := by
  simp [rootedSpecificEnergyDensity, rootAt_eq_none_of_mem_boundaryMask F hz]

end ReflectedGMS.RootDensities
