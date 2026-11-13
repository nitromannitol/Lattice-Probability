/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.BlockInterpolantExistence
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CentroidTraceLocalEnergy

/-!
# Finite-energy centroid trace on each selected patch

`Corrector/BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry` produces the
manuscript block interpolant `φ_m` (`s:eq:pinned`) from exactly one remaining per-square
analytic input `hfin`: for every `κ`-selected dyadic square `S` there is **some** field
`u : 𝓗(S) → ℝ²` with

* `vectorEnergy (restrictGraph F.graph (patchVertices F S)) u < ∞`, and
* `u v = cellCentroid F v` for every cell `v` meeting `∂S`.

This module discharges that input from the manuscript's own local energy bound
`W(R) < ∞` of Corollary `s:cor:spatialbounds` / `s:eq:Wbound`, i.e. from

`SpatialDiameterCellBounds F : ∀ R, Summable (fun v ∈ 𝓗(B̄_R) => d_v² (π(v) + π*(v)))`,

and hence makes `exists_isBlockInterpolation_of_geometry` and
`isBlockInterpolation_phi_of_geometry` conditional on that single environmental quantity
instead of on a per-square existential.

## The witness is the centroid trace itself, not a cut-off field

A cut-off field (centroid values on `∂S`, a constant in the interior of the patch) is *not*
a cheaper witness.  Its patch energy contains, for every boundary cell `v` and every patch
neighbour `w` of `v` outside `∂S`, the term `c(v,w)|b_v − z₀|²`, and `|b_v − z₀|` is of the
order of the side of `S`, not of the cell diameter `d_v`.  Summing those terms requires
`∑_{v ∈ ∂S} π(v) < ∞`, which is *not* implied by — and is in general much stronger than —
the manuscript's local mass `∑ d_v² π(v) < ∞`.  By contrast the centroid trace `b` itself has
increments controlled by diameters along every edge, because adjacent cells intersect
(`dist_cellCentroid_le_add_diam`), and `s:eq:basepatch` bounds its whole patch energy by
`2 ∑_{v ∈ 𝓗(S)} d_v² π(v)`.  So the honest witness is `b` restricted to the patch, and the
real content of this module is that the manuscript's *global* bound `W(R) < ∞` restricts to
every selected square at once.

## `hfin` is genuinely an environmental hypothesis

`vectorEnergy_boundaryTrace_lt_top_of_patchExtension` records the converse: the existence of
any admissible `u` already forces the centroid trace to have finite energy on the graph
restricted to the boundary cells `∂S`, since `u` is pinned to `b` at both endpoints of every
edge inside `∂S`.  That quantity is a pure function of the conductances and the cells, on
which `Geometry F` imposes no bound whatsoever.  Hence `hfin` cannot be derived from
`Geometry F` alone, and some environmental input of the strength of `s:eq:Wbound` is
necessary, not merely convenient.
-/

set_option autoImplicit false

open MeasureTheory Set

open scoped ENNReal

namespace ReflectedGMS.PatchCentroidTraceFiniteEnergy

open StatementIngredients DyadicApproximation

variable {V : Type*}

/-! ### Monotonicity of the restricted energy in the vertex set -/

/-- Scalar restricted energy is monotone along an inclusion of vertex sets: every ordered
edge of the smaller restricted graph is an ordered edge of the larger one, with the same
conductance and the same increment. -/
theorem energyENN_restrictGraph_mono (G : ReflectedWalk.ConductanceGraph V) {A B : Set V}
    (hAB : A ⊆ B) (f : B → ℝ) :
    energyENN (restrictGraph G A) (fun v => f (Set.inclusion hAB v)) ≤
      energyENN (restrictGraph G B) f := by
  have hinj : Function.Injective (Prod.map (Set.inclusion hAB) (Set.inclusion hAB)) :=
    (Set.inclusion_injective hAB).prodMap (Set.inclusion_injective hAB)
  have hterm : ∀ p : A × A,
      ENNReal.ofReal ((restrictGraph G A).gradSq (fun v => f (Set.inclusion hAB v)) p) =
        ENNReal.ofReal ((restrictGraph G B).gradSq f
          (Prod.map (Set.inclusion hAB) (Set.inclusion hAB) p)) := fun _ => rfl
  have hsum :
      (∑' p : A × A,
          ENNReal.ofReal ((restrictGraph G A).gradSq (fun v => f (Set.inclusion hAB v)) p)) ≤
        ∑' q : B × B, ENNReal.ofReal ((restrictGraph G B).gradSq f q) := by
    calc (∑' p : A × A,
            ENNReal.ofReal ((restrictGraph G A).gradSq (fun v => f (Set.inclusion hAB v)) p))
        = ∑' p : A × A, ENNReal.ofReal ((restrictGraph G B).gradSq f
            (Prod.map (Set.inclusion hAB) (Set.inclusion hAB) p)) := tsum_congr hterm
      _ ≤ ∑' q : B × B, ENNReal.ofReal ((restrictGraph G B).gradSq f q) :=
            ENNReal.tsum_comp_le_tsum_of_injective hinj
              (fun q : B × B => ENNReal.ofReal ((restrictGraph G B).gradSq f q))
  exact ENNReal.div_le_div_right hsum 2

/-- The plane-valued form of `energyENN_restrictGraph_mono`. -/
theorem vectorEnergy_restrictGraph_mono (G : ReflectedWalk.ConductanceGraph V) {A B : Set V}
    (hAB : A ⊆ B) (f : B → Plane) :
    vectorEnergy (restrictGraph G A) (fun v => f (Set.inclusion hAB v)) ≤
      vectorEnergy (restrictGraph G B) f :=
  Finset.sum_le_sum fun i _ => energyENN_restrictGraph_mono G hAB (fun v => f v i)

/-! ### The manuscript local mass `∑ d² π` and the spatial bound `W(R) < ∞` -/

/-- The manuscript's `π`-only local diameter mass `∑_{H ∈ A} d_H² π(H)` of a set of cells,
in summable form. -/
def LocalDiameterPiMass (F : IndexedCells V) (A : Set V) : Prop :=
  Summable fun v : A => Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1

/-- The combined local mass `∑_{H ∈ A} d_H² (π(H) + π*(H))` of a set of cells, which is the
summand of the manuscript quantity `W` in `s:eq:Wbound`. -/
def LocalDiameterCellMass (F : IndexedCells V) (A : Set V) : Prop :=
  Summable fun v : A =>
    Metric.diam (F.cell v.1 : Set Plane) ^ 2 *
      (RootDensities.pi F v.1 + RootDensities.piStar F v.1)

/-- **`s:eq:Wbound`, finite-radius half.**  `W(R) = ∑_{H ∈ 𝓗(B̄_R)} d_H² (π(H) + π*(H)) < ∞`
for every radius.  All summands are nonnegative, so summability is exactly finiteness of
`W(R)`.  This is the conclusion of Corollary `s:cor:spatialbounds`; its almost-sure producer
(the dyadic maximal-function proposition `s:prop:maximal`) is a separate obligation. -/
def SpatialDiameterCellBounds (F : IndexedCells V) : Prop :=
  ∀ R : ℝ, LocalDiameterCellMass F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}

/-- The `π`-only variant of `SpatialDiameterCellBounds`. -/
def SpatialDiameterPiBounds (F : IndexedCells V) : Prop :=
  ∀ R : ℝ, LocalDiameterPiMass F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}

theorem localDiameterPiMass_of_cellMass [Countable V] (F : IndexedCells V) (A : Set V)
    (h : LocalDiameterCellMass F A) : LocalDiameterPiMass F A :=
  summable_localDiameterPi_of_combined F A h

theorem spatialDiameterPiBounds_of_cellBounds [Countable V] (F : IndexedCells V)
    (h : SpatialDiameterCellBounds F) : SpatialDiameterPiBounds F :=
  fun R => localDiameterPiMass_of_cellMass F _ (h R)

/-! ### Restricting the spatial bound to a single patch -/

/-- A cell meeting a set meets any larger set. -/
theorem hits_mono (F : IndexedCells V) {A B : Set Plane} (hAB : A ⊆ B) {v : V}
    (hv : Hits F A v) : Hits F B v := by
  obtain ⟨z, hzc, hzA⟩ := hv
  exact ⟨z, hzc, hAB hzA⟩

/-- Local mass is inherited by subsets of cells: all summands are the same and the inclusion
is injective. -/
theorem localDiameterPiMass_mono (F : IndexedCells V) {A B : Set V} (hAB : B ⊆ A)
    (h : LocalDiameterPiMass F A) : LocalDiameterPiMass F B :=
  (h.comp_injective (Set.inclusion_injective hAB)).congr fun _ => rfl

theorem localDiameterCellMass_mono (F : IndexedCells V) {A B : Set V} (hAB : B ⊆ A)
    (h : LocalDiameterCellMass F A) : LocalDiameterCellMass F B :=
  (h.comp_injective (Set.inclusion_injective hAB)).congr fun _ => rfl

/-- Every rectangle patch sits inside the cells meeting some closed ball, because a bounded
closed axis-parallel rectangle is contained in a closed ball. -/
theorem exists_closedBall_patchVertices_subset (F : IndexedCells V) (Q : Rectangle) :
    ∃ R : ℝ, patchVertices F Q ⊆ {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} := by
  obtain ⟨R, hR⟩ := (rectangle_carrier_isBounded Q).subset_closedBall (0 : Plane)
  exact ⟨R, fun _ hv => hits_mono F hR hv⟩

/-- **The manuscript bound restricts to every patch simultaneously.** -/
theorem localDiameterPiMass_patchVertices (F : IndexedCells V)
    (hW : SpatialDiameterPiBounds F) (Q : Rectangle) :
    LocalDiameterPiMass F (patchVertices F Q) := by
  obtain ⟨R, hR⟩ := exists_closedBall_patchVertices_subset F Q
  exact localDiameterPiMass_mono F hR (hW R)

/-! ### The finite-energy field with the exact centroid boundary trace -/

/-- **The `hfin` input of `exists_isBlockInterpolation_of_geometry`, on one rectangle.**  The
witness is the centroid trace itself: its boundary agreement is definitional, and its patch
energy is finite by `s:eq:basepatch`. -/
theorem exists_finiteEnergy_centroidBoundaryTrace_of_localPiMass [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Q : Rectangle)
    (hmass : LocalDiameterPiMass F (patchVertices F Q)) :
    ∃ u : patchVertices F Q → Plane,
      vectorEnergy (restrictGraph F.graph (patchVertices F Q)) u < ∞ ∧
        ∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → u v = cellCentroid F v.1 :=
  ⟨fun v => cellCentroid F v.1, vectorEnergy_cellCentroid_patch_lt_top F hF Q hmass,
    fun _ _ => rfl⟩

/-- The same from the manuscript's global spatial bound. -/
theorem exists_finiteEnergy_centroidBoundaryTrace_of_spatialBounds [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hW : SpatialDiameterPiBounds F) (Q : Rectangle) :
    ∃ u : patchVertices F Q → Plane,
      vectorEnergy (restrictGraph F.graph (patchVertices F Q)) u < ∞ ∧
        ∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → u v = cellCentroid F v.1 :=
  exists_finiteEnergy_centroidBoundaryTrace_of_localPiMass F hF Q
    (localDiameterPiMass_patchVertices F hW Q)

/-- **`hfin` for all `κ`-selected squares at once**, in the exact shape consumed by
`BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry`. -/
theorem finiteEnergy_centroidBoundaryTrace_selected [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hW : SpatialDiameterPiBounds F)
    (D : Grid) (m : ℕ) :
    ∀ s : SquareIndex, Selected F D (m : ℝ) s →
      ∃ u : patchVertices F (square D s) → Plane,
        vectorEnergy (restrictGraph F.graph (patchVertices F (square D s))) u < ∞ ∧
          ∀ v : patchVertices F (square D s), v.1 ∈ boundaryVertices F (square D s) →
            u v = cellCentroid F v.1 :=
  fun s _ => exists_finiteEnergy_centroidBoundaryTrace_of_spatialBounds F hF hW (square D s)

/-! ### The block interpolant, now conditional only on the spatial energy bound -/

/-- **Existence of the manuscript block interpolant `φ_m` (`s:eq:pinned`)** under the
geometry of the cells and the manuscript spatial energy bound `s:eq:Wbound`. -/
theorem exists_isBlockInterpolation_of_spatialPiBounds [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hW : SpatialDiameterPiBounds F)
    (D : Grid) (m : ℕ) :
    ∃ f : V → Plane, IsBlockInterpolation F D m f :=
  BlockInterpolantExistence.exists_isBlockInterpolation_of_geometry F hF D m
    (finiteEnergy_centroidBoundaryTrace_selected F hF hW D m)

/-- The same from the combined `π + π*` bound, which is the literal `W` of `s:eq:Wbound`. -/
theorem exists_isBlockInterpolation_of_spatialCellBounds [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hW : SpatialDiameterCellBounds F)
    (D : Grid) (m : ℕ) :
    ∃ f : V → Plane, IsBlockInterpolation F D m f :=
  exists_isBlockInterpolation_of_spatialPiBounds F hF
    (spatialDiameterPiBounds_of_cellBounds F hW) D m

/-- The consumer form of `HarmonicMainStatement.ApproximationConclusions` from the literal
manuscript quantity `W`. -/
theorem isBlockInterpolation_phi_of_spatialCellBounds [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (hW : SpatialDiameterCellBounds F)
    (D : Grid) (m : ℕ) :
    IsBlockInterpolation F D m (phi F D m) :=
  phi_spec_of_exists F D m (exists_isBlockInterpolation_of_spatialCellBounds F hF hW D m)

/-! ### The input is not free: a necessary condition for `hfin` -/

end ReflectedGMS.PatchCentroidTraceFiniteEnergy
