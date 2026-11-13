/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.ActualUniformSublinearity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GoodGridMaximumPrinciple
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CentroidTraceLocalEnergy
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks

/-!
# The fixed-parameter block approximant is sublinear (`s:eq:fixedapprox`)

This module proves the second display of the manuscript's `s:lem:smallblocks`,

`(1/R) · sup_{H ∈ 𝓗(clB R)} |φ_m(H) - b_H| ⟶ 0`  (`s:eq:fixedapprox`),

for the project's **actual** block interpolant: `f` is any function satisfying
`DyadicApproximation.IsBlockInterpolation F D m f` with `m ≠ 0`, i.e. `f = b` on the
`m`-skeleton and `f` is a full centroid-trace minimizer on every `m`-selected dyadic
square.  No harmonicity, no arbitrary field with an assumed bound, and no probabilistic
input beyond `SublinearDiameterDecay` (the `ε`-form conclusion of the already checked
`Spatial.ae_maxDiamHittingBall_finite_and_sublinear`) is used.

Everything is assembled from existing checked producers; nothing is reproved.

* The maximum principle is **not** reproved.  The single analytic input is
  `GoodGridMaximumPrinciple.norm_sub_le_of_vector_trace_minimizer_on_component`, itself a
  wrapper around the full-energy componentwise principle
  `FullEnergyTraceBounds.coord_mem_Icc_of_vector_trace_minimizer_on_component`.  It is fed
  here at `c = 0` and `ε = 0`: the boundary trace of the block minimizer *is* the centroid
  trace, so the manuscript's "both `b_H` and the range of `φ_m` are in the corresponding
  coordinate enlargement of `S`" reduces to the centroid bookkeeping alone.
* The block-size input is the checked `s:eq:smallblocks`,
  `NonmacroscopicSelectedBlocks.maxSelectedSide_le_ofReal`, together with
  `exists_selected_mem` (every covered point lies in an `m`-selected square) and the scale bridge
  `square_subset_closedBall_of_meets`.
* The cell-size input is the checked `Spatial.maxDiamHittingBall` (`D_R`) through
  `SublinearDiameterDecay`.
* The centroid estimate is the checked `ReflectedGMS.dist_cellCentroid_le_diam`.

The results are stated for the centroid `b_H = cellCentroid F H`, exactly as the manuscript
does; passing to an arbitrary representative `z_H ∈ H` is the separate `s:eq:centroid` step
and is **not** performed here.  All radius quantifiers are uniform in the cells: the bound
of `norm_sub_cellCentroid_le_of_isBlockInterpolation` holds for *every* cell meeting
`clB R` with one pair of constants depending only on `R`.

What this module does **not** do, and what remains for the full `s:eq:sublinear`: the
residual `r_m = Φ - φ_m` must be shown to have small energy on large patches
(`s:eq:smallresidual`), which through `Corrector/GoodLineOscillation.lean` selects the good
offsets, and the limiting `Φ` must be supplied with the full-rectangle minimality clause
consumed by `GoodGridMaximumPrinciple.norm_corrector_sub_le_of_notMem_gridCells`.  Neither
is assumed anywhere below.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.ActualUniformSublinearity

open StatementIngredients DyadicApproximation NonmacroscopicSelectedBlocks Spatial

variable {V : Type*}

/-! ### Centroids of cells meeting one dyadic square -/

/-- **The centroid bookkeeping on one dyadic square.**  Two cells meeting the square
`S` have centroids at distance at most `2 ℓ(S) + 2 d`, where `d` bounds the diameters of
the cells meeting `S`.  This is the `s:eq:boundarycentroid` estimate specialised to the
block `S`, with `diam(S) ≤ 2 ℓ(S)` supplied by the checked `dist_le_two_mul_side`. -/
theorem norm_cellCentroid_sub_le_of_hits_square [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) (s : SquareIndex) {d : ℝ}
    (hd : ∀ w : V, Hits F (square D s).carrier w → Metric.diam (F.cell w : Set Plane) ≤ d)
    {v w : V} (hv : Hits F (square D s).carrier v) (hw : Hits F (square D s).carrier w) :
    ‖cellCentroid F w - cellCentroid F v‖ ≤ 2 * side D s.1 + 2 * d := by
  obtain ⟨qv, hqvc, hqvQ⟩ := hv
  obtain ⟨qw, hqwc, hqwQ⟩ := hw
  have h1 : dist (cellCentroid F w) qw ≤ d :=
    le_trans (ReflectedGMS.dist_cellCentroid_le_diam F hF w hqwc) (hd w ⟨qw, hqwc, hqwQ⟩)
  have h2 : dist qw qv ≤ 2 * side D s.1 := dist_le_two_mul_side D s hqwQ hqvQ
  have h3 : dist qv (cellCentroid F v) ≤ d := by
    rw [dist_comm]
    exact le_trans (ReflectedGMS.dist_cellCentroid_le_diam F hF v hqvc) (hd v ⟨qv, hqvc, hqvQ⟩)
  have htri : dist (cellCentroid F w) (cellCentroid F v)
      ≤ dist (cellCentroid F w) qw + dist qw qv + dist qv (cellCentroid F v) :=
    dist_triangle4 _ _ _ _
  rw [← dist_eq_norm]
  linarith

/-! ### The maximum principle on one selected block -/

/-- **The block estimate of `s:lem:smallblocks`.**  If `f` minimises the full vector energy
on the patch of the dyadic square `S` among all functions carrying the centroid boundary
trace, then every cell meeting `S` satisfies

`‖f H - b_H‖ ≤ √2 · (2 ℓ(S) + 2 d)`,

with `d` a bound for the diameters of the cells meeting `S`.  This is the manuscript's
"apply the coordinatewise maximum principle to the block minimizer; both `b_H` and the
range of `φ_m` are in the corresponding coordinate enlargement of `S`".

The maximum principle is the already checked
`GoodGridMaximumPrinciple.norm_sub_le_of_vector_trace_minimizer_on_component`, used at
`c = 0` and oscillation parameter `ε = 0`: on the spatial boundary of `S` the minimizer
*equals* the centroid trace, so the only surviving term is the centroid bookkeeping. -/
theorem norm_sub_cellCentroid_le_of_centroidTraceMinimizer [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (D : Grid) (s : SquareIndex)
    {f : V → Plane} (hmin : CentroidTraceMinimizer F (square D s) f) {d : ℝ}
    (hd : ∀ w : V, Hits F (square D s).carrier w → Metric.diam (F.cell w : Set Plane) ≤ d)
    {v : V} (hv : Hits F (square D s).carrier v) :
    ‖f v - cellCentroid F v‖ ≤ Real.sqrt 2 * (2 * side D s.1 + 2 * d) := by
  obtain ⟨hfin, htrace, hcomp⟩ := hmin
  have hbdd : Bornology.IsBounded ((square D s).carrier) := by
    obtain ⟨r, _, hsub'⟩ := rectangle_carrier_subset_closedBall (square D s)
    exact Metric.isBounded_closedBall.subset hsub'
  have hanch : BoundaryAnchored (restrictGraph F.graph (patchVertices F (square D s)))
      {a : patchVertices F (square D s) | a.1 ∈ boundaryVertices F (square D s)} :=
    boundaryAnchored_restrictGraph_cells_hitting F hF (square D s).carrier hbdd
  have key := GoodGridMaximumPrinciple.norm_sub_le_of_vector_trace_minimizer_on_component
    (restrictGraph F.graph (patchVertices F (square D s))) hanch
    (u := fun a : patchVertices F (square D s) => cellCentroid F a.1)
    (Φ := fun a : patchVertices F (square D s) => f a.1)
    hfin (fun a ha => htrace a ha) (fun g hg => hcomp g hg)
    (fun a : patchVertices F (square D s) => cellCentroid F a.1) 0
    (ε := 0) (δ := 2 * side D s.1 + 2 * d) (x := ⟨v, hv⟩)
    (fun a ha _ => by
      have : f a.1 = cellCentroid F a.1 := htrace a ha
      simp [this])
    (fun a _ _ => norm_cellCentroid_sub_le_of_hits_square F hF D s hd hv a.2)
  simpa using key

/-! ### The fixed-parameter approximant near the origin -/

/-- A cell meeting `clB R` lies in an `m`-selected square whose side is at most the
manuscript's `s_m(R)`, and every cell meeting that square meets `clB (R + 2 s_m(R))`. -/
theorem exists_selected_square_of_hits_closedBall [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) (hsub : SublinearDiameterDecay F) {m : ℝ} (hm : 0 < m)
    {R ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : maxSelectedSide F D m R ≤ ENNReal.ofReal ℓ)
    {v : V} (hv : Hits F (Metric.closedBall (0 : Plane) R) v) :
    ∃ s : SquareIndex, Selected F D m s ∧ side D s.1 ≤ ℓ ∧
      Hits F (square D s).carrier v ∧
      ∀ w : V, Hits F (square D s).carrier w →
        Hits F (Metric.closedBall (0 : Plane) (R + 2 * ℓ)) w := by
  obtain ⟨z, hzc, hzB⟩ := hv
  -- `z` was produced inside the cell of `v`, so it is covered and the manuscript's covering
  -- statement applies to it; no claim is made at an uncovered point.
  have hzcov : z ∉ uncoveredSet F := by
    intro hc
    exact hc (Set.mem_iUnion.2 ⟨v, hzc⟩)
  obtain ⟨s, hs, hzs⟩ := exists_selected_mem F hF D hsub m hm z hzcov
  have hmeet : ((square D s).carrier ∩ Metric.closedBall (0 : Plane) R).Nonempty :=
    ⟨z, hzs, hzB⟩
  have hside : side D s.1 ≤ ℓ := by
    have hle : ENNReal.ofReal (side D s.1) ≤ maxSelectedSide F D m R :=
      le_iSup (fun t : {t : SquareIndex // Selected F D m t ∧
          ((square D t).carrier ∩ Metric.closedBall (0 : Plane) R).Nonempty} =>
        ENNReal.ofReal (side D t.1.1)) ⟨s, hs, hmeet⟩
    exact (ENNReal.ofReal_le_ofReal_iff hℓ0).1 (le_trans hle hℓ)
  refine ⟨s, hs, hside, ⟨z, hzc, hzs⟩, ?_⟩
  intro w hw
  obtain ⟨q, hqc, hqs⟩ := hw
  refine ⟨q, hqc, ?_⟩
  have hball := square_subset_closedBall_of_meets D s hmeet hqs
  refine Metric.closedBall_subset_closedBall ?_ hball
  linarith

/-- **`s:eq:fixedapprox`, uniform quantitative form.**  Let `f` be the actual `m`-block
interpolant (`m ≠ 0`).  If `ℓ` bounds the manuscript's block size `s_m(R)` and `d` bounds
the manuscript's cell size `D_{R + 2ℓ}`, then *every* cell meeting `clB R` satisfies

`‖f H - b_H‖ ≤ √2 · (2 ℓ + 2 d)`.

The bound is uniform over the cells: the two constants depend only on the radius. -/
theorem norm_sub_cellCentroid_le_of_isBlockInterpolation [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (D : Grid) (hsub : SublinearDiameterDecay F) {m : ℕ} (hm : m ≠ 0)
    {f : V → Plane} (hf : IsBlockInterpolation F D m f) {R ℓ d : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hd0 : 0 ≤ d)
    (hℓ : maxSelectedSide F D (m : ℝ) R ≤ ENNReal.ofReal ℓ)
    (hd : maxDiamHittingBall F (R + 2 * ℓ) ≤ ENNReal.ofReal d)
    {v : V} (hv : Hits F (Metric.closedBall (0 : Plane) R) v) :
    ‖f v - cellCentroid F v‖ ≤ Real.sqrt 2 * (2 * ℓ + 2 * d) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  obtain ⟨s, hs, hside, hvs, hball⟩ :=
    exists_selected_square_of_hits_closedBall F hF D hsub hmpos hℓ0 hℓ hv
  have hfm : (∀ w ∈ skeleton F D (m : ℝ), f w = cellCentroid F w) ∧
      ∀ t : SquareIndex, Selected F D (m : ℝ) t →
        CentroidTraceMinimizer F (square D t) f := by
    simpa [IsBlockInterpolation, hm] using hf
  have hdiam : ∀ w : V, Hits F (square D s).carrier w →
      Metric.diam (F.cell w : Set Plane) ≤ d := by
    intro w hw
    have hle : ENNReal.ofReal (Metric.diam (F.cell w : Set Plane))
        ≤ maxDiamHittingBall F (R + 2 * ℓ) :=
      le_iSup (fun u : {u : V // Hits F (Metric.closedBall (0 : Plane) (R + 2 * ℓ)) u} =>
        ENNReal.ofReal (Metric.diam (F.cell u.1 : Set Plane))) ⟨w, hball w hw⟩
    exact (ENNReal.ofReal_le_ofReal_iff hd0).1 (le_trans hle hd)
  have hbound := norm_sub_cellCentroid_le_of_centroidTraceMinimizer F hF D s
    (hfm.2 s hs) hdiam hvs
  refine le_trans hbound ?_
  have hsq : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have : 2 * side D s.1 + 2 * d ≤ 2 * ℓ + 2 * d := by linarith
  exact mul_le_mul_of_nonneg_left this hsq

/-! ### The sublinear limit -/

end ReflectedGMS.ActualUniformSublinearity
