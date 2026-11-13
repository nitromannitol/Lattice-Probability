/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.CentroidTraceLocalEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SpatialRadiusEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.VectorTraceMinimizer
import LatticeProb.Bonanno.ReflectedGMS.Environment.CellArea
import LatticeProb.Bonanno.ReflectedGMS.Geometry.BoundaryAnchoring

/-!
# Local finite energy of the centroid trace and the patch minimizer

This module proves the deterministic energy clause of the manuscript restriction lemma
(`s:lem:restriction`): on the graph `G_Q` of cells meeting a bounded closed axis-parallel
rectangle, the centroid trace `b` has finite energy, with the manuscript constant

`E_{G_Q}(b) ≤ 2 ∑_{H ∈ 𝓗(Q)} d_H² π(H)`  (`s:eq:basepatch`),

and then discharges both hypotheses of the already-checked patch minimizer
`exists_centroidTraceMinimizer`, so that a full centroid-trace minimizer exists on every
rectangle whose local diameter-conductance mass is summable.

The estimate is the vector analogue of `restrictedEnergy_norm_representative_le_localCellMass`
for the spatial radius: the same neighbouring-cell increment mechanism
(`|b_H - b_{H'}| ≤ d_H + d_{H'}` for adjacent cells, because adjacent cells intersect) and the
same ordered-edge majorant `2(d_H² c + c d_{H'}²)`.  It is stated for the *vector* increment
rather than one scalar coordinate, which is what produces the manuscript constant `2` instead
of `4`: the two coordinate squares reassemble into one squared distance.  The local mass is
taken with `π` alone, exactly as in `s:eq:basepatch`; the corollary
`exists_centroidTraceMinimizer_of_localCellMass` accepts instead the combined `π + π*` mass
produced by the spatial bounds corollary.

No finiteness of the cell count, no connectedness of the restricted patch, and no
finite-support or speed-`L²` restriction of the competition class is used anywhere: the patch
may carry infinitely many cells and the comparison class stays the full one of
`DyadicApproximation.CentroidTraceMinimizer`.

The remaining input is exactly the deterministic local mass hypothesis
`Summable (fun v : A => d_v ^ 2 * π(v))`; its random producer (finite expectation /
mass transport) is a separate obligation and is *not* assumed here in the form of finite
centroid energy.
-/

set_option autoImplicit false

open MeasureTheory Set

open scoped ENNReal

namespace ReflectedGMS

open StatementIngredients

variable {V : Type*}

/-! ### The ordered-edge majorant for the `π`-only local mass -/

/-- With the manuscript's `π`-only local diameter mass, the ordered edge family carrying the
diameter of its first endpoint is summable.  This is the `π`-only counterpart of
`summable_localDiameterSq_mul_conductance`, which assumes the combined `π + π*` mass. -/
theorem summable_localDiameterSq_mul_conductance_of_localPiMass [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    Summable (fun p : A × A =>
      Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1) := by
  rw [summable_prod_of_nonneg]
  · constructor
    · intro v
      have hrow : Summable (fun w : A =>
          Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.c v.1 w.1) :=
        ((F.graph.summable_c v.1).subtype fun w => w ∈ A).mul_left
          (Metric.diam (F.cell v.1 : Set Plane) ^ 2)
      exact hrow
    · apply Summable.of_nonneg_of_le
        (fun v => tsum_nonneg fun w => mul_nonneg (sq_nonneg _) (F.graph.c_nonneg _ _))
        _ hmass
      intro v
      change (∑' w : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.c v.1 w.1) ≤ _
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left
        ((F.graph.summable_c v.1).tsum_subtype_le (F.graph.c v.1) A
          (fun w => F.graph.c_nonneg v.1 w)) (sq_nonneg _)
  · intro p
    exact mul_nonneg (sq_nonneg _) (F.graph.c_nonneg _ _)

/-- The ordered edge sum of the first-endpoint diameter mass is at most the vertex mass. -/
theorem tsum_localDiameterSq_mul_conductance_le_localPiMass [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    ∑' p : A × A, Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1 ≤
      ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1 := by
  have hfirst := summable_localDiameterSq_mul_conductance_of_localPiMass F A hmass
  rw [hfirst.tsum_prod]
  have hrows : Summable (fun v : A =>
      ∑' w : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.c v.1 w.1) :=
    ((summable_prod_of_nonneg
      (fun p : A × A => mul_nonneg (sq_nonneg _) (F.graph.c_nonneg p.1.1 p.2.1))).mp hfirst).2
  refine hrows.tsum_le_tsum (fun v => ?_) hmass
  change (∑' w : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * F.graph.c v.1 w.1) ≤ _
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    ((F.graph.summable_c v.1).tsum_subtype_le (F.graph.c v.1) A
      (fun w => F.graph.c_nonneg v.1 w)) (sq_nonneg _)

/-- The mirrored ordered edge family, carrying the diameter of its second endpoint. -/
theorem summable_conductance_mul_localDiameterSq_of_localPiMass [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    Summable (fun p : A × A =>
      F.graph.c p.1.1 p.2.1 * Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
  refine (summable_localDiameterSq_mul_conductance_of_localPiMass F A hmass).prod_symm.congr
    fun p => ?_
  rcases p with ⟨v, w⟩
  simp only [Prod.swap_prod_mk]
  rw [F.graph.c_symm]
  ring

theorem tsum_conductance_mul_localDiameterSq_le_localPiMass [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    ∑' p : A × A, F.graph.c p.1.1 p.2.1 * Metric.diam (F.cell p.2.1 : Set Plane) ^ 2 ≤
      ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1 := by
  have heq : (∑' p : A × A, F.graph.c p.1.1 p.2.1 *
        Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) =
      ∑' p : A × A, Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1 := by
    calc (∑' p : A × A, F.graph.c p.1.1 p.2.1 *
            Metric.diam (F.cell p.2.1 : Set Plane) ^ 2)
        = ∑' p : A × A,
            Metric.diam (F.cell p.swap.1.1 : Set Plane) ^ 2 *
              F.graph.c p.swap.1.1 p.swap.2.1 := by
          apply tsum_congr
          rintro ⟨v, w⟩
          simp only [Prod.swap_prod_mk]
          rw [F.graph.c_symm]
          ring
      _ = ∑' p : A × A, Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 *
            F.graph.c p.1.1 p.2.1 :=
          (Equiv.prodComm A A).tsum_eq
            (fun p : A × A =>
              Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1)
  rw [heq]
  exact tsum_localDiameterSq_mul_conductance_le_localPiMass F A hmass

/-! ### The vector local energy estimate -/

/-- **Quantitative local vector energy of a neighbour-controlled trace.**  If a plane-valued
trace moves by at most `d_H + d_{H'}` across every edge, then on the graph restricted to any
vertex set its full vector energy obeys the manuscript bound
`E ≤ 2 ∑ d_H² π(H)` of `s:eq:basepatch`.  Nothing is assumed about the cardinality or
connectedness of the vertex set. -/
theorem vectorEnergy_restrictGraph_le_localPiMass [Countable V]
    (F : IndexedCells V) (z : V → Plane)
    (hz : ∀ v w : V, F.graph.toSimpleGraph.Adj v w →
      dist (z v) (z w) ≤
        Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane))
    (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    vectorEnergy (restrictGraph F.graph A) (fun v : A => z v.1) ≤
      ENNReal.ofReal
        (2 * ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1) := by
  set first : A × A → ℝ := fun p =>
    Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 * F.graph.c p.1.1 p.2.1 with hfirstdef
  set second : A × A → ℝ := fun p =>
    F.graph.c p.1.1 p.2.1 * Metric.diam (F.cell p.2.1 : Set Plane) ^ 2 with hseconddef
  set major : A × A → ℝ := fun p => 2 * (first p + second p) with hmajordef
  have hfirst : Summable first :=
    summable_localDiameterSq_mul_conductance_of_localPiMass F A hmass
  have hsecond : Summable second :=
    summable_conductance_mul_localDiameterSq_of_localPiMass F A hmass
  have hmajor : Summable major := (hfirst.add hsecond).mul_left 2
  have hsumpoint : ∀ p : A × A,
      ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p ≤ major p := by
    intro p
    by_cases hc : F.graph.c p.1.1 p.2.1 = 0
    · have hzero : ∀ i : Fin 2,
          (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p = 0 := by
        intro i
        simp [ReflectedWalk.ConductanceGraph.gradSq, restrictGraph, hc]
      have hmaj : major p = 0 := by
        simp [hmajordef, hfirstdef, hseconddef, hc]
      rw [hmaj, Finset.sum_congr rfl fun i _ => hzero i]
      simp
    · have hadj : F.graph.toSimpleGraph.Adj p.1.1 p.2.1 :=
        lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
      have hdist : dist (z p.2.1) (z p.1.1) ≤
          Metric.diam (F.cell p.1.1 : Set Plane) +
            Metric.diam (F.cell p.2.1 : Set Plane) := by
        rw [dist_comm]
        exact hz _ _ hadj
      have hdsq : ∑ i : Fin 2, (z p.2.1 i - z p.1.1 i) ^ 2 =
          dist (z p.2.1) (z p.1.1) ^ 2 := by
        rw [EuclideanSpace.dist_eq,
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
        exact Finset.sum_congr rfl fun i _ => by rw [Real.dist_eq, sq_abs]
      have hsq : dist (z p.2.1) (z p.1.1) ^ 2 ≤
          2 * (Metric.diam (F.cell p.1.1 : Set Plane) ^ 2 +
            Metric.diam (F.cell p.2.1 : Set Plane) ^ 2) := by
        have h0 : dist (z p.2.1) (z p.1.1) ^ 2 ≤
            (Metric.diam (F.cell p.1.1 : Set Plane) +
              Metric.diam (F.cell p.2.1 : Set Plane)) ^ 2 := by
          nlinarith [dist_nonneg (x := z p.2.1) (y := z p.1.1), hdist]
        nlinarith [sq_nonneg (Metric.diam (F.cell p.1.1 : Set Plane) -
          Metric.diam (F.cell p.2.1 : Set Plane))]
      have hmul := mul_le_mul_of_nonneg_left hsq (F.graph.c_nonneg p.1.1 p.2.1)
      calc ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p
          = F.graph.c p.1.1 p.2.1 * ∑ i : Fin 2, (z p.2.1 i - z p.1.1 i) ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => rfl
        _ = F.graph.c p.1.1 p.2.1 * dist (z p.2.1) (z p.1.1) ^ 2 := by rw [hdsq]
        _ ≤ major p := by
            simp only [hmajordef, hfirstdef, hseconddef]
            nlinarith [hmul]
  have hpoint : ∀ (i : Fin 2) (p : A × A),
      (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p ≤ major p := by
    intro i p
    refine le_trans ?_ (hsumpoint p)
    exact Finset.single_le_sum
      (fun j _ => (restrictGraph F.graph A).gradSq_nonneg (fun v : A => z v.1 j) p)
      (Finset.mem_univ i)
  have hcoordfin : ∀ i : Fin 2,
      (restrictGraph F.graph A).HasFiniteEnergy (fun v : A => z v.1 i) := by
    intro i
    exact Summable.of_nonneg_of_le
      (fun p => (restrictGraph F.graph A).gradSq_nonneg _ p) (hpoint i) hmajor
  have hsumsummable : Summable (fun p : A × A =>
      ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p) :=
    Summable.of_nonneg_of_le
      (fun p => Finset.sum_nonneg fun i _ =>
        (restrictGraph F.graph A).gradSq_nonneg (fun v : A => z v.1 i) p)
      hsumpoint hmajor
  have hinterchange : (∑' p : A × A,
        ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p) =
      ∑ i : Fin 2,
        ∑' p : A × A, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p :=
    Summable.tsum_finsetSum (fun i _ => hcoordfin i)
  have hEnergy : ∑ i : Fin 2, (restrictGraph F.graph A).Energy (fun v : A => z v.1 i) =
      (∑' p : A × A,
        ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p) / 2 := by
    rw [hinterchange, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hmajorsum : (∑' p : A × A, major p) ≤
      4 * ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1 := by
    have hsplit : (∑' p : A × A, major p) =
        2 * ((∑' p : A × A, first p) + ∑' p : A × A, second p) := by
      simp only [hmajordef]
      rw [tsum_mul_left, hfirst.tsum_add hsecond]
    rw [hsplit]
    have h1 := tsum_localDiameterSq_mul_conductance_le_localPiMass F A hmass
    have h2 := tsum_conductance_mul_localDiameterSq_le_localPiMass F A hmass
    rw [hfirstdef, hseconddef]
    linarith
  have hreal : ∑ i : Fin 2, (restrictGraph F.graph A).Energy (fun v : A => z v.1 i) ≤
      2 * ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1 := by
    rw [hEnergy]
    have hle : (∑' p : A × A,
        ∑ i : Fin 2, (restrictGraph F.graph A).gradSq (fun v : A => z v.1 i) p) ≤
        ∑' p : A × A, major p := hsumsummable.tsum_le_tsum hsumpoint hmajor
    linarith
  rw [vectorEnergy_eq_ofReal_sum (restrictGraph F.graph A) hcoordfin]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The centroid trace is neighbour-controlled -/

/-- The centroid of a cell is within the cell diameter of every point of the cell: it is an
average of points of the cell, so the average of the distances to a fixed point of the cell
bounds it. -/
theorem dist_cellCentroid_le_diam [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (v : V) {q : Plane} (hq : q ∈ (F.cell v : Set Plane)) :
    dist (cellCentroid F v) q ≤ Metric.diam (F.cell v : Set Plane) := by
  have hKc : IsCompact (F.cell v : Set Plane) := (F.cell v).isCompact
  have hvol : volume (F.cell v : Set Plane) < ∞ := hKc.measure_lt_top
  have harea : 0 < cellArea F v := StatementIngredients.cellArea_pos F hF v
  have hareal : volume.real (F.cell v : Set Plane) = cellArea F v := rfl
  have hid : IntegrableOn (fun x : Plane => x) (F.cell v : Set Plane) volume :=
    continuous_id.continuousOn.integrableOn_compact hKc
  have hconst : IntegrableOn (fun _ : Plane => q) (F.cell v : Set Plane) volume :=
    integrableOn_const hvol.ne
  have hsub : ∫ x in (F.cell v : Set Plane), (x - q) ∂volume
      = (∫ x in (F.cell v : Set Plane), x ∂volume) - cellArea F v • q := by
    rw [integral_sub hid hconst, setIntegral_const, hareal]
  have hcent : cellCentroid F v - q
      = (cellArea F v)⁻¹ • ∫ x in (F.cell v : Set Plane), (x - q) ∂volume := by
    rw [hsub, smul_sub, smul_smul, inv_mul_cancel₀ harea.ne', one_smul]
    rfl
  have hnorm : ‖∫ x in (F.cell v : Set Plane), (x - q) ∂volume‖
      ≤ Metric.diam (F.cell v : Set Plane) * cellArea F v := by
    rw [← hareal]
    refine norm_setIntegral_le_of_norm_le_const hvol ?_
    intro x hx
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hKc.isBounded hx hq
  rw [dist_eq_norm, hcent, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 harea)]
  calc (cellArea F v)⁻¹ * ‖∫ x in (F.cell v : Set Plane), (x - q) ∂volume‖
      ≤ (cellArea F v)⁻¹ * (Metric.diam (F.cell v : Set Plane) * cellArea F v) :=
        mul_le_mul_of_nonneg_left hnorm (inv_pos.2 harea).le
    _ = Metric.diam (F.cell v : Set Plane) := by
        rw [mul_comm (Metric.diam (F.cell v : Set Plane)) (cellArea F v),
          inv_mul_cancel_left₀ harea.ne']

/-- **The manuscript centroid estimate.** Adjacent cells intersect, so their centroids differ
by at most the sum of the two cell diameters. -/
theorem dist_cellCentroid_le_add_diam [Countable V] (F : IndexedCells V) (hF : Geometry F)
    {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w) :
    dist (cellCentroid F v) (cellCentroid F w) ≤
      Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
  obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hvw
  calc dist (cellCentroid F v) (cellCentroid F w)
      ≤ dist (cellCentroid F v) q + dist q (cellCentroid F w) := dist_triangle _ _ _
    _ ≤ Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
        refine add_le_add (dist_cellCentroid_le_diam F hF v hqv) ?_
        rw [dist_comm]
        exact dist_cellCentroid_le_diam F hF w hqw

/-! ### Finite local energy of the centroid trace -/

/-- **`s:eq:basepatch`.** The centroid trace has vector energy at most `2 ∑ d_H² π(H)` on the
graph restricted to any set of cells. -/
theorem vectorEnergy_cellCentroid_le_localPiMass [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    vectorEnergy (restrictGraph F.graph A) (fun v : A => cellCentroid F v.1) ≤
      ENNReal.ofReal
        (2 * ∑' v : A, Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1) :=
  vectorEnergy_restrictGraph_le_localPiMass F (cellCentroid F)
    (fun _ _ hvw => dist_cellCentroid_le_add_diam F hF hvw) A hmass

/-- The finiteness half of the deterministic energy clause of `s:lem:restriction`. -/
theorem vectorEnergy_cellCentroid_lt_top_of_localPiMass [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    vectorEnergy (restrictGraph F.graph A) (fun v : A => cellCentroid F v.1) < ∞ :=
  lt_of_le_of_lt (vectorEnergy_cellCentroid_le_localPiMass F hF A hmass) ENNReal.ofReal_lt_top

/-! ### Boundary anchoring of a rectangle patch and the centroid-trace minimizer -/

theorem rectangle_carrier_eq_axisAlignedRectangle (Q : Rectangle) :
    Q.carrier = axisAlignedRectangle (WithLp.toLp 2 Q.lower) (WithLp.toLp 2 Q.upper) := rfl

theorem rectangle_carrier_isBounded (Q : Rectangle) :
    Bornology.IsBounded Q.carrier := by
  rw [rectangle_carrier_eq_axisAlignedRectangle Q]
  exact axisAlignedRectangle_isBounded _ _

/-- **The boundary-anchoring clause of `s:lem:restriction`** in the exact form required by
`exists_centroidTraceMinimizer`: the patch graph of a rectangle is anchored at its cells
meeting the spatial boundary. -/
theorem rectangle_patch_boundaryAnchored [Countable V] (F : IndexedCells V) (hF : Geometry F)
    (Q : Rectangle) :
    BoundaryAnchored (restrictGraph F.graph (patchVertices F Q))
      {v : patchVertices F Q | v.1 ∈ boundaryVertices F Q} :=
  boundaryAnchored_restrictGraph_cells_hitting F hF Q.carrier (rectangle_carrier_isBounded Q)

/-- **Deterministic patch input of `s:lem:restriction`, paper-facing form.** On a rectangle
whose local diameter mass `∑_{H ∈ 𝓗(Q)} d_H² π(H)` is summable, the centroid trace has finite
vector energy on `G_Q`. -/
theorem vectorEnergy_cellCentroid_patch_lt_top [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (Q : Rectangle)
    (hmass : Summable (fun v : patchVertices F Q =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1)) :
    vectorEnergy (restrictGraph F.graph (patchVertices F Q))
      (fun v : patchVertices F Q => cellCentroid F v.1) < ∞ :=
  vectorEnergy_cellCentroid_lt_top_of_localPiMass F hF (patchVertices F Q) hmass

end ReflectedGMS
