/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.LFMultigraph at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `LFMultigraph`

Locally finite multigraph with loops and parallel edges; the orientation `src`/`tgt` only labels the two
edge ends, and every derived notion is symmetric in it. The field `exists_inc` (no isolated vertex) is accepted by
 Q2: every graph of the paper is connected with at least two vertices.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- A locally finite multigraph with vertex type `V` and edge type `E` (§1.5; Definition 1.1; Definitions 1.3, 1.8). Each edge `e` joins `src e` and `tgt e`; the orientation is only a labelling of the
two edge ends (edges are unoriented, : every derived notion below is symmetric in it). Loops
(`src e = tgt e`) and parallel edges (distinct `e` with the same ends) are allowed. Every vertex meets finitely
many edges (local finiteness, needed for simple random walk) and at least one edge (no isolated vertex; every
connected graph with two or more vertices, in particular every graph of the paper, has this property). -/
structure LFMultigraph (V E : Type*) where
  /-- The first end of an edge. -/
  src : E → V
  /-- The second end of an edge. -/
  tgt : E → V
  /-- Local finiteness: finitely many edges at each vertex. -/
  finite_inc : ∀ x : V, {e : E | src e = x ∨ tgt e = x}.Finite
  /-- No isolated vertex. -/
  exists_inc : ∀ x : V, ∃ e : E, src e = x ∨ tgt e = x

end MatedCRTHarmonic
