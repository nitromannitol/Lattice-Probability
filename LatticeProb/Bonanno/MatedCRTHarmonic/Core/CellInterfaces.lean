/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Core.CellInterfaces at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Disconnects
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Topology.PolarTemplate

/-!
# Core cell-topology interfaces for Route M (graph separation for the annulus-disconnection estimate)

Core interfaces for graph separation in cell configurations:

* `CellularEmbedding.MonotoneDrawing`: an upstairs planar model of a cell configuration (TF3 §5): a
  continuous, surjective, proper map `Ψ : ℂ → ℂ` with preconnected fibres, and a planar drawing of `G.adj`
  (vertex points `pt`, edge arcs `arc`) carried by `Ψ` into the cells;
* `CellularEmbedding.movedTemplate`: the sealed polar template moved by a similarity, extended to `ℝ` by clamping;
* `CellularEmbedding.TemplateSeparation`: graph separation by walks whose cells follow the moved polar template
  (TF3 §2, the conclusion of Lemma D″); the annulus-disconnection estimate consumes it, and the mated-CRT layer discharges it;
* `CellularEmbedding.PointConnected`: the cell-topology property (LC): the cells through any point induce a connected subgraph (TF2's Theorem B proves it for the
  mated-CRT map); TF3's Lemma D″ uses it through Corollary B′.

Only deviation from TF3's text: in field `arc_symm` the reversed adjacency is written `h.symm`
(`SimpleGraph.Adj.symm`), because in the pinned Mathlib `SimpleGraph.symm` is a `Std.Symm` instance rather than a
function (TF3's `G.adj.symm h` does not elaborate); the meaning is unchanged.

`MonotoneDrawing` is data with properties; `TemplateSeparation` and `PointConnected` are definitions of
propositions about a given cell configuration. They are discharged for the mated-CRT map by the Route M theorems and the point-connectedness theorem.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.CellularEmbedding

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- An upstairs planar model of the cell configuration (TF3 §5): a continuous proper surjection `Ψ` with connected
fibres and a planar drawing of `G.adj` carried by `Ψ` into the cells. -/
structure MonotoneDrawing where
  Ψ : ℂ → ℂ
  continuous_Ψ : Continuous Ψ
  surjective_Ψ : Function.Surjective Ψ
  tendsto_Ψ : Filter.Tendsto Ψ (Filter.cocompact ℂ) (Filter.cocompact ℂ)
  isPreconnected_fiber : ∀ q, IsPreconnected (Ψ ⁻¹' {q})
  pt : V → ℂ
  pt_injective : Function.Injective pt
  arc : ∀ x y, G.adj.Adj x y → Path (pt x) (pt y)
  arc_injective : ∀ x y h, Function.Injective (arc x y h)
  arc_symm : ∀ x y (h : G.adj.Adj x y), arc y x h.symm = (arc x y h).symm
  arc_inter : ∀ x y x' y' (h : G.adj.Adj x y) (h' : G.adj.Adj x' y'), ¬ (x = x' ∧ y = y') → ¬ (x = y' ∧ y = x') →
    Set.range (arc x y h) ∩ Set.range (arc x' y' h') ⊆ pt '' ({x, y} ∩ {x', y'})
  pt_mem_arc : ∀ v x y h, pt v ∈ Set.range (arc x y h) → v = x ∨ v = y
  Ψ_pt : ∀ x, Ψ (pt x) ∈ H.cell x
  Ψ_arc : ∀ x y h t, Ψ (arc x y h t) ∈ H.cell x ∪ H.cell y

/-- `T` extended to `ℝ` by clamping (`Set.projIcc`). -/
noncomputable def movedTemplate (z : ℂ) (r ϑ s : ℝ) : ℂ :=
  z + r * Complex.exp (ϑ * Complex.I) * Topology.polarTemplate (Set.projIcc 0 1 zero_le_one s)

/-- Graph separation by walks whose cells follow the moved polar template (TF3 §2, Lemma D″'s conclusion). -/
def TemplateSeparation (z : ℂ) (r : ℝ) : Prop :=
  ∀ (ϑ : ℝ) (n : ℕ) (v : ℕ → V) (α β : ℕ → ℝ),
    (∀ j < n, G.adj.Adj (v j) (v (j + 1))) → α 0 = 0 → β n = 1 → Monotone α → Monotone β →
    (∀ j < n, α (j + 1) ≤ β j) → (∀ j ≤ n, 0 ≤ α j ∧ α j ≤ β j ∧ β j ≤ 1 ∧ β j - α j ≤ 1 / 50) →
    (∀ j ≤ n, ∀ s ∈ Set.Icc (α j) (β j), ∀ w ∈ H.cell (v j), ‖w - movedTemplate z r ϑ s‖ < r / 60) →
    G.Disconnects {y | ∃ j ≤ n, v j = y}
      (verticesMeeting H.cell (Metric.sphere z (3 * r / 4))) (verticesMeeting H.cell (Metric.sphere z (5 * r / 4)))

/-- (LC) (TF2 Details (a)): the cells through any point induce a connected subgraph. -/
def PointConnected : Prop := ∀ q : ℂ, (G.adj.induce {x | q ∈ H.cell x}).Connected

end MatedCRTHarmonic.CellularEmbedding
