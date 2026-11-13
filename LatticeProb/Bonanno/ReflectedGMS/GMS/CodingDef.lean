/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.CodingDef at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement

/-!
# The labelled coding of a GMS cell configuration

The reflected-walk development works with *labelled* environments (`Code.RawCode`, manuscript
Appendix B): slot `n` holds the cell whose least rational interior point is `rationalPoint n`, and
the conductance array is read off at the labelled cells.  This file defines that coding for an
unlabelled GMS cell configuration.  Its measurability for GMS's `d^CC`-Borel σ-algebra, its
validity, and its compatibility with similarities are proved elsewhere.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.GMS

namespace CellConfig

variable (H : CellConfig)

/-- Slot `n`: the cell of `H` whose least rational interior label is `n`, if there is one. -/
noncomputable def slot (n : ℕ) : Option Cell :=
  open Classical in
  if h : ∃ K ∈ H.cells, Code.LeastInteriorLabel K n then some h.choose else none

/-- The conductance array at the labelled cells (`0` at absent labels). -/
noncomputable def codeCond (n m : ℕ) : ℝ :=
  match H.slot n, H.slot m with
  | some K, some K' => H.c K K'
  | _, _ => 0

/-- **The labelled code** of a cell configuration. -/
noncomputable def code : Code.RawCode := (H.slot, H.codeCond)

/-- GMS's connectedness along lines for one configuration: for each nondegenerate horizontal or
vertical segment `L`, the subgraph of cells meeting `L` is connected. -/
def LineConnected : Prop :=
  (∀ a b y : ℝ, a < b → (H.inducedGraph (horizontal a b y)).Connected) ∧
    ∀ x a b : ℝ, a < b → (H.inducedGraph (vertical x a b)).Connected

end CellConfig

theorem connectedAlongLines_iff (μ : Measure GMSSpace) :
    ConnectedAlongLines μ ↔ ∀ᵐ H ∂μ, H.1.LineConnected := Iff.rfl

/-- The coding map on the GMS configuration space. -/
noncomputable def codeMap (H : GMSSpace) : Code.RawCode := H.1.code

end ReflectedGMS.GMS
