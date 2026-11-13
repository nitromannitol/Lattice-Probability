/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.Potentials at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Code
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients

/-! Measurable cell fields on the canonical trace environment space.
These are concrete objects and conclusion predicates, not assertions of existence
of harmonic coordinates. Zero values at absent labels are coding conventions. -/
set_option autoImplicit false
open MeasureTheory Set
namespace ReflectedGMS.EnvironmentFields
open Code StatementIngredients

/-- A measurable plane-valued function on all active cells. Extending by zero at
absent labels presents the dependent family using a fixed countable product. -/
structure CellField where
  value : Env → ℕ → Plane
  measurable_value : Measurable value
  absent_zero : ∀ e n, e.val.1 n = none → value e n = 0

/-- Restriction of a coded field to the actual vertices of an environment. -/
def CellField.at (Φ : CellField) (e : Env) : Vertex e.val → Plane :=
  fun v => Φ.value e v.val

theorem CellField.measurable_label (Φ : CellField) (n : ℕ) :
    Measurable (fun e => Φ.value e n) :=
  (measurable_pi_apply n).comp Φ.measurable_value

/-- Measurable representatives are required to lie in their actual compact cells. -/
def IsCellRepresentative (z : CellField) : Prop :=
  ∀ e v, z.at e v ∈ ((decode e).cell v : Set Plane)

/-- The actual difference along an ordered pair of active vertices. -/
def CellField.gradient (Φ : CellField) (e : Env)
    (v w : Vertex e.val) : Plane := Φ.at e w - Φ.at e v

/-- Full spatial variational conclusion, without a finitely supported test restriction. -/
def FullSpatialHarmonicity (Φ : CellField) (e : Env) : Prop :=
  FullRectangleOrthogonality (decode e) (Φ.at e) ∧
  FullRectangleMinimizer (decode e) (Φ.at e)

/-- Vector-valued discrete harmonicity at every actual vertex. -/
def DiscreteHarmonicity (Φ : CellField) (e : Env) : Prop :=
  ∀ v : Vertex e.val,
    ∑' w : Vertex e.val, (decode e).graph.c v w • Φ.gradient e v w = 0

/-- Corrector sublinearity against centroids and every choice of cell representatives.
These are conclusion predicates; no measurable selection is assumed for the
pathwise quantification over representatives.  The every-representative conjunct is the
clause that excludes the zero (or constant) field: the zero field satisfies the centroid
conjunct's companions but fails sublinearity against arbitrary in-cell representatives
(fidelity audit 2026-09-18, `outputs/fidelity-audit-top.md` I1). -/
def SublinearCorrector (Φ : CellField) (e : Env) : Prop :=
  UniformlySublinearCorrector (decode e) (Φ.at e) ∧
  ∀ z : Vertex e.val → Plane, CellRepresentatives (decode e) z →
    UniformlySublinearError (decode e) (Φ.at e) z

end ReflectedGMS.EnvironmentFields
