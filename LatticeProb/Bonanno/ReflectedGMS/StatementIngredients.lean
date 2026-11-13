/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.StatementIngredients at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.AELineConnectivity
import LatticeProb.Bonanno.ReflectedGMS.Graph.Restriction
import LatticeProb.Bonanno.ReflectedGMS.Analysis.ExtendedEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Concrete ingredients for the two reflected-GMS main theorem conclusions.
This file does NOT yet declare either complete main theorem. The missing
random-environment and canonical-process objects are recorded separately.
-/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ReflectedGMS.StatementIngredients

variable {V : Type*}

/-- A bounded closed axis-parallel rectangle with nonempty interior. -/
structure Rectangle where
  lower : Fin 2 → ℝ
  upper : Fin 2 → ℝ
  nondegenerate : ∀ i, lower i < upper i

def Rectangle.carrier (Q : Rectangle) : Set Plane :=
  {z | ∀ i, Q.lower i ≤ z i ∧ z i ≤ Q.upper i}

/-- Cells meeting the rectangle, with no finite-cardinality assumption. -/
def patchVertices (F : IndexedCells V) (Q : Rectangle) : Set V :=
  {v | Hits F Q.carrier v}

/-- Cells meeting its spatial boundary. -/
def boundaryVertices (F : IndexedCells V) (Q : Rectangle) : Set V :=
  {v | Hits F (frontier Q.carrier) v}

noncomputable def cellArea (F : IndexedCells V) (v : V) : ℝ :=
  (volume (F.cell v : Set Plane)).toReal

noncomputable def cellCentroid (F : IndexedCells V) (v : V) : Plane :=
  (cellArea F v)⁻¹ • ∫ z in (F.cell v : Set Plane), z ∂volume

/-- Half the ordered-edge sum, equivalently once per unoriented edge.
The extended-real definition retains infinite energy. -/
noncomputable def vectorEnergy (G : ReflectedWalk.ConductanceGraph V)
    (f : V → Plane) : ℝ≥0∞ :=
  ∑ i : Fin 2, energyENN G (fun v => f v i)

/-- Two scalar Dirichlet pairings; only used below with both energies finite. -/
noncomputable def vectorPairing (G : ReflectedWalk.ConductanceGraph V)
    (f g : V → Plane) : ℝ :=
  ∑ i : Fin 2, G.dirichletForm (fun v => f v i) (fun v => g v i)

/-- The full finite-energy zero-spatial-boundary class on an infinite patch.
There is no finite-support or vanishing-near-an-end condition. -/
def FullZeroBoundaryVariation (F : IndexedCells V) (Q : Rectangle)
    (u : patchVertices F Q → Plane) : Prop :=
  vectorEnergy (restrictGraph F.graph (patchVertices F Q)) u < ∞ ∧
    ∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → u v = 0

/-- The precise full-variation orthogonality conclusion in main theorem (a). -/
def FullRectangleOrthogonality (F : IndexedCells V) (Φ : V → Plane) : Prop :=
  ∀ Q : Rectangle,
    vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) < ∞ ∧
    ∀ u : patchVertices F Q → Plane, FullZeroBoundaryVariation F Q u →
      vectorPairing (restrictGraph F.graph (patchVertices F Q))
        (fun v => Φ v.1) u = 0

/-- Full finite-energy minimization with uniqueness for the prescribed trace.
This is a conclusion predicate, not an extra environmental hypothesis. -/
def FullRectangleMinimizer (F : IndexedCells V) (Φ : V → Plane) : Prop :=
  ∀ Q : Rectangle,
    vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) < ∞ ∧
    ∀ f : patchVertices F Q → Plane,
      (∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q → f v = Φ v.1) →
      vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) ≤
        vectorEnergy (restrictGraph F.graph (patchVertices F Q)) f ∧
      (vectorEnergy (restrictGraph F.graph (patchVertices F Q)) f =
          vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => Φ v.1) →
        f = fun v => Φ v.1)

/-- Epsilon form of the uniform sublinear error on all cells meeting a disk.
It avoids real-valued supremum conventions on an unbounded family. -/
def UniformlySublinearError (F : IndexedCells V) (Φ z : V → Plane) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ R₀ : ℝ, 0 < R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ∀ v : V,
      Hits F (Metric.closedBall (0 : Plane) R) v → ‖Φ v - z v‖ ≤ η * R

def UniformlySublinearCorrector (F : IndexedCells V) (Φ : V → Plane) : Prop :=
  UniformlySublinearError F Φ (cellCentroid F)

/-- A representative actually belongs to its cell; measurability over the
random environment is a separate, as-yet-unavailable object. -/
def CellRepresentatives (F : IndexedCells V) (z : V → Plane) : Prop :=
  ∀ v, z v ∈ (F.cell v : Set Plane)

/-- The ordinary-edge bracket density in the manuscript. Geometry ensures
finite degree, so the sums here have finite support. -/
noncomputable def bracketDensity (F : IndexedCells V) (Φ : V → Plane)
    (v : V) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (cellArea F v)⁻¹ *
    ∑' w : V, F.graph.c v w * (Φ w i - Φ v i) * (Φ w j - Φ v j)

/-- The full deterministic, symmetric positive-definite covariance condition. -/
def SymmetricPositiveDefinite (covariance : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, covariance i j = covariance j i) ∧
    ∀ ξ : Fin 2 → ℝ, ξ ≠ 0 →
      0 < ∑ i : Fin 2, ∑ j : Fin 2, ξ i * covariance i j * ξ j

end ReflectedGMS.StatementIngredients
