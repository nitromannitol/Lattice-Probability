/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.DyadicApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi

/-! Concrete dyadic block approximations from manuscript Sections 2 and 4.
The uniform probability law and minimizer existence are separate obligations. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ReflectedGMS.DyadicApproximation
open StatementIngredients

/-- All levels of an axis-parallel dyadic lattice. The binary offset records
which of the four children contains the lower corner of the finer base square.
This contains geometric grid data, not ergodicity or convergence hypotheses. -/
structure Grid where
  phase : ℝ
  phase_mem : phase ∈ Set.Ico (0 : ℝ) 1
  origin : ℤ → Fin 2 → ℝ
  digit : ℤ → Fin 2 → Fin 2
  origin_position : ∀ (k : ℤ) (i : Fin 2),
    -(2 : ℝ) ^ (phase + (k : ℝ)) < origin k i ∧ origin k i ≤ 0
  compatible : ∀ k i,
    origin k i = origin (k + 1) i +
      (2 : ℝ) ^ (phase + (k : ℝ)) * (digit k i).val

/-- The trace sigma algebra from the countable coordinate code. -/
instance : MeasurableSpace Grid :=
  MeasurableSpace.comap
    (fun D : Grid => (D.phase, D.origin, D.digit)) inferInstance

def SquareIndex := ℤ × (Fin 2 → ℤ)

noncomputable def side (D : Grid) (k : ℤ) : ℝ :=
  (2 : ℝ) ^ (D.phase + (k : ℝ))

theorem side_pos (D : Grid) (k : ℤ) : 0 < side D k :=
  Real.rpow_pos_of_pos (by norm_num) _

noncomputable def square (D : Grid) (s : SquareIndex) : Rectangle where
  lower i := D.origin s.1 i + side D s.1 * (s.2 i : ℝ)
  upper i := D.origin s.1 i + side D s.1 * (s.2 i : ℝ) + side D s.1
  nondegenerate _i := lt_add_of_pos_right _ (side_pos D s.1)

/-- At a fixed level the phase, relative origin position, and finitely many
successive parent choices. Cylinder laws avoid hiding an arbitrary grid law. -/
noncomputable def gridCylinder (k : ℤ) (n : ℕ) (D : Grid) :
    ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) :=
  (D.phase, (fun i => -D.origin k i / side D k),
    fun j i => D.digit (k + (j.val : ℤ)) i)

/-- Exact uniform-dyadic-law specification: a uniform logarithmic phase,
uniform origin position in its square, and independent uniform parents.
Existence, uniqueness, and similarity invariance are not asserted here. -/
def UniformGridLaw (ν : Measure Grid) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ (k : ℤ) (n : ℕ),
    Measure.map (gridCylinder k n) ν =
      (volume.restrict (Set.Ico (0 : ℝ) 1)).prod
        ((Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1))).prod
          (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure)

/-- Integer division identifies the actual parent lattice square. -/
def parent (D : Grid) (s : SquareIndex) : SquareIndex :=
  (s.1 + 1, fun i => (s.2 i + (D.digit s.1 i).val) / 2)

def ancestor (D : Grid) (s : SquareIndex) (j : ℕ) : SquareIndex :=
  (parent D)^[j] s

@[simp] theorem ancestor_zero (D : Grid) (s : SquareIndex) :
    ancestor D s 0 = s := rfl

@[simp] theorem ancestor_one (D : Grid) (s : SquareIndex) :
    ancestor D s 1 = parent D s := rfl

variable {V : Type*}

/-- Extended diameter supremum: meaningful before local boundedness is proved. -/
noncomputable def maxCellDiameter (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) : ℝ≥0∞ :=
  ⨆ v : patchVertices F (square D s),
    ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane))

/-- The manuscript's a(S), using every ancestor including S. -/
noncomputable def ancestorRatio (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) : ℝ≥0∞ :=
  ⨆ j : ℕ, maxCellDiameter F D (ancestor D s j) /
    ENNReal.ofReal (side D (ancestor D s j).1)

/-- The index b(S), distinct from the cell centroid b_H. -/
noncomputable def inverseRatio (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) : ℝ≥0∞ := (ancestorRatio F D s)⁻¹

noncomputable def blockIndex (F : IndexedCells V) (D : Grid)
    (s : SquareIndex) : ℝ≥0∞ :=
  ∑' j : ℕ, ((4 : ℝ≥0∞) ^ j)⁻¹ * inverseRatio F D (ancestor D s j)

/-- Exact κ threshold, with a real positive block parameter. -/
def Selected (F : IndexedCells V) (D : Grid) (m : ℝ) (s : SquareIndex) : Prop :=
  0 < m ∧ blockIndex F D s ≤ ENNReal.ofReal m ∧
    ENNReal.ofReal m < blockIndex F D (parent D s)

/-- Cells meeting any selected square boundary, including accumulated grids. -/
def skeleton (F : IndexedCells V) (D : Grid) (m : ℝ) : Set V :=
  {v | ∃ s : SquareIndex, Selected F D m s ∧
    v ∈ boundaryVertices F (square D s)}

/-- On the good event these conditions allow comparison with all the finite
positive real quantities in the manuscript; they are not assumed definitions. -/
def FinitePositiveIndices (F : IndexedCells V) (D : Grid) : Prop :=
  ∀ s : SquareIndex,
    0 < maxCellDiameter F D s ∧ maxCellDiameter F D s < ∞ ∧
    0 < ancestorRatio F D s ∧ ancestorRatio F D s < ∞ ∧
    0 < blockIndex F D s ∧ blockIndex F D s < ∞

/-- Full finite-energy minimization on one actual patch with centroid trace.
The comparison class is all functions with this boundary trace. -/
def CentroidTraceMinimizer (F : IndexedCells V) (Q : Rectangle)
    (f : V → Plane) : Prop :=
  vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => f v.1) < ∞ ∧
  (∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q →
    f v.1 = cellCentroid F v.1) ∧
  ∀ g : patchVertices F Q → Plane,
    (∀ v : patchVertices F Q, v.1 ∈ boundaryVertices F Q →
      g v = cellCentroid F v.1) →
    vectorEnergy (restrictGraph F.graph (patchVertices F Q)) (fun v => f v.1) ≤
      vectorEnergy (restrictGraph F.graph (patchVertices F Q)) g

/-- The actual blockwise interpolation specification. m=0 is prescribed
separately, and positive stages use the κ-selected dyadic squares. -/
def IsBlockInterpolation (F : IndexedCells V) (D : Grid) (m : ℕ)
    (f : V → Plane) : Prop :=
  if m = 0 then f = cellCentroid F
  else (∀ v ∈ skeleton F D (m : ℝ), f v = cellCentroid F v) ∧
    ∀ s : SquareIndex, Selected F D (m : ℝ) s →
      CentroidTraceMinimizer F (square D s) f

/-- A total choice of the specified interpolation, defaulting to centroids
when existence has not been established. The public theorem must prove that
this choice satisfies IsBlockInterpolation almost surely; the default cannot
substitute for that obligation. -/
noncomputable def phi (F : IndexedCells V) (D : Grid) (m : ℕ) : V → Plane := by
  classical
  exact if h : ∃ f, IsBlockInterpolation F D m f then Classical.choose h
    else cellCentroid F

theorem phi_spec_of_exists (F : IndexedCells V) (D : Grid) (m : ℕ)
    (h : ∃ f, IsBlockInterpolation F D m f) :
    IsBlockInterpolation F D m (phi F D m) := by
  unfold phi
  rw [dite_eq_left h]
  exact Classical.choose_spec h

@[simp] theorem phi_zero (F : IndexedCells V) (D : Grid) :
    phi F D 0 = cellCentroid F := by
  have h : ∃ f, IsBlockInterpolation F D 0 f := ⟨cellCentroid F, by simp [IsBlockInterpolation]⟩
  simpa [IsBlockInterpolation] using phi_spec_of_exists F D 0 h

/-- Normalize at the actual root vertex once that root is selected. -/
noncomputable def normalizedPhi (F : IndexedCells V) (D : Grid)
    (root : V) (m : ℕ) (v : V) : Plane := phi F D m v - phi F D m root

@[simp] theorem normalizedPhi_root (F : IndexedCells V) (D : Grid)
    (root : V) (m : ℕ) : normalizedPhi F D root m root = 0 := by
  simp [normalizedPhi]

end ReflectedGMS.DyadicApproximation
