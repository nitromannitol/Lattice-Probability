/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.Similarity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry

set_option autoImplicit false
open Set
namespace ReflectedGMS

/-- The translation/dilation convention used by the reflected-GMS manuscript:
`S(s,u)(z) = s • (z - u)`. The intended action has `0 < s`. -/
def positiveSimilarity (s : ℝ) (u z : Plane) : Plane :=
  s • (z - u)

@[simp]
theorem positiveSimilarity_apply (s : ℝ) (u z : Plane) :
    positiveSimilarity s u z = s • (z - u) :=
  rfl

theorem positiveSimilarity_comp (s t : ℝ) (u v z : Plane) (ht : 0 < t) :
    positiveSimilarity s u (positiveSimilarity t v z) =
      positiveSimilarity (s * t) (v + t⁻¹ • u) z := by
  ext i
  simp [positiveSimilarity, smul_eq_mul]
  field_simp [ne_of_gt ht]
  ring

theorem positiveSimilarity_inverse_left (s : ℝ) (u z : Plane) (hs : 0 < s) :
    positiveSimilarity s⁻¹ (-s • u) (positiveSimilarity s u z) = z := by
  ext i
  simp [positiveSimilarity, ne_of_gt hs]

theorem positiveSimilarity_inverse_right (s : ℝ) (u z : Plane) (hs : 0 < s) :
    positiveSimilarity s u (positiveSimilarity s⁻¹ (-s • u) z) = z := by
  ext i
  simp [positiveSimilarity, ne_of_gt hs]

/-- A positive similarity as a homeomorphism of the Euclidean plane. -/
noncomputable def positiveSimilarityHomeomorph (s : ℝ) (u : Plane) (hs : 0 < s) : Plane ≃ₜ Plane where
  toFun := positiveSimilarity s u
  invFun := positiveSimilarity s⁻¹ (-s • u)
  left_inv := fun z => positiveSimilarity_inverse_left s u z hs
  right_inv := fun z => positiveSimilarity_inverse_right s u z hs
  continuous_toFun := by
    unfold positiveSimilarity
    fun_prop
  continuous_invFun := by
    unfold positiveSimilarity
    fun_prop

@[simp]
theorem positiveSimilarityHomeomorph_apply (s : ℝ) (u z : Plane) (hs : 0 < s) :
    positiveSimilarityHomeomorph s u hs z = positiveSimilarity s u z :=
  rfl

@[simp]
theorem positiveSimilarityHomeomorph_symm_apply (s : ℝ) (u z : Plane) (hs : 0 < s) :
    (positiveSimilarityHomeomorph s u hs).symm z =
      positiveSimilarity s⁻¹ (-s • u) z :=
  rfl

/-- The image of a nonempty compact cell under a positive similarity. -/
noncomputable def transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : TopologicalSpace.NonemptyCompacts Plane) :
    TopologicalSpace.NonemptyCompacts Plane :=
  K.map (positiveSimilarityHomeomorph s u hs)
    (positiveSimilarityHomeomorph s u hs).continuous

@[simp]
theorem coe_transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K : TopologicalSpace.NonemptyCompacts Plane) :
    (transformCell s u hs K : Set Plane) = positiveSimilarity s u '' (K : Set Plane) :=
  rfl

/-- Preliminary label-preserving indexed action. It transforms geometric cells and
retains the same conductance graph. It is deliberately distinct from the future
canonical relabeling action on encoded environments. -/
noncomputable def transformIndexedCells {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) : IndexedCells V where
  cell v := transformCell s u hs (F.cell v)
  graph := F.graph

@[simp]
theorem transformIndexedCells_cell {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) (v : V) :
    (transformIndexedCells s u hs F).cell v = transformCell s u hs (F.cell v) :=
  rfl

@[simp]
theorem transformIndexedCells_graph {V : Type*} (s : ℝ) (u : Plane) (hs : 0 < s)
    (F : IndexedCells V) :
    (transformIndexedCells s u hs F).graph = F.graph :=
  rfl

end ReflectedGMS
