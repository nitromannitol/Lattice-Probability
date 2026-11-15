import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Walk.ConstantStepInterpolation

/-! # Spatial range of sequences of cells -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigWalk

/-- A bounded set of points can meet only finitely many cells. The point
chosen in a cell may vary from visit to visit. -/
theorem finite_range_cells_of_bounded_representatives
    (H : CellConfig) (hH : H.IsCellConfiguration) (ω : ℕ → H.cells)
    (p : ℕ → Plane) (hp : ∀ n, p n ∈ ((ω n).1 : Set Plane))
    (hb : Bornology.IsBounded (Set.range p)) : (Set.range ω).Finite := by
  apply ((CellConfig.finite_restrict_of_isCompact hH hb.isCompact_closure).preimage
    Subtype.val_injective.injOn).subset
  rintro K ⟨n, rfl⟩
  exact ⟨(ω n).2, p n, hp n, subset_closure (Set.mem_range_self n)⟩

/-- Visiting infinitely many cells forces any sequence of points chosen from
those cells to have unbounded range. -/
theorem unbounded_range_representatives_of_infinite_range_cells
    (H : CellConfig) (hH : H.IsCellConfiguration) (ω : ℕ → H.cells)
    (p : ℕ → Plane) (hp : ∀ n, p n ∈ ((ω n).1 : Set Plane))
    (hinf : (Set.range ω).Infinite) : ¬ Bornology.IsBounded (Set.range p) := by
  intro hb
  exact hinf (finite_range_cells_of_bounded_representatives H hH ω p hp hb)

/-- Constant-step interpolation through representatives of infinitely many
cells has unbounded range. -/
theorem unbounded_range_constantStep_of_infinite_range_cells
    (H : CellConfig) (hH : H.IsCellConfiguration) (ω : ℕ → H.cells)
    (p : ℕ → Plane) (hp : ∀ n, p n ∈ ((ω n).1 : Set Plane))
    (hinf : (Set.range ω).Infinite) {m : ℝ≥0} (hm : 0 < m) :
    ¬ Bornology.IsBounded (Set.range (ConstantStepInterpolation.path m p)) := by
  intro hb
  apply unbounded_range_representatives_of_infinite_range_cells H hH ω p hp hinf
  apply hb.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨ConstantStepInterpolation.knot m n,
    ConstantStepInterpolation.path_knot hm p n⟩

end LatticeProb.CellConfigWalk
end
