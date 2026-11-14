import LatticeProb.Prob.ParentBlockSelector

/-!
# A measurable selector for a translated square grid

A positive-mesh translated integer grid covers the plane by closed squares. Consequently it can
be used with the parent-block exit selector.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb.ParentBlock

/-- The centre of the square indexed by an integer pair in a translated square grid. -/
noncomputable def gridCentre (a : ℂ) (s : ℝ) (p : ℤ × ℤ) : ℂ :=
  a + ⟨s * ((p.1 : ℝ) + 1 / 2), s * ((p.2 : ℝ) + 1 / 2)⟩

/-- Every complex point lies in a square of a positive-mesh translated integer grid. -/
theorem exists_mem_closedSquare_gridCentre (a z : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ p : ℤ × ℤ, z ∈ closedSquare (gridCentre a s p) s := by
  let j : ℤ := ⌊(z.re - a.re) / s⌋
  let k : ℤ := ⌊(z.im - a.im) / s⌋
  have hj₁ : (j : ℝ) * s ≤ z.re - a.re :=
    (le_div_iff₀ hs).mp (Int.floor_le _)
  have hj₂ : z.re - a.re ≤ ((j : ℝ) + 1) * s :=
    (div_le_iff₀ hs).mp (Int.lt_floor_add_one _).le
  have hk₁ : (k : ℝ) * s ≤ z.im - a.im :=
    (le_div_iff₀ hs).mp (Int.floor_le _)
  have hk₂ : z.im - a.im ≤ ((k : ℝ) + 1) * s :=
    (div_le_iff₀ hs).mp (Int.lt_floor_add_one _).le
  refine ⟨(j, k), ?_⟩
  change |z.re - (a.re + s * ((j : ℝ) + 1 / 2))| ≤ s / 2 ∧
    |z.im - (a.im + s * ((k : ℝ) + 1 / 2))| ≤ s / 2
  constructor <;> apply abs_le.mpr <;> constructor <;> nlinarith

/-- A natural-number enumeration of a positive-mesh translated grid covers the plane. -/
theorem gridCentre_cover (a : ℂ) {s : ℝ} (hs : 0 < s)
    (e : ℕ → ℤ × ℤ) (he : Function.Surjective e) :
    (Set.univ : Set ℂ) ⊆ ⋃ n, closedSquare (gridCentre a s (e n)) s := by
  intro z _
  obtain ⟨p, hp⟩ := exists_mem_closedSquare_gridCentre a z hs
  obtain ⟨n, rfl⟩ := he p
  exact mem_iUnion.mpr ⟨n, hp⟩

/-- Select grid squares measurably until the state leaves the outer parent block. -/
theorem exists_measurable_parentBlock_grid_selector [MeasurableSpace (Option ℕ)]
    (a c : ℂ) {S s : ℝ} (hS : 0 ≤ S) (hs : 0 < s)
    (e : ℕ → ℤ × ℤ) (he : Function.Surjective e) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Option ℕ, Measurable f ∧
      (∀ x n, f x = some n →
        Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈ closedSquare (gridCentre a s (e n)) s ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          interior (parentBlock (gridCentre a s (e n)) s)) ∧
      (∀ x, f x = none ↔ Complex.orthonormalBasisOneI.repr.symm x ∉ parentBlock c S) := by
  apply exists_measurable_parentBlock_selector c hS hs (fun n => gridCentre a s (e n))
  exact (subset_univ _).trans (gridCentre_cover a hs e he)

end LatticeProb.ParentBlock
