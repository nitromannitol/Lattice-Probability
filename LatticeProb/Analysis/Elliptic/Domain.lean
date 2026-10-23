import LatticeProb.Analysis.Elliptic.Holder

/-!
# Domains defined by regular sublevel sets

The defining function has locally finite Euclidean `C^{2,σ}` norms. Its nonzero derivative
at each zero ensures that its zero set is precisely the boundary of its negative sublevel set.
-/

namespace LatticeProb.Elliptic

open LatticeProb.Euclidean.Lattice
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A bounded domain with `C^{2,σ}` boundary, through a defining function. -/
def IsC2HolderDomain (σ : ℝ) (U : Set (Fin d → ℝ)) : Prop :=
  IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
    ∃ ρ : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 ρ ∧
      (∀ R : ℝ, c2HolderNorm σ {x | radius x < R} ρ < ⊤) ∧
      U = {x | ρ x < 0} ∧ ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0

/-- At a regular zero, every neighborhood meets the negative sublevel set. -/
theorem mem_closure_sublevel_of_regular_zero {ρ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hx : ρ x = 0) (hderiv : fderiv ℝ ρ x ≠ 0) :
    x ∈ closure {y | ρ y < 0} := by
  by_contra h
  have hmin : IsLocalMin ρ x := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h] with y hy
    have hnonneg : ¬ρ y < 0 := fun hyneg => hy (subset_closure hyneg)
    rw [hx]
    exact le_of_not_gt hnonneg
  exact hderiv hmin.fderiv_eq_zero

/-- A continuous defining function with regular zeros has exactly that zero set as boundary. -/
theorem frontier_sublevel_eq_zero {ρ : (Fin d → ℝ) → ℝ} (hρ : Continuous ρ)
    (hregular : ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0) :
    frontier {x | ρ x < 0} = {x | ρ x = 0} := by
  have hopen : IsOpen {x | ρ x < 0} := isOpen_lt hρ continuous_const
  ext x
  rw [hopen.frontier_eq]
  change (x ∈ closure {y | ρ y < 0} ∧ ¬ρ x < 0) ↔ ρ x = 0
  constructor
  · rintro ⟨hx, hxnot⟩
    have hsubset : closure {y | ρ y < 0} ⊆ {y | ρ y ≤ 0} := by
      apply (isClosed_le hρ continuous_const).closure_subset_iff.mpr
      intro y hy
      change ρ y ≤ 0
      exact (show ρ y < 0 from hy).le
    have hle : ρ x ≤ 0 := hsubset hx
    exact le_antisymm hle (le_of_not_gt hxnot)
  · intro hx
    exact ⟨mem_closure_sublevel_of_regular_zero hx (hregular x hx), by simp [hx]⟩

/-- A defining function from the domain predicate identifies the boundary with its zero set. -/
theorem frontier_eq_zero_of_definingFunction {U : Set (Fin d → ℝ)}
    {ρ : (Fin d → ℝ) → ℝ} (hρ : ContDiff ℝ 2 ρ) (hU : U = {x | ρ x < 0})
    (hregular : ∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0) :
    frontier U = {x | ρ x = 0} := by
  rw [hU]
  exact frontier_sublevel_eq_zero hρ.continuous hregular

end

end LatticeProb.Elliptic
