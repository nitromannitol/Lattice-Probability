import LatticeProb.Prob.Percolation.IntegerSlopeCompactHit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A nontrivial compact-hit event

For one slope coordinate and one constraint, use the sample itself as coefficient and the
singleton slope one. The compact-hit event is exactly the integers in the real line; it
contains zero and excludes one half.
-/

namespace LatticeProb.Prob.Percolation

/-- A singleton slope one with coefficient equal to the sample hits exactly at integers. -/
theorem integerSlopeCompactHit_singleton_one :
    {ω : ℝ | ∃ p ∈ ({1} : Set (Fin 1 → ℝ)),
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} =
      Set.range (Int.cast : ℤ → ℝ) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left,
    mem_integerSlopeSubgroup, Fin.sum_univ_one, Pi.one_apply, one_mul, Set.mem_range]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h ()
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩ _
    exact ⟨z, hz.symm⟩

/-- The generic compact-hit theorem applies to this nonconstant measurable coefficient field. -/
theorem measurableSet_integerSlopeCompactHit_singleton_one :
    MeasurableSet {ω : ℝ | ∃ p ∈ ({1} : Set (Fin 1 → ℝ)),
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} :=
  measurableSet_integerSlopeCompactHit (fun ω (_ : Unit) (_ : Fin 1) => ω)
    (fun _ _ => measurable_id) {1} isCompact_singleton

/-- Zero belongs to the singleton-one compact-hit event. -/
theorem zero_mem_integerSlopeCompactHit_singleton_one :
    (0 : ℝ) ∈ {ω : ℝ | ∃ p ∈ ({1} : Set (Fin 1 → ℝ)),
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} := by
  rw [integerSlopeCompactHit_singleton_one]
  exact ⟨0, Int.cast_zero⟩

/-- One half is excluded, so the singleton-one compact-hit event is proper. -/
theorem half_not_mem_integerSlopeCompactHit_singleton_one :
    (1 / 2 : ℝ) ∉ {ω : ℝ | ∃ p ∈ ({1} : Set (Fin 1 → ℝ)),
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} := by
  rw [integerSlopeCompactHit_singleton_one]
  rintro ⟨z, hz⟩
  have hpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hlt : (z : ℝ) < 1 := by linarith
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hpos
  have hzlt : z < (1 : ℤ) := by exact_mod_cast hlt
  omega

end LatticeProb.Prob.Percolation
