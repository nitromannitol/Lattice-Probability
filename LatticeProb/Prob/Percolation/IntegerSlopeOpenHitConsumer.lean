import LatticeProb.Prob.Percolation.IntegerSlopeOpenHit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# A nontrivial open-hit event

For one slope coordinate and one constraint, take the sample as coefficient and allow slopes
strictly between one half and three halves. The resulting measurable event contains the
coefficient one and excludes the coefficient one half.
-/

namespace LatticeProb.Prob.Percolation

/-- The interval restricting the single slope coordinate is open in slope space. -/
theorem isOpen_integerSlopeInterval :
    IsOpen {p : Fin 1 → ℝ | 1 / 2 < p 0 ∧ p 0 < 3 / 2} :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)

/-- The generic open-hit theorem applies to the sample-dependent scalar coefficient. -/
theorem measurableSet_integerSlopeOpenHit_interval :
    MeasurableSet {ω : ℝ | ∃ p ∈ {p : Fin 1 → ℝ | 1 / 2 < p 0 ∧ p 0 < 3 / 2},
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} :=
  measurableSet_integerSlopeOpenHit (fun ω (_ : Unit) (_ : Fin 1) => ω)
    (fun _ _ => measurable_id) _ isOpen_integerSlopeInterval

/-- Coefficient one admits slope one in the open interval. -/
theorem one_mem_integerSlopeOpenHit_interval :
    (1 : ℝ) ∈ {ω : ℝ | ∃ p ∈ {p : Fin 1 → ℝ | 1 / 2 < p 0 ∧ p 0 < 3 / 2},
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} := by
  refine ⟨1, ?_, ?_⟩
  · norm_num
  · intro _
    exact ⟨1, by norm_num [Fin.sum_univ_one]⟩

/-- Coefficient one half would force an integer strictly between zero and one. -/
theorem half_not_mem_integerSlopeOpenHit_interval :
    (1 / 2 : ℝ) ∉ {ω : ℝ | ∃ p ∈ {p : Fin 1 → ℝ | 1 / 2 < p 0 ∧ p 0 < 3 / 2},
      p ∈ integerSlopeSubgroup (fun (_ : Unit) (_ : Fin 1) => ω)} := by
  rintro ⟨p, ⟨hlo, hhi⟩, hp⟩
  obtain ⟨z, hz⟩ := (mem_integerSlopeSubgroup _ p).mp hp ()
  simp only [Fin.sum_univ_one] at hz
  have hpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hlt : (z : ℝ) < 1 := by linarith
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hpos
  have hzlt : z < (1 : ℤ) := by exact_mod_cast hlt
  omega

end LatticeProb.Prob.Percolation
