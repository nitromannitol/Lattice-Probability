/-
Normalization of equal masses on a finite output carrier. A unit total mass and
equality of the individual masses determine each mass as the inverse cardinality.
For measurable disjoint events, finite measure additivity produces the total mass.
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false

namespace LatticeProb.Prob

open MeasureTheory
open scoped ENNReal

/-- Equal masses on a finite carrier have individual mass equal to the total
mass divided by the cardinality. The chosen output guards the empty-carrier case. -/
theorem mass_eq_sum_div_card {T : Type*} [Fintype T] (m : T → ℝ≥0∞)
    (heq : ∀ t u, m t = m u) (t : T) :
    m t = (∑ u, m u) / (Fintype.card T : ℝ≥0∞) := by
  letI : Nonempty T := ⟨t⟩
  have hsum : (∑ u, m u) = m t * (Fintype.card T : ℝ≥0∞) := by
    simp only [heq _ t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  rw [hsum]
  exact (ENNReal.mul_div_cancel_right (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)).symm

/-- A finite family of equal nonnegative extended-real masses with total one
has individual mass equal to the inverse cardinality of its actual carrier. -/
theorem mass_eq_inv_card_of_sum_eq_one {T : Type*} [Fintype T] (m : T → ℝ≥0∞)
    (hsum : ∑ t, m t = 1) (heq : ∀ t u, m t = m u) (t : T) :
    m t = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hmul : m t * (Fintype.card T : ℝ≥0∞) = 1 := by
    simpa only [heq _ t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      using hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left hmul

/-- Equal masses of measurable disjoint events divide their actual union mass
by the number of outputs. The union is not assumed to have probability one. -/
theorem event_mass_eq_union_div_card {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (μ : Measure Ω) (A : T → Set Ω) (hmeas : ∀ t, MeasurableSet (A t))
    (hdisj : Pairwise (fun t u => Disjoint (A t) (A u)))
    (heq : ∀ t u, μ (A t) = μ (A u)) (t : T) :
    μ (A t) = μ (⋃ u, A u) / (Fintype.card T : ℝ≥0∞) := by
  rw [measure_iUnion hdisj hmeas, tsum_fintype]
  exact mass_eq_sum_div_card (fun t => μ (A t)) heq t

/-- **Finite output normalization.** Measurable disjoint output events with
unit union mass and equal individual masses have inverse-cardinality mass.
The hypotheses describe this internal finite-measure argument; concrete protocols
must produce their partition, success and common-mass facts independently. -/
theorem event_mass_eq_inv_card {Ω T : Type*} [MeasurableSpace Ω] [Fintype T]
    (μ : Measure Ω) (A : T → Set Ω) (hmeas : ∀ t, MeasurableSet (A t))
    (hdisj : Pairwise (fun t u => Disjoint (A t) (A u)))
    (htotal : μ (⋃ t, A t) = 1) (heq : ∀ t u, μ (A t) = μ (A u)) (t : T) :
    μ (A t) = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  have hsum : ∑ t, μ (A t) = 1 := by
    rw [measure_iUnion hdisj hmeas, tsum_fintype] at htotal
    exact htotal
  exact mass_eq_inv_card_of_sum_eq_one (fun t => μ (A t)) hsum heq t

end LatticeProb.Prob
