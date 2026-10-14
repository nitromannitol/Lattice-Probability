/-
Affine reparametrization of a closed subinterval of the unit interval. The explicit
inverse transports both endpoint and strict interior membership.
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
namespace LatticeProb.Topology

open Set

/-- The increasing affine parametrization of the interval from `a` to `b`. -/
def subintervalParameter (a b : Icc (0 : ℝ) 1) (hab : a.val < b.val)
    (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨a.val + (b.val - a.val) * t.val, by
    have hpos := sub_nonneg.mpr hab.le
    have hlo := mul_nonneg hpos t.property.1
    have hhi := mul_le_of_le_one_right hpos t.property.2
    constructor <;> linarith [a.property.1, b.property.2]⟩

/-- The affine subinterval parametrization is continuous. -/
theorem continuous_subintervalParameter (a b : Icc (0 : ℝ) 1)
    (hab : a.val < b.val) : Continuous (subintervalParameter a b hab) :=
  (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- Strictly ordered subinterval endpoints give an injective parametrization. -/
theorem injective_subintervalParameter (a b : Icc (0 : ℝ) 1)
    (hab : a.val < b.val) : Function.Injective (subintervalParameter a b hab) := by
  intro s t h
  have hv := congrArg Subtype.val h
  change a.val + (b.val - a.val) * s.val = a.val + (b.val - a.val) * t.val at hv
  exact Subtype.ext (mul_left_cancel₀ (ne_of_gt (sub_pos.mpr hab)) (add_left_cancel hv))

/-- Every parameter maps between the chosen subinterval endpoints. -/
theorem subintervalParameter_mem (a b : Icc (0 : ℝ) 1) (hab : a.val < b.val)
    (t : Icc (0 : ℝ) 1) : (subintervalParameter a b hab t).val ∈ Icc a.val b.val := by
  have hlo := mul_nonneg (sub_nonneg.mpr hab.le) t.property.1
  have hhi := mul_le_of_le_one_right (sub_nonneg.mpr hab.le) t.property.2
  change a.val ≤ a.val + (b.val - a.val) * t.val ∧
    a.val + (b.val - a.val) * t.val ≤ b.val
  constructor <;> linarith

/-- **Interior parameter transport.** A point strictly between the endpoints has an interior unit-interval preimage. -/
theorem exists_interior_subintervalParameter (a b : Icc (0 : ℝ) 1)
    (hab : a.val < b.val) (t : Icc (0 : ℝ) 1)
    (ha : a.val < t.val) (hb : t.val < b.val) :
    ∃ q : Icc (0 : ℝ) 1, 0 < q.val ∧ q.val < 1 ∧
      subintervalParameter a b hab q = t := by
  have hpos : 0 < b.val - a.val := sub_pos.mpr hab
  have hlo : 0 < (t.val - a.val) / (b.val - a.val) := div_pos (sub_pos.mpr ha) hpos
  have hhi : (t.val - a.val) / (b.val - a.val) < 1 :=
    (div_lt_one hpos).mpr (sub_lt_sub_right hb a.val)
  refine ⟨⟨(t.val - a.val) / (b.val - a.val), hlo.le, hhi.le⟩, hlo, hhi, ?_⟩
  apply Subtype.ext
  change a.val + (b.val - a.val) * ((t.val - a.val) / (b.val - a.val)) = t.val
  rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
  exact add_sub_cancel _ _

end LatticeProb.Topology
