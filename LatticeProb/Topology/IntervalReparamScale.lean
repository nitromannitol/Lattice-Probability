import LatticeProb.Topology.IntervalReparamNormalize
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Order.Hom.Set

/-! # Scaling finite time intervals -/

set_option autoImplicit false
open scoped ENNReal NNReal unitInterval

namespace LatticeProb.IntervalReparamEDist

/-- Positive scaling identifies the unit interval with a finite time interval. -/
noncomputable def timeIntervalScale (T : ℝ≥0) (hT : 0 < T) :
    unitInterval ≃o TimeInterval (T : ℝ≥0∞) := by
  let e := (OrderIso.mulRight₀ T hT).Iic 1
  let j : Set.Iic ((OrderIso.mulRight₀ T hT) 1) ≃o TimeInterval (T : ℝ≥0∞) :=
    { toFun := fun x => ⟨x.1, by
        apply ENNReal.coe_le_coe.mpr
        have hx := x.2
        change x.1 ≤ (1 : ℝ≥0) * T at hx
        simpa only [one_mul] using hx⟩
      invFun := fun x => ⟨x.1, by
        change x.1 ≤ (1 : ℝ≥0) * T
        simpa only [one_mul] using ENNReal.coe_le_coe.mp x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_rel_iff' := Iff.rfl }
  exact (NNReal.orderIsoIccZeroCoe 1).trans (e.trans j)

@[simp] theorem timeIntervalScale_apply (T : ℝ≥0) (hT : 0 < T) (u : unitInterval) :
    ((timeIntervalScale T hT u).1 : ℝ) = (u : ℝ) * (T : ℝ) := by
  change (u : ℝ) * (T : ℝ) = (u : ℝ) * (T : ℝ)
  rfl

/-- Positive finite prefixes have the same interval and normalized-curve distance. -/
theorem intervalEDist_eq_edist_normalizedPrefixCurve {d : ℕ}
    (f g : C(ℝ≥0, EuclideanSpace ℝ (Fin d)))
    (T U : ℝ≥0) (hT : 0 < T) (hU : 0 < U) :
    intervalEDist f g T U = edist (normalizedPrefixCurve f T) (normalizedPrefixCurve g U) := by
  let p := NormalizedCurve.ofPath (normalizedPathPrefix f T)
  let q := NormalizedCurve.ofPath (normalizedPathPrefix g U)
  have hp : ∀ u, p.path u = f ((timeIntervalScale T hT u).1) := by
    intro u
    change f ⟨(u : ℝ) * (T : ℝ), _⟩ = f ((timeIntervalScale T hT u).1)
    congr 1
  have hq : ∀ u, q.path u = g ((timeIntervalScale U hU u).1) := by
    intro u
    change g ⟨(u : ℝ) * (U : ℝ), _⟩ = g ((timeIntervalScale U hU u).1)
    congr 1
  rw [intervalEDist_eq_normalized f g (timeIntervalScale T hT) (timeIntervalScale U hU)
    p q hp hq]
  rfl

end LatticeProb.IntervalReparamEDist
