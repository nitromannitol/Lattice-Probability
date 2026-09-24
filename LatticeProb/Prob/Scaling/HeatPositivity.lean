/-
Strict positivity of a derivative from backward propagation of its zeros, and the resulting
statement that the positive set of a monotone field vanishing at time zero lies entirely at
positive times.

Moved from Parking-Sharpness.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

open Set

namespace LatticeProb.Scaling.HeatPositivity

/-- A nondecreasing function starting at zero has strictly positive derivative on its
positive set if a zero derivative propagates backward through that set. -/
theorem derivative_pos_of_backward_zero
    {f v : ℝ → ℝ} (hf : Continuous f) (hmono : Monotone f) (hzero : f 0 = 0)
    (hderiv : ∀ t, 0 < f t → HasDerivAt f (v t) t)
    (hback : ∀ b, 0 < f b → v b = 0 → ∀ a, a < b → 0 < f a →
      ∀ t ∈ Ioc a b, v t = 0) :
    ∀ t, 0 < f t → 0 < v t := by
  intro b hb
  have hb0 : 0 < b := by
    by_contra hn
    have := hmono (le_of_not_gt hn)
    linarith
  have hvnonneg := (hderiv b hb).nonneg_of_monotone hmono
  by_contra hn
  have hvzero : v b = 0 := le_antisymm (le_of_not_gt hn) hvnonneg
  have hhalf : f b / 2 ∈ Icc (f 0) (f b) := by
    rw [hzero]
    constructor <;> linarith
  obtain ⟨a, ha, haf⟩ := intermediate_value_Icc hb0.le hf.continuousOn hhalf
  have hafpos : 0 < f a := by rw [haf]; positivity
  have hab : a < b := by
    refine lt_of_le_of_ne ha.2 ?_
    intro heq
    subst a
    linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f v hab hf.continuousOn
    (fun t ht => hderiv t (hafpos.trans_le (hmono ht.1.le)))
  have hvc : v c = 0 := hback b hb hvzero a hab hafpos c ⟨hc.1, hc.2.le⟩
  have hdiff : f b - f a = 0 := (div_eq_zero_iff.mp (hvc ▸ hslope.symm)).resolve_right
    (ne_of_gt (sub_pos.mpr hab))
  linarith

/-- Every positive point of a monotone field initially zero has positive time. -/
theorem positive_time {E : Type*} {u : ℝ × E → ℝ}
    (hzero : ∀ x, u (0, x) = 0) (hmono : ∀ x, Monotone fun s => u (s, x)) :
    {p | 0 < u p} ⊆ {p : ℝ × E | 0 < p.1} := by
  intro p hp
  by_contra ht
  have hu := hmono p.2 (le_of_not_gt ht)
  dsimp at hu
  rw [hzero] at hu
  exact (not_lt_of_ge hu) hp

end LatticeProb.Scaling.HeatPositivity
