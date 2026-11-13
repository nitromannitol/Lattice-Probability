/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SLUSupport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.WeylScale

 






set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness

namespace LSCMetric

instance instBorelSpace : BorelSpace SupercriticalLQGUniqueness.LSCMetric := ⟨rfl⟩

end LSCMetric

namespace IsExtMetric

theorem self_eq_zero {α : Type*} {d : α × α → ℝ≥0∞} (h : IsExtMetric d) :
    ∀ x, d (x, x) = 0 := h.1

theorem eq_of_eq_zero {α : Type*} {d : α × α → ℝ≥0∞} (h : IsExtMetric d) :
    ∀ x y, d (x, y) = 0 → x = y := h.2.1

theorem symm {α : Type*} {d : α × α → ℝ≥0∞} (h : IsExtMetric d) :
    ∀ x y, d (x, y) = d (y, x) := h.2.2.1

theorem triangle {α : Type*} {d : α × α → ℝ≥0∞} (h : IsExtMetric d) :
    ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z) := h.2.2.2

end IsExtMetric

namespace EuclideanAnnulus

theorem innerRadius_pos (A : EuclideanAnnulus) : 0 < A.innerRadius := A.2.1

theorem innerRadius_lt_outerRadius (A : EuclideanAnnulus) :
    A.innerRadius < A.outerRadius := A.2.2

end EuclideanAnnulus

end SupercriticalLQGUniqueness
