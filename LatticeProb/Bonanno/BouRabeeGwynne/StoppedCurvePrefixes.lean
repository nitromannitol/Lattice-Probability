/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedCurvePrefixes at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BoundaryStoppingComparison

/-! A stopped path with a constant terminal segment represents exactly its
linearly normalized prefix, including a prefix of duration zero. -/

open Set
open scoped unitInterval

namespace BouRabeeGwynne

/-- Rescale the prefix ending at `a` onto the unit interval. -/
noncomputable def prefixUnitCurve {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) (a : unitInterval) :
    C(unitInterval, EuclideanSpace ℝ (Fin d)) :=
  ⟨fun t => f (a * t), by fun_prop⟩

lemma prefixUnitCurve_comp_terminalPause {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) (a : unitInterval)
    (ha : 0 < (a : ℝ)) :
    (prefixUnitCurve f a).comp (terminalPauseClock (a : ℝ)) = stoppedUnitCurve f a := by
  apply ContinuousMap.ext
  intro t
  change f (a * (terminalPauseClock (a : ℝ) t)) = f (min t a)
  congr 1
  apply Subtype.ext
  change (a : ℝ) * max 0 (min 1 ((t : ℝ) / a)) = min (t : ℝ) (a : ℝ)
  by_cases ht : (t : ℝ) ≤ a
  · have hq : (t : ℝ) / a ≤ 1 := (div_le_one ha).mpr ht
    rw [min_eq_right hq, max_eq_right (div_nonneg t.property.1 ha.le), min_eq_left ht]
    field_simp [ha.ne']
  · have hq : 1 ≤ (t : ℝ) / a := (one_le_div ha).mpr (le_of_not_ge ht)
    rw [min_eq_left hq, max_eq_right zero_le_one, mul_one,
      min_eq_right (le_of_not_ge ht)]

/-- Constant padding and normalization of the genuine prefix give the same
Fréchet curve class; no positivity of the stopping duration is required. -/
theorem curveSpace_project_stoppedUnitCurve_eq_prefix {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) (a : unitInterval) :
    CurveSpace.project (stoppedUnitCurve f a) = CurveSpace.project (prefixUnitCurve f a) := by
  by_cases ha : a = 0
  · subst a
    apply congrArg CurveSpace.project
    apply ContinuousMap.ext
    intro t
    change f (min t 0) = f (0 * t)
    have ht : (0 : unitInterval) ≤ t := t.property.1
    rw [min_eq_right ht, zero_mul]
  · have hapos : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (by
      intro h
      exact ha (Subtype.ext h.symm))
    rw [← prefixUnitCurve_comp_terminalPause f a hapos]
    exact curveSpace_project_terminalPause _ hapos a.property.2

end BouRabeeGwynne
