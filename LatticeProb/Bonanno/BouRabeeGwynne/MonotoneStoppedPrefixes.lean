/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.MonotoneStoppedPrefixes at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurvePrefixes

/-! Stopping a curve at corresponding points of a continuous monotone clock
preserves its actual Fréchet class, including prefixes of duration zero. -/

open Set
open scoped unitInterval

namespace BouRabeeGwynne

private lemma prefix_mul_le (a t : unitInterval) : a * t ≤ a := by
  change (a : ℝ) * (t : ℝ) ≤ a
  exact mul_le_of_le_one_right a.property.1 t.property.2

/-- Normalize the part of a monotone clock before a prescribed endpoint. -/
noncomputable def restrictedPrefixClock
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (a b : unitInterval) (hab : φ a = b) (hb : 0 < (b : ℝ)) :
    C(unitInterval, unitInterval) :=
  ⟨fun t ↦ ⟨(φ (a * t) : ℝ) / b, by
      constructor
      · exact div_nonneg (φ (a * t)).property.1 hb.le
      · apply (div_le_one hb).mpr
        have hle : (φ (a * t) : ℝ) ≤ (φ a : ℝ) := hmono (prefix_mul_le a t)
        exact hle.trans_eq (congrArg Subtype.val hab)⟩,
    by fun_prop⟩

lemma restrictedPrefixClock_monotone
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (a b : unitInterval) (hab : φ a = b) (hb : 0 < (b : ℝ)) :
    Monotone (restrictedPrefixClock φ hmono a b hab hb) := by
  intro s t hst
  change (φ (a * s) : ℝ) / b ≤ (φ (a * t) : ℝ) / b
  apply div_le_div_of_nonneg_right _ hb.le
  exact hmono (mul_le_mul_of_nonneg_left hst a.property.1)

lemma restrictedPrefixClock_zero
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ) (hzero : φ 0 = 0)
    (a b : unitInterval) (hab : φ a = b) (hb : 0 < (b : ℝ)) :
    restrictedPrefixClock φ hmono a b hab hb 0 = 0 := by
  apply Subtype.ext
  change (φ (a * 0) : ℝ) / b = 0
  simp only [mul_zero, hzero, Set.Icc.coe_zero, zero_div]

lemma restrictedPrefixClock_one
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (a b : unitInterval) (hab : φ a = b) (hb : 0 < (b : ℝ)) :
    restrictedPrefixClock φ hmono a b hab hb 1 = 1 := by
  apply Subtype.ext
  change (φ (a * 1) : ℝ) / b = 1
  rw [mul_one, hab, div_self hb.ne']

lemma prefixUnitCurve_comp_eq_restrictedPrefixClock {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ)
    (a b : unitInterval) (hab : φ a = b) (hb : 0 < (b : ℝ)) :
    prefixUnitCurve (f.comp φ) a =
      (prefixUnitCurve f b).comp (restrictedPrefixClock φ hmono a b hab hb) := by
  apply ContinuousMap.ext
  intro t
  change f (φ (a * t)) = f (b * restrictedPrefixClock φ hmono a b hab hb t)
  congr 1
  apply Subtype.ext
  change (φ (a * t) : ℝ) = (b : ℝ) * ((φ (a * t) : ℝ) / b)
  field_simp

/-- This local prefix identity needs only monotonicity and the initial point;
the corresponding endpoints may both be zero. -/
theorem curveSpace_project_prefix_comp_monotone {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ) (hzero : φ 0 = 0)
    (a b : unitInterval) (hab : φ a = b) :
    CurveSpace.project (prefixUnitCurve (f.comp φ) a) =
      CurveSpace.project (prefixUnitCurve f b) := by
  by_cases hb : (b : ℝ) = 0
  · apply congrArg CurveSpace.project
    apply ContinuousMap.ext
    intro t
    change f (φ (a * t)) = f (b * t)
    have hle : (φ (a * t) : ℝ) ≤ (φ a : ℝ) := hmono (prefix_mul_le a t)
    have hval : (φ (a * t) : ℝ) = 0 := le_antisymm
      (hle.trans_eq ((congrArg Subtype.val hab).trans hb))
      (φ (a * t)).property.1
    congr 1
    apply Subtype.ext
    change (φ (a * t) : ℝ) = (b : ℝ) * (t : ℝ)
    rw [hval, hb, zero_mul]
  · have hbpos : 0 < (b : ℝ) := lt_of_le_of_ne b.property.1 (Ne.symm hb)
    rw [prefixUnitCurve_comp_eq_restrictedPrefixClock f φ hmono a b hab hbpos]
    exact curveSpace_project_comp_monotone _ _
      (restrictedPrefixClock_monotone φ hmono a b hab hbpos)
      (restrictedPrefixClock_zero φ hmono hzero a b hab hbpos)
      (restrictedPrefixClock_one φ hmono a b hab hbpos)

theorem curveSpace_project_stopped_comp_monotone {d : ℕ}
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d)))
    (φ : C(unitInterval, unitInterval)) (hmono : Monotone φ) (hzero : φ 0 = 0)
    (a b : unitInterval) (hab : φ a = b) :
    CurveSpace.project (stoppedUnitCurve (f.comp φ) a) =
      CurveSpace.project (stoppedUnitCurve f b) := by
  rw [curveSpace_project_stoppedUnitCurve_eq_prefix,
    curveSpace_project_stoppedUnitCurve_eq_prefix]
  exact curveSpace_project_prefix_comp_monotone f φ hmono hzero a b hab

end BouRabeeGwynne
