/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.UnitCurveExit at commit fdb5cad; local imports adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedBrownianMeasurable
import LatticeProb.Bonanno.BouRabeeGwynne.ContinuousExitProperties
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurvePrefixes
import Mathlib.Topology.Order.ProjIcc

/-! Measurable first-exit stopping of an actual continuous unit-interval curve.
The curve is extended constantly beyond time one; absence of an exit retains
the whole curve. -/

open MeasureTheory Set
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne

variable {d : ℕ}

noncomputable def extendUnitCurve (f : C(unitInterval, Euc d)) : BrownianPath d :=
  ⟨fun t ↦ f (Set.projIcc 0 1 zero_le_one (t : ℝ)), by fun_prop⟩

@[simp] lemma extendUnitCurve_apply_unit (f : C(unitInterval, Euc d))
    (a : unitInterval) : extendUnitCurve f ⟨a, a.property.1⟩ = f a := by
  change f (Set.projIcc 0 1 zero_le_one (a : ℝ)) = f a
  rw [Set.projIcc_val]

lemma measurable_extendUnitCurve : Measurable (extendUnitCurve (d := d)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ContinuousMap.measurable_eval (Set.projIcc 0 1 zero_le_one (t : ℝ))

/-- First unit-time exit, capped at one. -/
noncomputable def unitCurveExitTime (U : Set (Euc d)) (f : C(unitInterval, Euc d)) :
    unitInterval :=
  ⟨((min (continuousExitTime U 0 (extendUnitCurve f)) 1).toNNReal : ℝ),
    (min (continuousExitTime U 0 (extendUnitCurve f)) 1).toNNReal.property, by
      have h := ENNReal.toNNReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
        (min_le_right (continuousExitTime U 0 (extendUnitCurve f)) 1)
      exact_mod_cast h⟩

lemma unitCurveExitTime_coe (U : Set (Euc d)) (f : C(unitInterval, Euc d)) :
    ENNReal.ofNNReal ⟨(unitCurveExitTime U f : ℝ), (unitCurveExitTime U f).property.1⟩ =
      min (continuousExitTime U 0 (extendUnitCurve f)) 1 := by
  change (((min (continuousExitTime U 0 (extendUnitCurve f)) 1).toNNReal : ℝ≥0) : ℝ≥0∞) = _
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))

lemma measurable_unitCurveExitTime {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable (unitCurveExitTime U) := by
  apply Measurable.subtype_mk
  exact measurable_coe_nnreal_real.comp
    (ENNReal.measurable_toNNReal.comp
      (((measurable_continuousExitTime hU 0).comp measurable_extendUnitCurve).min
        measurable_const))

lemma unitCurveExitTime_le_of_not_mem {U : Set (Euc d)}
    {f : C(unitInterval, Euc d)} {a : unitInterval} (ha : f a ∉ U) :
    unitCurveExitTime U f ≤ a := by
  have hout : (0 : Euc d) + extendUnitCurve f ⟨a, a.property.1⟩ ∉ U := by
    simpa only [zero_add, extendUnitCurve_apply_unit] using ha
  have ht := (min_le_left (continuousExitTime U 0 (extendUnitCurve f)) 1).trans
    (continuousExitTime_le_of_not_mem hout)
  rw [← unitCurveExitTime_coe U f] at ht
  exact ENNReal.coe_le_coe.mp ht

lemma mem_of_lt_unitCurveExitTime {U : Set (Euc d)}
    {f : C(unitInterval, Euc d)} {a : unitInterval}
    (ha : a < unitCurveExitTime U f) : f a ∈ U := by
  by_contra hout
  exact (not_le_of_gt ha) (unitCurveExitTime_le_of_not_mem hout)

lemma unitCurveExitTime_not_mem_of_exists {U : Set (Euc d)} (hU : IsOpen U)
    {f : C(unitInterval, Euc d)} (hex : ∃ a, f a ∉ U) :
    f (unitCurveExitTime U f) ∉ U := by
  obtain ⟨a, ha⟩ := hex
  have hout : (0 : Euc d) + extendUnitCurve f ⟨a, a.property.1⟩ ∉ U := by
    simpa only [zero_add, extendUnitCurve_apply_unit] using ha
  have hτ : continuousExitTime U 0 (extendUnitCurve f) ≤ 1 :=
    (continuousExitTime_le_of_not_mem hout).trans (by
      exact ENNReal.coe_le_coe.mpr a.property.2)
  have hfinite := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞) hτ
  have htime : (⟨(unitCurveExitTime U f : ℝ),
      (unitCurveExitTime U f).property.1⟩ : ℝ≥0) =
      (continuousExitTime U 0 (extendUnitCurve f)).toNNReal := by
    apply Subtype.ext
    change ((min (continuousExitTime U 0 (extendUnitCurve f)) 1).toNNReal : ℝ) = _
    rw [min_eq_left hτ]
    rfl
  have he := continuousExitTime_not_mem hU hfinite
  rw [zero_add, ← htime, extendUnitCurve_apply_unit] at he
  exact he

lemma unitCurveExitTime_eq_one_of_forall_mem {U : Set (Euc d)}
    {f : C(unitInterval, Euc d)} (hf : ∀ a, f a ∈ U) : unitCurveExitTime U f = 1 := by
  have hτ : continuousExitTime U 0 (extendUnitCurve f) = ∞ := by
    apply top_unique
    apply le_iInf
    intro t
    exact False.elim (t.property (by
      change (0 : Euc d) + f (Set.projIcc 0 1 zero_le_one (t.val : ℝ)) ∈ U
      simpa only [zero_add] using hf (Set.projIcc 0 1 zero_le_one (t.val : ℝ))))
  apply Subtype.ext
  simp [unitCurveExitTime, hτ]

lemma measurable_prefixUnitCurve :
    Measurable (fun p : C(unitInterval, Euc d) × unitInterval ↦ prefixUnitCurve p.1 p.2) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have heval : Measurable (fun p : C(unitInterval, Euc d) × unitInterval ↦ p.1 p.2) :=
    (by fun_prop : Continuous (fun p : C(unitInterval, Euc d) × unitInterval ↦ p.1 p.2)).measurable
  have htime : Measurable (fun p : C(unitInterval, Euc d) × unitInterval ↦ p.2 * t) := by
    fun_prop
  exact heval.comp (measurable_fst.prodMk htime)

/-- The actual prefix ending at the first continuous exit, or the entire
curve if its range is contained in the domain. -/
noncomputable def unitCurveExitRepresentative (U : Set (Euc d))
    (f : C(unitInterval, Euc d)) : C(unitInterval, Euc d) :=
  prefixUnitCurve f (unitCurveExitTime U f)

lemma measurable_unitCurveExitRepresentative {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable (unitCurveExitRepresentative U) :=
  measurable_prefixUnitCurve.comp (measurable_id.prodMk (measurable_unitCurveExitTime hU))

noncomputable def unitCurveExitProjection (U : Set (Euc d))
    (f : C(unitInterval, Euc d)) : CurveSpace d :=
  CurveSpace.project (unitCurveExitRepresentative U f)

lemma measurable_unitCurveExitProjection {U : Set (Euc d)} (hU : IsOpen U) :
    Measurable (unitCurveExitProjection U) :=
  CurveSpace.continuous_project.measurable.comp (measurable_unitCurveExitRepresentative hU)

end BouRabeeGwynne
