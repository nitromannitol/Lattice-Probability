import LatticeProb.Prob.UniformCellScaling
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridTranslationInvariance

/-! The phase of Lebesgue measure on an interval of one complete period. -/

open MeasureTheory Set

namespace LatticeProb

/-- On any interval of length `a⁻¹`, the fractional part of `a * x - c`
has uniform Lebesgue measure on the unit interval, scaled by the interval's
length. -/
theorem map_fract_mul_restrict_cell {a : ℝ} (ha : 0 < a) (t c : ℝ) :
    Measure.map (fun x : ℝ => Int.fract (a * x - c))
        (volume.restrict (Ico t (t + a⁻¹))) =
      ENNReal.ofReal a⁻¹ • volume.restrict (Ico 0 1) := by
  have htrans : Measure.map (fun x : ℝ => x - t)
      (volume.restrict (Ico t (t + a⁻¹))) = volume.restrict (Ico 0 a⁻¹) := by
    have hpre : (fun x : ℝ => x - t) ⁻¹' Ico (0 : ℝ) a⁻¹ = Ico t (t + a⁻¹) := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hmeas : Measurable (fun x : ℝ => x - t) := by fun_prop
    rw [← hpre, ← Measure.restrict_map hmeas measurableSet_Ico]
    simpa only [sub_eq_add_neg] using
      congrArg (fun μ : Measure ℝ => μ.restrict (Ico (0 : ℝ) a⁻¹))
        (map_add_right_eq_self volume (-t))
  have hmul : Measurable (fun y : ℝ => a * y) := by fun_prop
  have hsub : Measurable (fun x : ℝ => x - t) := by fun_prop
  have hrot : Measurable (fun y : ℝ => Int.fract (y + (a * t - c))) :=
    measurable_fract.comp (measurable_id.add_const _)
  calc
    _ = Measure.map (fun y : ℝ => Int.fract (y + (a * t - c)))
        (Measure.map (fun y : ℝ => a * y)
          (Measure.map (fun x : ℝ => x - t)
            (volume.restrict (Ico t (t + a⁻¹))))) := by
      have hfun : (fun x : ℝ => Int.fract (a * x - c)) =
          (fun y : ℝ => Int.fract (y + (a * t - c))) ∘
            ((fun y : ℝ => a * y) ∘ (fun x : ℝ => x - t)) := by
        funext x
        dsimp only [Function.comp_apply]
        congr 1
        ring
      rw [Measure.map_map hmul hsub,
        Measure.map_map hrot (hmul.comp hsub), ← hfun]
    _ = _ := by
      rw [htrans, map_mul_restrict_unit_cell ha, Measure.map_smul _ hrot.aemeasurable]
      congr 1
      simpa only [ReflectedGMS.DyadicGridLaw.unitMeasure] using
        ReflectedGMS.UniformGridTranslationInvariance.map_fract_add_unitMeasure (a * t - c)

end LatticeProb
