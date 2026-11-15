import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Scaling Lebesgue measure on a complete interval to the unit interval. -/

open MeasureTheory Set

namespace LatticeProb

/-- Scaling a complete interval of length `a⁻¹` gives Lebesgue measure on the
unit interval, scaled by the original length. -/
theorem map_mul_restrict_unit_cell {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : ℝ => a * x) (volume.restrict (Ico 0 a⁻¹)) =
      ENNReal.ofReal a⁻¹ • volume.restrict (Ico 0 1) := by
  have hpre : (fun x : ℝ => a * x) ⁻¹' Ico (0 : ℝ) 1 = Ico 0 a⁻¹ := by
    ext x
    simp only [mem_preimage, mem_Ico]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using h0) ha, ?_⟩
      simpa only [one_div] using ((lt_div_iff₀ ha).2 (by simpa only [mul_comm] using h1) : x < 1 / a)
    · rintro ⟨h0, h1⟩
      refine ⟨mul_nonneg ha.le h0, ?_⟩
      have h : x < 1 / a := by simpa only [one_div] using h1
      simpa only [mul_comm] using (lt_div_iff₀ ha).1 h
  calc
    _ = (Measure.map (fun x : ℝ => a * x) volume).restrict (Ico 0 1) := by
      rw [Measure.restrict_map (show Measurable (fun x : ℝ => a * x) from
        measurable_const.mul measurable_id) measurableSet_Ico, hpre]
    _ = _ := by
      rw [Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha), Measure.restrict_smul]

end LatticeProb
