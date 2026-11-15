import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Odd extensions from a positive interval -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Extend a function on the positive real axis by odd reflection, setting its value at zero to zero. -/
noncomputable def oddIntervalExtension (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then f x else if x < 0 then -f (-x) else 0

@[simp] theorem oddIntervalExtension_of_pos (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    oddIntervalExtension f x = f x := by
  simp [oddIntervalExtension, hx]

@[simp] theorem oddIntervalExtension_zero (f : ℝ → ℂ) : oddIntervalExtension f 0 = 0 := by
  simp [oddIntervalExtension]

/-- The extension is odd, including at the origin. -/
theorem oddIntervalExtension_neg (f : ℝ → ℂ) (x : ℝ) :
    oddIntervalExtension f (-x) = -oddIntervalExtension f x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [oddIntervalExtension, hx, not_lt.mpr hx.le, neg_pos.mpr hx]
  · subst x
    simp
  · simp [oddIntervalExtension, hx, neg_neg,
      neg_lt_zero.mpr hx, not_lt.mpr (neg_nonpos.mpr hx.le)]

/-- Reflection sends Lebesgue measure on the negative interval to that on the positive interval. -/
theorem map_neg_restrict_Ioo (θ : ℝ) :
    (volume.restrict (Ioo (-θ) 0)).map Neg.neg = volume.restrict (Ioo 0 θ) := by
  conv => rhs; rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
    measurableEmbedding_neg.restrict_map]
  simp

/-- Lᵖ integrability on a positive interval is preserved by reflection. -/
theorem memLp_reflect_Ioo {θ : ℝ} {p : ℝ≥0∞} {f : ℝ → ℂ}
    (hf : MemLp f p (volume.restrict (Ioo 0 θ))) :
    MemLp (fun x => f (-x)) p (volume.restrict (Ioo (-θ) 0)) := by
  have hfmap : MemLp f p ((volume.restrict (Ioo (-θ) 0)).map Neg.neg) := by
    rw [map_neg_restrict_Ioo]
    exact hf
  exact hfmap.comp_of_map measurable_neg.aemeasurable

/-- The odd extension of an interval Lᵖ function is Lᵖ on the reflected interval. -/
theorem memLp_oddIntervalExtension {θ : ℝ} (hθ : 0 < θ) {p : ℝ≥0∞} {f : ℝ → ℂ}
    (hf : MemLp f p (volume.restrict (Ioo 0 θ))) :
    MemLp (oddIntervalExtension f) p (volume.restrict (Ioo (-θ) θ)) := by
  let μ := volume.restrict (Ioo (-θ) θ)
  have hp : MemLp f p (μ.restrict (Ioi 0)) := by
    have hs : Ioi (0 : ℝ) ∩ Ioo (-θ) θ = Ioo 0 θ := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨a, b, c⟩
        exact ⟨a, c⟩
      · rintro ⟨a, b⟩
        exact ⟨a, by linarith, b⟩
    simpa only [μ, Measure.restrict_restrict measurableSet_Ioi, hs] using hf
  have hn : MemLp (fun x => -f (-x)) p (μ.restrict (Ioi 0)ᶜ) := by
    have hs : (Ioi (0 : ℝ))ᶜ ∩ Ioo (-θ) θ = Ioc (-θ) 0 := by
      ext x
      simp only [mem_inter_iff, mem_compl_iff, mem_Ioi, not_lt, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨a, b, c⟩
        exact ⟨b, a⟩
      · rintro ⟨a, b⟩
        exact ⟨b, a, by linarith⟩
    dsimp only [μ]
    rw [Measure.restrict_restrict measurableSet_Ioi.compl, hs,
      ← restrict_Ioo_eq_restrict_Ioc]
    exact (memLp_reflect_Ioo hf).neg
  have hpiece := hp.piecewise measurableSet_Ioi hn
  apply hpiece.ae_eq
  filter_upwards [μ.ae_ne 0] with x hx
  by_cases hxpos : 0 < x
  · simp [oddIntervalExtension, Set.piecewise, hxpos]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    simp [oddIntervalExtension, Set.piecewise, hxpos, hxneg]

/-- The odd extension lifts to an Lᵖ function on the circle of twice the interval length. -/
theorem memLp_lift_oddIntervalExtension {θ : ℝ} [Fact (0 < 2 * θ)]
    (hθ : 0 < θ) {p : ℝ≥0∞}
    {f : ℝ → ℂ} (hf : MemLp f p (volume.restrict (Ioo 0 θ))) :
    MemLp (AddCircle.liftIoc (2 * θ) (-θ) (oddIntervalExtension f)) p := by
  apply MemLp.memLp_liftIoc
  have h := memLp_oddIntervalExtension hθ hf
  have heq : -θ + 2 * θ = θ := by ring
  rw [heq, ← restrict_Ioo_eq_restrict_Ioc]
  exact h

end LatticeProb
