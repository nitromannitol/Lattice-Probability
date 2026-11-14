import Mathlib

/-!
# Reparametrization distance on time intervals

A duration may be infinite. In that case its time interval consists of all finite nonnegative
real times. The infimum is taken over order isomorphisms between the two time intervals.
-/

set_option autoImplicit false

open scoped ENNReal NNReal

namespace LatticeProb.IntervalReparamEDist

/-- Finite nonnegative times bounded by an extended nonnegative duration. -/
abbrev TimeInterval (T : ℝ≥0∞) := {t : ℝ≥0 // (t : ℝ≥0∞) ≤ T}

variable {E : Type*} [PseudoEMetricSpace E]

/-- The uniform distance after the best increasing reparametrization of the time intervals. -/
noncomputable def intervalEDist (f g : ℝ≥0 → E) (T U : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ φ : TimeInterval T ≃o TimeInterval U, ⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1)

theorem intervalEDist_le_of_orderIso (f g : ℝ≥0 → E) {T U : ℝ≥0∞}
    (φ : TimeInterval T ≃o TimeInterval U) :
    intervalEDist f g T U ≤ ⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1) :=
  iInf_le _ φ

theorem intervalEDist_le_iSup_edist (f g : ℝ≥0 → E) (T : ℝ≥0∞) :
    intervalEDist f g T T ≤ ⨆ t : TimeInterval T, edist (f t.1) (g t.1) :=
  iInf_le_of_le (OrderIso.refl (TimeInterval T)) le_rfl

@[simp] theorem intervalEDist_self (f : ℝ≥0 → E) (T : ℝ≥0∞) :
    intervalEDist f f T T = 0 :=
  nonpos_iff_eq_zero.1 ((intervalEDist_le_iSup_edist f f T).trans (by simp))

theorem iSup_edist_comp_eq (f g : ℝ≥0 → E) {T U : ℝ≥0∞}
    (φ : TimeInterval T ≃o TimeInterval U) :
    (⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1)) =
      ⨆ s : TimeInterval U, edist (g s.1) (f (φ.symm s).1) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun s => ?_)
  · rw [edist_comm]
    calc edist (g (φ t).1) (f t.1) = edist (g (φ t).1) (f (φ.symm (φ t)).1) := by
          rw [φ.symm_apply_apply]
      _ ≤ ⨆ s : TimeInterval U, edist (g s.1) (f (φ.symm s).1) :=
          le_iSup (fun s => edist (g s.1) (f (φ.symm s).1)) (φ t)
  · rw [edist_comm]
    calc edist (f (φ.symm s).1) (g s.1) = edist (f (φ.symm s).1) (g (φ (φ.symm s)).1) := by
          rw [φ.apply_symm_apply]
      _ ≤ ⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1) :=
          le_iSup (fun t => edist (f t.1) (g (φ t).1)) (φ.symm s)

theorem intervalEDist_le_comm (f g : ℝ≥0 → E) (T U : ℝ≥0∞) :
    intervalEDist f g T U ≤ intervalEDist g f U T := by
  refine le_iInf fun φ => ?_
  calc intervalEDist f g T U ≤ ⨆ s : TimeInterval T, edist (f s.1) (g (φ.symm s).1) :=
        intervalEDist_le_of_orderIso f g φ.symm
    _ = ⨆ t : TimeInterval U, edist (g t.1) (f (φ t).1) :=
        (iSup_edist_comp_eq g f φ).symm

theorem intervalEDist_comm (f g : ℝ≥0 → E) (T U : ℝ≥0∞) :
    intervalEDist f g T U = intervalEDist g f U T :=
  le_antisymm (intervalEDist_le_comm f g T U) (intervalEDist_le_comm g f U T)

/-- The triangle inequality holds also when some of the durations are infinite. -/
theorem intervalEDist_triangle (f g h : ℝ≥0 → E) (T U V : ℝ≥0∞) :
    intervalEDist f h T V ≤ intervalEDist f g T U + intervalEDist g h U V := by
  refine ENNReal.le_iInf_add_iInf fun φ ψ => ?_
  calc intervalEDist f h T V ≤ ⨆ t : TimeInterval T, edist (f t.1) (h ((φ.trans ψ) t).1) :=
        intervalEDist_le_of_orderIso f h (φ.trans ψ)
    _ ≤ (⨆ t : TimeInterval T, edist (f t.1) (g (φ t).1)) +
        ⨆ s : TimeInterval U, edist (g s.1) (h (ψ s).1) := by
        refine iSup_le fun t => ?_
        rw [OrderIso.trans_apply]
        exact (edist_triangle _ (g (φ t).1) _).trans
          (add_le_add (le_iSup (fun t => edist (f t.1) (g (φ t).1)) t)
            (le_iSup (fun s => edist (g s.1) (h (ψ s).1)) (φ t)))

end LatticeProb.IntervalReparamEDist
