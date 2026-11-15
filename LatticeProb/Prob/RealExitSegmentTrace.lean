import LatticeProb.Prob.RealBallExitHistory

/-! # Real-time and nonnegative-time exit segments -/

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- Extending a path constantly to negative times preserves the image of an interval
with nonnegative endpoints. -/
theorem image_real_extension_Icc {E : Type*} (w : ℝ≥0 → E) (a b : ℝ≥0) :
    (fun t : ℝ => w t.toNNReal) '' Icc (a : ℝ) (b : ℝ) = w '' Icc a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t.toNNReal, ⟨?_, ?_⟩, rfl⟩
    · exact (Real.le_toNNReal_iff_coe_le (le_trans a.coe_nonneg ht.1)).2 ht.1
    · exact Real.toNNReal_le_iff_le_coe.2 ht.2
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t : ℝ), ⟨ht.1, ht.2⟩, ?_⟩
    simp only [Real.toNNReal_coe]

/-- The real-infimum description of a segment between finite exits has the same
trace as the corresponding nonnegative-time description. -/
theorem real_exit_segment_trace_eq {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUfin : openExitTime (fun t (_ : Unit) => w t) U () ≠ ⊤)
    (hVfin : openExitTime (fun t (_ : Unit) => w t) V () ≠ ⊤) :
    (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ U})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ V}) =
    w '' Icc (openExitTime (fun t (_ : Unit) => w t) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) V ()).toNNReal := by
  rw [sInf_real_extension_eq_openExitTime (fun t (_ : Unit) => w t) () U
      w.continuous hU hUfin,
    sInf_real_extension_eq_openExitTime (fun t (_ : Unit) => w t) () V
      w.continuous hV hVfin]
  exact image_real_extension_Icc w _ _

/-- A ball is contained in the real-time exit segment exactly when it is contained
in the corresponding nonnegative-time exit segment. -/
theorem real_exit_segment_contains_ball_iff {E : Type*} [PseudoMetricSpace E]
    (w : C(ℝ≥0, E)) (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUfin : openExitTime (fun t (_ : Unit) => w t) U () ≠ ⊤)
    (hVfin : openExitTime (fun t (_ : Unit) => w t) V () ≠ ⊤) (r : ℝ) :
    (∃ y, ball y r ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ U})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ V})) ↔
    ∃ y, ball y r ⊆ w '' Icc
      (openExitTime (fun t (_ : Unit) => w t) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) V ()).toNNReal := by
  rw [real_exit_segment_trace_eq w U V hU hV hUfin hVfin]

end LatticeProb
