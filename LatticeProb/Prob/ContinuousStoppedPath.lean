import Mathlib

/-! # Continuity of stopped continuous paths -/

set_option autoImplicit false

open Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-- A continuous path stopped at a finite or infinite time. -/
noncomputable def stoppedPath {E : Type*} [TopologicalSpace E]
    (T : ℝ≥0∞) (w : C(ℝ≥0, E)) : C(ℝ≥0, E) where
  toFun t := w (min (t : ℝ≥0∞) T).toNNReal
  continuous_toFun := w.continuous.comp
    (ENNReal.continuousOn_toNNReal.comp_continuous
      (ENNReal.continuous_coe.min continuous_const)
      fun _ => ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne)

@[simp] theorem stoppedPath_apply {E : Type*} [TopologicalSpace E]
    (T : ℝ≥0∞) (w : C(ℝ≥0, E)) (t : ℝ≥0) :
    stoppedPath T w t = w (min (t : ℝ≥0∞) T).toNNReal := rfl

@[simp] theorem stoppedPath_top {E : Type*} [TopologicalSpace E] (w : C(ℝ≥0, E)) :
    stoppedPath ⊤ w = w := by
  ext t
  simp

/-- Stopping a path is jointly continuous in the stopping time and the path. -/
theorem continuous_stoppedPath {E : Type*} [TopologicalSpace E] :
    Continuous (fun p : ℝ≥0∞ × C(ℝ≥0, E) => stoppedPath p.1 p.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have h : Continuous (fun p : (ℝ≥0∞ × C(ℝ≥0, E)) × ℝ≥0 =>
      (min (p.2 : ℝ≥0∞) p.1.1).toNNReal) :=
    ENNReal.continuousOn_toNNReal.comp_continuous
      ((ENNReal.continuous_coe.comp continuous_snd).min (continuous_fst.comp continuous_fst))
      fun _ => ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne
  exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h)

/-- Stopping is continuous along any continuously varying time and path. -/
theorem Continuous.stoppedPath {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    {T : A → ℝ≥0∞} {w : A → C(ℝ≥0, E)} (hT : Continuous T) (hw : Continuous w) :
    Continuous (fun a => stoppedPath (T a) (w a)) :=
  continuous_stoppedPath.comp (hT.prodMk hw)

end LatticeProb
