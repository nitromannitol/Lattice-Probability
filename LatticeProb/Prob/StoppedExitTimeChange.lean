import LatticeProb.Prob.OpenExitTimeReparam
import LatticeProb.Prob.ContinuousStoppedPath

/-! # Stopped paths and exit segments under a change of clock -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- Stopping a reparametrized path at the inverse clock time is the same as
reparametrizing the path stopped at the original time. -/
theorem stoppedPath_comp_orderIso {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (φ : ℝ≥0 ≃o ℝ≥0) (T : ℝ≥0) :
    stoppedPath (φ.symm T : ℝ≥0∞) (w.comp ⟨φ, φ.continuous⟩) =
      (stoppedPath (T : ℝ≥0∞) w).comp ⟨φ, φ.continuous⟩ := by
  ext t
  simp only [stoppedPath_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mk, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  rcases le_total t (φ.symm T) with h | h
  · rw [min_eq_left h, min_eq_left (by simpa only [φ.apply_symm_apply] using φ.monotone h)]
  · rw [min_eq_right h, min_eq_right (by simpa only [φ.apply_symm_apply] using φ.monotone h), φ.apply_symm_apply]

/-- The stopped observation at a finite open-set exit commutes with an
increasing change of clock. -/
theorem stoppedPath_openExit_comp_orderIso {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (U : Set E) (φ : ℝ≥0 ≃o ℝ≥0) (hU : IsOpen U)
    (hfin : openExitTime (fun t (_ : Unit) => w t) U () ≠ ⊤) :
    let v := w.comp ⟨φ, φ.continuous⟩
    stoppedPath (openExitTime (fun t (_ : Unit) => v t) U ()) v =
      (stoppedPath (openExitTime (fun t (_ : Unit) => w t) U ()) w).comp
        ⟨φ, φ.continuous⟩ := by
  dsimp only
  let τ := openExitTime (fun t (_ : Unit) => w t) U ()
  let σ := openExitTime (fun t (_ : Unit) => w (φ t)) U ()
  have hout : w τ.toNNReal ∉ U := openExitTime_not_mem hU w.continuous hfin
  have hσle : σ ≤ (φ.symm τ.toNNReal : ℝ≥0∞) := by
    apply openExitTime_le_of_not_mem
    simpa only [φ.apply_symm_apply] using hout
  have hσ : σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hσle
  have htime := openExitTime_comp_orderIso_toNNReal w U φ hU w.continuous hfin
  change σ.toNNReal = φ.symm τ.toNNReal at htime
  change stoppedPath σ (w.comp ⟨φ, φ.continuous⟩) =
    (stoppedPath τ w).comp ⟨φ, φ.continuous⟩
  have hτ : τ ≠ ⊤ := hfin
  rw [← ENNReal.coe_toNNReal hσ, ← ENNReal.coe_toNNReal hτ, htime]
  exact stoppedPath_comp_orderIso w φ τ.toNNReal

/-- A change of clock preserves the trace between two finite open-set exits. -/
theorem openExit_segment_comp_orderIso {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (U V : Set E) (φ : ℝ≥0 ≃o ℝ≥0)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUfin : openExitTime (fun t (_ : Unit) => w t) U () ≠ ⊤)
    (hVfin : openExitTime (fun t (_ : Unit) => w t) V () ≠ ⊤) :
    (fun t => w (φ t)) '' Icc
      (openExitTime (fun t (_ : Unit) => w (φ t)) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w (φ t)) V ()).toNNReal =
    w '' Icc (openExitTime (fun t (_ : Unit) => w t) U ()).toNNReal
      (openExitTime (fun t (_ : Unit) => w t) V ()).toNNReal := by
  rw [openExitTime_comp_orderIso_toNNReal w U φ hU w.continuous hUfin,
    openExitTime_comp_orderIso_toNNReal w V φ hV w.continuous hVfin]
  change (⇑w ∘ φ) '' Icc _ _ = _
  rw [Set.image_comp, φ.image_Icc]
  simp only [φ.apply_symm_apply]

end LatticeProb
