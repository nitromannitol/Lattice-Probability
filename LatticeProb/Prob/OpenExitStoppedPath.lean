import LatticeProb.Prob.BrownianOpenExitStopping
import LatticeProb.Prob.BrownianPathPaste
import LatticeProb.Prob.ContinuousStoppedPath
import LatticeProb.Topology.ContinuousMapBorel

/-! # Recovering an open-set exit time from the stopped path -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Stopping a continuous path at its first exit does not change that exit time. -/
theorem openExitTime_stoppedPath {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) {U : Set E} (hU : IsOpen U) :
    openExitTime (fun t (_ : Unit) => stoppedPath
      (openExitTime (fun s (_ : Unit) => w s) U ()) w t) U () =
      openExitTime (fun s (_ : Unit) => w s) U () := by
  let τ := openExitTime (fun s (_ : Unit) => w s) U ()
  change openExitTime (fun t (_ : Unit) => stoppedPath τ w t) U () = τ
  apply le_antisymm
  · by_cases hτ : τ = ⊤
    · rw [hτ]
      exact le_top
    · have hout : w τ.toNNReal ∉ U := openExitTime_not_mem hU w.continuous hτ
      have h := openExitTime_le_of_not_mem (B := fun t (_ : Unit) => stoppedPath τ w t)
        (ω := ()) (t := τ.toNNReal) (by
          simpa only [stoppedPath_apply, ENNReal.coe_toNNReal hτ, min_self] using hout)
      simpa only [ENNReal.coe_toNNReal hτ] using h
  · apply le_iInf
    intro t
    have hout : w (min (t.val : ℝ≥0∞) τ).toNNReal ∉ U := t.property
    have h := openExitTime_le_of_not_mem (B := fun s (_ : Unit) => w s) (ω := ()) hout
    have hfin : min (t.val : ℝ≥0∞) τ ≠ ⊤ :=
      ((min_le_left _ _).trans_lt ENNReal.coe_lt_top).ne
    rw [ENNReal.coe_toNNReal hfin] at h
    exact h.trans (min_le_left _ _)

/-- The exit clock is measurable in the path stopped at that exit, including infinite exits. -/
theorem measurable_openExitTime_stoppedPath {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hc : ∀ ω, Continuous fun t => X t ω) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) :
    Measurable[MeasurableSpace.comap
      (fun ω => stoppedPath (openExitTime X U ω) (pathMap X hc ω)) inferInstance]
      (openExitTime X U) := by
  let F : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ :=
    fun w => openExitTime (fun t (_ : Unit) => w t) U ()
  have hF : Measurable F := by
    have h := measurable_openExitTime
      (B := fun t (w : C(ℝ≥0, EuclideanSpace ℝ (Fin d))) => w t)
      (fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable)
      (fun w => w.continuous) hU
    exact h
  have h := hF.comp (comap_measurable
    (fun ω => stoppedPath (openExitTime X U ω) (pathMap X hc ω)))
  convert h using 1
  funext ω
  exact (openExitTime_stoppedPath (pathMap X hc ω) hU).symm

end LatticeProb
