import LatticeProb.Prob.BrownianPathPaste
import LatticeProb.Prob.ContinuousStoppedPath

/-! # Stopped paths and the stopped natural filtration -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The path stopped at a possibly infinite stopping time is measurable for the stopped
natural filtration. -/
theorem measurable_stoppedPath_natFiltration {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime (natFiltration X hm) τ) :
    Measurable[hτ.measurableSpace] (fun ω => stoppedPath (τ ω) (pathMap X hc ω)) := by
  have hprog : IsStronglyProgressive (natFiltration X hm) X :=
    (stronglyAdapted_natFiltration X hm).isStronglyProgressive_of_continuous hc
  have heval : ∀ t : ℝ≥0, Measurable[hτ.measurableSpace]
      (fun ω => stoppedPath (τ ω) (pathMap X hc ω) t) := by
    intro t
    have hπ : IsStoppingTime (natFiltration X hm) (fun ω => min (τ ω) (t : ℝ≥0∞)) :=
      hτ.min_const t
    have hmπ : Measurable[hπ.measurableSpace]
        (stoppedValue X (fun ω => min (τ ω) (t : ℝ≥0∞))) :=
      measurable_stoppedValue hprog hπ
    have hmτ := hmπ.mono (hπ.measurableSpace_mono hτ (fun ω => min_le_left _ _)) le_rfl
    convert hmτ using 1
    funext ω
    change X (min (t : ℝ≥0∞) (τ ω)).toNNReal ω =
      X (min (τ ω) (t : ℝ≥0∞)).untopA ω
    rw [min_comm, untopA_eq_toNNReal ((min_le_right _ _).trans_lt ENNReal.coe_lt_top).ne]

  let _ : MeasurableSpace Ω := hτ.measurableSpace
  exact ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 heval

end LatticeProb
