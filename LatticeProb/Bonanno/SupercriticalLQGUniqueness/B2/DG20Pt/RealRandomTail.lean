/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.RealRandomTail at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.TightNormed
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_real_random_tail
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | M < |f ω|} ≤ ENNReal.ofReal ζ := by
  let μ : Measure ℝ := P.map f
  haveI : IsFiniteMeasure μ := Measure.isFiniteMeasure_map P f
  have ht : Tendsto (fun r : ℝ => μ {x : ℝ | r < ‖x‖}) atTop (𝓝 0) := by
    simpa using tendsto_measure_norm_gt_of_isTightMeasureSet
      (S := {μ}) isTightMeasureSet_singleton
  have he : ∀ᶠ r : ℝ in atTop, μ {x : ℝ | r < ‖x‖} < ENNReal.ofReal ζ :=
    ht.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.2 hζ))
  obtain ⟨M, hM⟩ := (eventually_atTop.1 he)
  refine ⟨max M 1, lt_max_of_lt_right zero_lt_one, ?_⟩
  have hle : μ {x : ℝ | max M 1 < ‖x‖} ≤ μ {x : ℝ | M < ‖x‖} :=
    measure_mono (by intro x hx; change max M 1 < ‖x‖ at hx;
                     exact lt_of_le_of_lt (le_max_left _ _) hx)
  have hmap : P {ω | max M 1 < |f ω|} = μ {x : ℝ | max M 1 < ‖x‖} := by
    exact (Measure.map_apply hf (isOpen_lt continuous_const continuous_norm).measurableSet).symm
  rw [hmap]
  exact hle.trans (hM M le_rfl).le

end SupercriticalLQGUniqueness.B2.DG20Pt
