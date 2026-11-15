import LatticeProb.Prob.BallExitHistory
import LatticeProb.Topology.RealFirstExitClock

/-! # Real-time descriptions of nested ball-exit histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- A finite exit from an open set has the same endpoint after extending the path
constantly to negative times. -/
theorem sInf_real_extension_eq_openExitTime {Ω E : Type*} [TopologicalSpace E]
    (X : ℝ≥0 → Ω → E) (ω : Ω) (U : Set E)
    (hc : Continuous fun t => X t ω) (hU : IsOpen U)
    (hfin : openExitTime X U ω ≠ ⊤) :
    sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ U} =
      ((openExitTime X U ω).toNNReal : ℝ) := by
  have hclock : openExitTime (fun s (_ : Unit) => X (0 + (s : ℝ)).toNNReal ω) U () =
      openExitTime X U ω := by
    have hf : (fun (s : ℝ≥0) (_ : Unit) => X (0 + (s : ℝ)).toNNReal ω) =
        (fun s (_ : Unit) => X s ω) := by
      funext s u
      simp
    rw [hf]
    rfl
  have hfin' : openExitTime (fun s (_ : Unit) => X (0 + (s : ℝ)).toNNReal ω) U () ≠ ⊤ := by
    rw [hclock]
    exact hfin
  have h := sInf_outside_eq_forward_openExitTime (fun t : ℝ => X t.toNNReal ω)
    U 0 (hc.comp continuous_real_toNNReal) hU hfin'
  rw [hclock] at h
  simpa only [zero_add] using h

/-- A real-time nested ball-exit event admits a representative in the stopped history
at the outer exit. -/
theorem exists_measurableSet_real_ball_subset_exitHistory_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (k : ℕ) {a : ℝ} (ha : 0 < a)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z (r (k + 1))) ω ≠ ⊤) :
    ∃ s : Set Ω, MeasurableSet[ballExitHistory X hm hc z r hr (k + 1)] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r k)})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r (k + 1))})) := by
  obtain ⟨s, hs, hrep⟩ :=
    exists_measurableSet_ball_subset_exitHistory_segment hm hc z r hr k ha hfin
  refine ⟨s, hs, ?_⟩
  filter_upwards [hrep, hfin] with ω hrepω houter
  have hinner : openExitTime X (ball z (r k)) ω ≠ ⊤ :=
    ne_top_of_le_ne_top houter (monotone_openExitTime_ball X ω z (hr (Nat.le_succ k)))
  rw [sInf_real_extension_eq_openExitTime X ω _ (hc ω) isOpen_ball hinner,
    sInf_real_extension_eq_openExitTime X ω _ (hc ω) isOpen_ball houter]
  exact hrepω

end LatticeProb
