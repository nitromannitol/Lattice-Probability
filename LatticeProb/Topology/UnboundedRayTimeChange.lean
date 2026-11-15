import LatticeProb.Topology.UnboundedRayCurveSpace
import LatticeProb.Prob.OpenExitTimeReparam

/-! # Time changes of unbounded local curves -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb.UnboundedRayCurveSpace

open UnboundedRayIntervalIntegrand UnboundedRayLocalDistance
open IntervalReparamEDist

/-- An increasing change of clock preserves the range of a continuous ray. -/
noncomputable def timeChange {d : ℕ} (f : UnboundedRay d) (φ : ℝ≥0 ≃o ℝ≥0) :
    UnboundedRay d := by
  let g : Path d := ⟨fun t => f.1 (φ t), f.1.continuous.comp φ.continuous⟩
  refine ⟨g, ?_⟩
  have hr : Set.range g = Set.range f.1 := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨φ t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨φ.symm t, by simp [g]⟩
  simpa only [hr] using f.2

/-- Restrict an increasing clock to a finite initial interval. -/
noncomputable def initialIntervalIso (φ : ℝ≥0 ≃o ℝ≥0) (T : ℝ≥0) :
    TimeInterval (φ.symm T : ℝ≥0∞) ≃o TimeInterval (T : ℝ≥0∞) where
  toFun t := ⟨φ t.1, by
    apply ENNReal.coe_le_coe.mpr
    simpa only [φ.apply_symm_apply] using (φ.le_iff_le).2 (ENNReal.coe_le_coe.mp t.2)⟩
  invFun t := ⟨φ.symm t.1, by
    apply ENNReal.coe_le_coe.mpr
    exact (φ.symm.le_iff_le).2 (ENNReal.coe_le_coe.mp t.2)⟩
  left_inv t := by ext; simp
  right_inv t := by ext; simp
  map_rel_iff' := by intro a b; exact φ.le_iff_le

/-- The local curve class is unchanged by an increasing homeomorphism of the time ray. -/
theorem project_timeChange {d : ℕ} (f : UnboundedRay d) (φ : ℝ≥0 ≃o ℝ≥0) :
    project (timeChange f φ) = project f := by
  apply (project_eq_project_iff _ _).2
  unfold localEDist LocalCurveIntervalDistance.localEDist
  apply MeasureTheory.lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [] with r
  let τ := ballClock f.1 r
  let σ := ballClock (timeChange f φ).1 r
  have hτ : τ ≠ ⊤ := ballClock_ne_top f r
  have hσ : σ ≠ ⊤ := ballClock_ne_top (timeChange f φ) r
  have hclock : σ.toNNReal = φ.symm τ.toNNReal := by
    exact openExitTime_comp_orderIso_toNNReal f.1 (ball 0 r) φ isOpen_ball f.1.continuous hτ
  have hdist : intervalEDist (timeChange f φ).1 f.1 σ τ = 0 := by
    rw [← ENNReal.coe_toNNReal hσ, ← ENNReal.coe_toNNReal hτ, hclock]
    apply nonpos_iff_eq_zero.mp
    refine (intervalEDist_le_of_orderIso _ _ (initialIntervalIso φ τ.toNNReal)).trans ?_
    simp [timeChange, initialIntervalIso]
  change ENNReal.ofReal (Real.exp (-r)) * min 1 (intervalEDist _ _ σ τ) = 0
  simp [hdist]

end LatticeProb.UnboundedRayCurveSpace
