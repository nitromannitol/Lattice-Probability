import LatticeProb.Bonanno.BouRabeeGwynne.WalkAbsorption
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveMeasurable

/-! # Stopped curve laws for nested absorbing sets -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne

namespace LatticeProb

/-- Stopping the vertex path preserves the polygonal curve stopped at the same set,
including the totalized value when the exit time is infinite. -/
theorem stoppedPolygonalCurve_stoppedWalkPath {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (pos : V → Euc d) (B : Set V) (ω : ℕ → V) :
    stoppedPolygonalCurve pos B (FiniteConductanceNetwork.stoppedWalkPath B ω) =
      stoppedPolygonalCurve pos B ω := by
  unfold stoppedPolygonalCurve
  rw [FiniteConductanceNetwork.exitTime_stoppedWalkPath]
  apply congrArg CurveSpace.project
  apply polygonalCurve_congr_prefix
  intro k hk
  exact FiniteConductanceNetwork.stoppedWalkPath_eq_of_le_exitTime B ω k
    ((WithTop.coe_le_coe.mpr hk).trans (WithTop.coe_untopD_le _ _))

/-- The stopped curve law is independent of absorption outside the smaller set. -/
theorem trajectoryLaw_map_stoppedPolygonalCurve_of_subset {d : ℕ} {V : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (N : FiniteConductanceNetwork V) (pos : V → Euc d) {A B : Set V} (hBA : B ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) :
    (N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos B) =
      (N.trajectoryLaw B hB v).map (stoppedPolygonalCurve pos B) := by
  rw [← N.trajectoryLaw_map_stoppedWalkPath hBA hA hB v,
    Measure.map_map (measurable_stoppedPolygonalCurve pos B)
      (FiniteConductanceNetwork.measurable_stoppedWalkPath B)]
  congr 1
  funext ω
  exact (stoppedPolygonalCurve_stoppedWalkPath pos B ω).symm

end LatticeProb
end
