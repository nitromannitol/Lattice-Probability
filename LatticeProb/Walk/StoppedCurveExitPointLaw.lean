import LatticeProb.Walk.CountableStoppedCurveMeasurable
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties
import Mathlib.Topology.Instances.ENat

/-! # Joint laws of stopped curves and their exit points -/

set_option autoImplicit false
set_option linter.style.haveILetI false

open MeasureTheory BouRabeeGwynne

namespace LatticeProb

local instance : MeasurableSpace ℕ∞ := ENat.instMeasurableSpace

/-- The clock, stopped curve and embedded exit point have the joint law
obtained by adjoining the endpoint to the clock and curve. The convention at
an infinite exit time is the initial vertex on both sides. -/
theorem map_stoppedCurve_clock_exitPoint {d : ℕ} {V : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : Measure (ℕ → V)) (pos : V → Euc d) (A : Set V) :
    μ.map (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p,
        pos (p ((FiniteConductanceNetwork.exitTime A p).untopD 0)))) =
      (μ.map (fun p =>
        (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p))).map
        (fun q => (q.1, q.2, CurveSpace.endPoint q.2)) := by
  have ht' : @Measurable (ℕ → V) ℕ∞ _ WithTop.instMeasurableSpace
      (FiniteConductanceNetwork.exitTime A) :=
    (FiniteConductanceNetwork.coordinateProcess_adapted.isStoppingTime_hittingAfter
      (Set.to_countable Aᶜ).measurableSet).measurable'
  have ht : @Measurable (ℕ → V) ℕ∞ _ ENat.instMeasurableSpace
      (FiniteConductanceNetwork.exitTime A) := by
    apply measurable_to_countable'
    intro y
    have hy : @MeasurableSet ℕ∞ WithTop.instMeasurableSpace {y} := by
      letI : MeasurableSpace ℕ∞ := WithTop.instMeasurableSpace
      letI : BorelSpace ℕ∞ := ⟨rfl⟩
      exact measurableSet_singleton y
    exact ht' hy
  have hc := measurable_stoppedPolygonalCurve_countable pos A
  have hg : Measurable (fun q : ℕ∞ × CurveSpace d =>
      (q.1, q.2, CurveSpace.endPoint q.2)) :=
    measurable_fst.prodMk (measurable_snd.prodMk
      (CurveSpace.continuous_endPoint.measurable.comp measurable_snd))
  have heq : (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p,
        pos (p ((FiniteConductanceNetwork.exitTime A p).untopD 0)))) =
      (fun q : ℕ∞ × CurveSpace d => (q.1, q.2, CurveSpace.endPoint q.2)) ∘
        (fun p => (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p)) := by
    funext p
    change (_, _, _) = (_, _, CurveSpace.endPoint (stoppedPolygonalCurve pos A p))
    rw [stoppedPolygonalCurve_endPoint]
  rw [heq]
  exact (Measure.map_map hg (ht.prodMk hc)).symm

/-- Equality of joint clock and stopped-curve laws also identifies the joint
law including the embedded exit point. -/
theorem map_stoppedCurve_clock_exitPoint_eq {d : ℕ} {V W : Type*}
    [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (μ : Measure (ℕ → V)) (ν : Measure (ℕ → W))
    (pos : V → Euc d) (pos' : W → Euc d) (A : Set V) (B : Set W) :
    μ.map (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p)) =
    ν.map (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime B p), stoppedPolygonalCurve pos' B p)) →
    μ.map (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime A p), stoppedPolygonalCurve pos A p,
        pos (p ((FiniteConductanceNetwork.exitTime A p).untopD 0)))) =
    ν.map (fun p =>
      (id (α := ℕ∞) (FiniteConductanceNetwork.exitTime B p), stoppedPolygonalCurve pos' B p,
        pos' (p ((FiniteConductanceNetwork.exitTime B p).untopD 0)))) := by
  intro h
  rw [map_stoppedCurve_clock_exitPoint, map_stoppedCurve_clock_exitPoint, h]

end LatticeProb
