/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.BoundedVertexRangeAvoidance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.PathwiseComponentStabilization
import LatticeProb.Bonanno.ReflectedGMS.Forms.EndLabelConstruction

/-!
# Spatial-infinity avoidance from bounded vertex range

The manuscript's end-avoidance corollary needs no continuous spatial extension.
For a correctly end-labelled path, density of vertex times and boundedness of
the vertex representatives on bounded time intervals already contradict the
definition of a spatially escaping end.

For the actual reflected path, finite-cut stabilization constructs the unique
end-labelled lift pathwise.  The final theorem below is therefore an almost
sure pathwise existence-and-uniqueness statement; it does not assert that the
lift is jointly measurable in the sample point.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

universe u

namespace ReflectedGMS.BoundedVertexRangeAvoidance

open SpatialEnds ReflectedWalk

variable {V : Type u}

/-- A densely vertex-valued, correctly end-labelled path whose vertex
representatives are bounded on every bounded time interval cannot visit a
spatially escaping graph end. -/
theorem avoidsSpatialInfinity_of_bounded_vertex_range
    (F : IndexedCells V) (z : V → Plane)
    (hz : ∀ v, z v ∈ (F.cell v : Set Plane)) (X : ℝ≥0 → State F)
    (hlabel : IsEndLabeling F X)
    (hdense : Dense {t | ∃ v, X t = Sum.inl v})
    (hbounded : ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t ≤ T, ∀ v,
      X t = Sum.inl v → ‖z v‖ ≤ M) :
    AvoidsSpatialInfinity F X := by
  intro t e hte hinfty
  obtain ⟨M, hM⟩ := hbounded (t + 1)
  obtain ⟨K, hK⟩ := hinfty M
  have hcomponent : ∀ᶠ s in 𝓝 t,
      ∀ v, X s = Sum.inl v → v ∈ endComponent F e K :=
    hlabel t e hte K
  have htime : ∀ᶠ s in 𝓝 t, s < t + 1 :=
    Iio_mem_nhds (lt_add_one t)
  have hboth : {s | (∀ v, X s = Sum.inl v → v ∈ endComponent F e K) ∧
      s < t + 1} ∈ 𝓝 t := by
    filter_upwards [hcomponent, htime] with s hscomponent hstime
    exact ⟨hscomponent, hstime⟩
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp hboth
  obtain ⟨s, ⟨v, hsv⟩, hsU⟩ := hdense.exists_mem_open hUopen ⟨t, htU⟩
  have hsprops := hUsub hsU
  change (∀ v, X s = Sum.inl v → v ∈ endComponent F e K) ∧ s < t + 1 at hsprops
  have hvcomponent : v ∈ endComponent F e K := hsprops.1 v hsv
  have hlarge : M < ‖z v‖ := hK K (Finset.Subset.rfl) v hvcomponent (z v) (hz v)
  exact (not_lt_of_ge (hM s hsprops.2.le v hsv)) hlarge

/-- Fixed-time definedness on the rational grid makes the vertex-valued times
of the actual collapsed reflected path dense, simultaneously almost surely. -/
theorem reflected_ae_dense_vertex_times [Countable V]
    (F : IndexedCells V) {w : V → ℝ} {hmin : F.graph.EnergyMinimizer}
    (PF : ProcessFamily V) (hPF : IsReflectedWalk F.graph w hmin PF) (start : V) :
    ∀ᵐ omega ∂PF.P start, Dense {t | ∃ v, PF.X t omega = some v} := by
  have hgrid : ∀ᵐ omega ∂PF.P start, ∀ q : ℚ,
      ∃ v, PF.X (Real.toNNReal (q : ℝ)) omega = some v := by
    refine ae_all_iff.2 fun q => ?_
    exact ((hPF start).2.1 (Real.toNNReal (q : ℝ))).mono fun _ h => h.1
  have hrat : DenseRange (fun q : ℚ => Real.toNNReal (q : ℝ)) := by
    have hsurj : Function.Surjective Real.toNNReal := by
      intro t
      refine ⟨(t : ℝ), NNReal.eq ?_⟩
      exact Real.coe_toNNReal (t : ℝ) t.property
    simpa only [Function.comp_def] using
      hsurj.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  filter_upwards [hgrid] with omega hgridomega
  apply hrat.mono
  rintro t ⟨q, rfl⟩
  exact hgridomega q

/-- Under the actual fixed-vertex starting law, finite-cut stabilization and
rational-time vertex density give the unique end-labelled lift.  If the
producer's compact-time bound on vertex representatives is supplied, this lift
avoids every spatial-infinity end almost surely.  This is pathwise existence;
no measurable selection of lifts is claimed. -/
theorem reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V]
    (F : IndexedCells V) (z : V → Plane)
    (hz : ∀ v, z v ∈ (F.cell v : Set Plane))
    {w : V → ℝ} {hmin : F.graph.EnergyMinimizer}
    (PF : ProcessFamily V) (hPF : IsReflectedWalk F.graph w hmin PF)
    (hG : F.graph.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v) (start : V)
    (hbounded : ∀ᵐ omega ∂PF.P start, ∀ T : ℝ≥0, ∃ M : ℝ,
      ∀ t ≤ T, ∀ v, PF.X t omega = some v → ‖z v‖ ≤ M) :
    ∀ᵐ omega ∂PF.P start, ∃! Y : ℝ≥0 → State F,
      (∀ t, collapse (Y t) = PF.X t omega) ∧
      IsEndLabeling F Y ∧ AvoidsSpatialInfinity F Y := by
  filter_upwards [reflected_ae_dense_vertex_times F PF hPF start,
    PathwiseComponentStabilization.reflected_ae_hasFiniteCutStabilization
      F hPF hG hw start,
    hbounded] with omega hdense hstabilizes hboundedomega
  obtain ⟨Y, hY, hYunique⟩ :=
    EndLabelConstruction.existsUnique_endLabelLift F (fun t => PF.X t omega)
      hdense hstabilizes
  have hdenseY : Dense {t | ∃ v, Y t = Sum.inl v} := by
    apply hdense.mono
    rintro t ⟨v, htv⟩
    refine ⟨v, EndLabelConstruction.collapse_eq_some_iff.mp ?_⟩
    exact (hY.1 t).trans htv
  have hboundedY : ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t ≤ T, ∀ v,
      Y t = Sum.inl v → ‖z v‖ ≤ M := by
    intro T
    obtain ⟨M, hM⟩ := hboundedomega T
    refine ⟨M, ?_⟩
    intro t ht v htv
    apply hM t ht v
    rw [← hY.1 t, htv]
    rfl
  have havoids : AvoidsSpatialInfinity F Y :=
    avoidsSpatialInfinity_of_bounded_vertex_range F z hz Y hY.2 hdenseY hboundedY
  refine ⟨Y, ⟨hY.1, hY.2, havoids⟩, ?_⟩
  intro Y' hY'
  exact hYunique Y' ⟨hY'.1, hY'.2.1⟩

end ReflectedGMS.BoundedVertexRangeAvoidance
