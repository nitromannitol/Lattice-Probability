/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SpatialInfinityAvoidance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement

/-!
# Spatial-infinity avoidance

An end-labelled path with a continuous spatial extension cannot visit an end
whose finite-cut components escape every bounded spatial set, provided vertex
times are dense.  For an actual reflected walk, fixed-time definedness on the
countable rational grid supplies that density almost surely.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

universe u

namespace ReflectedGMS.SpatialInfinityAvoidance

open SpatialEnds ReflectedWalk

variable {V : Type u}

theorem collapse_eq_some_iff {F : IndexedCells V} {x : State F} {v : V} :
    collapse x = some v ↔ x = Sum.inl v := by
  cases x with
  | inl w => simp [collapse]
  | inr e => simp [collapse]

/-- Fixed-time definedness of an actual reflected walk, intersected only over
the rational grid, makes the vertex-valued times of a collapsed lift dense. -/
theorem dense_vertices_ae_of_isReflectedWalk [Countable V]
    (F : IndexedCells V) {w : V → ℝ} {hmin : F.graph.EnergyMinimizer}
    (PF : ProcessFamily V) (hPF : IsReflectedWalk F.graph w hmin PF) (start : V)
    (Y : ℝ≥0 → PF.Ω → State F)
    (hcollapse : ∀ᵐ ω ∂PF.P start, ∀ t, collapse (Y t ω) = PF.X t ω) :
    ∀ᵐ ω ∂PF.P start, Dense {t | ∃ v, Y t ω = Sum.inl v} := by
  have hgrid : ∀ᵐ ω ∂PF.P start, ∀ q : ℚ,
      ∃ v, PF.X (Real.toNNReal (q : ℝ)) ω = some v := by
    refine ae_all_iff.2 fun q => ?_
    exact ((hPF start).2.1 (Real.toNNReal (q : ℝ))).mono fun _ h => h.1
  have hrat : DenseRange (fun q : ℚ => Real.toNNReal (q : ℝ)) := by
    have hsurj : Function.Surjective Real.toNNReal := by
      intro t
      refine ⟨(t : ℝ), NNReal.eq ?_⟩
      exact Real.coe_toNNReal (t : ℝ) t.property
    simpa only [Function.comp_def] using
      hsurj.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  filter_upwards [hcollapse, hgrid] with omega hcollapseω hgridω
  refine hrat.mono ?_
  rintro t ⟨q, rfl⟩
  obtain ⟨v, hv⟩ := hgridω q
  exact ⟨v, collapse_eq_some_iff.mp ((hcollapseω _).trans hv)⟩

end ReflectedGMS.SpatialInfinityAvoidance
