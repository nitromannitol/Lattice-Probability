/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.HarmonicMeasureBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DiscreteHarmonicMeasure
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveProperties
import LatticeProb.Bonanno.BouRabeeGwynne.LevyProkhorovMaps

/-!
# Section 4: exit expectations and stopped-curve endpoints

These identities refer to the actual trajectory measure, its first exit vertex,
and the normalized polygonal curve. The boundary perturbation estimate is the
finite probabilistic step used when a smooth harmonic approximation replaces a
continuous boundary test function.
-/

open MeasureTheory ProbabilityTheory

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
variable (N : FiniteConductanceNetwork V)

/-- The endpoint distribution of the actual stopped polygonal walk is its
first-exit harmonic measure, mapped to the spatial embedding. -/
theorem stoppedPolygonalCurve_map_endPoint {d : ℕ} (pos : V → Euc d)
    (A : Set V) (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ((N.trajectoryLaw A hpos v).map (stoppedPolygonalCurve pos A)).map
        CurveSpace.endPoint =
      (N.discreteHarmonicMeasure A hpos v).map pos := by
  rw [Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedPolygonalCurve pos A)]
  rw [discreteHarmonicMeasure,
    Measure.map_map (measurable_of_finite pos) (measurable_exitVertex A)]
  congr 1
  funext ω
  exact stoppedPolygonalCurve_endPoint pos A ω

/-- Replacing the boundary data changes its actual exit expectation by at most
the uniform boundary error. This also allows a separate approximation error at
the starting point. -/
theorem abs_integral_discreteHarmonicMeasure_sub_le (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    {g h f : V → ℝ} (hf : N.SolvesDirichlet A h f) {η : ℝ}
    (hboundary : ∀ w, w ∉ A → |g w - h w| ≤ η) (v : V) (target : ℝ) :
    |(∫ w, g w ∂N.discreteHarmonicMeasure A hpos v) - target| ≤
      η + |f v - target| := by
  rw [N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess
    (N.dirichletSolution_spec A haccess g) v]
  exact (abs_sub_le (N.dirichletSolution A haccess g v) (f v) target).trans
    (add_le_add (N.dirichlet_stability A haccess
      (N.dirichletSolution_spec A haccess g) hf hboundary v) le_rfl)

/-- A strict interior Dirichlet approximation bound combines with the boundary
test error without changing either quantifier or normalization. -/
theorem abs_integral_discreteHarmonicMeasure_sub_lt (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    {g h f : V → ℝ} (hf : N.SolvesDirichlet A h f) {η ρ : ℝ}
    (hboundary : ∀ w, w ∉ A → |g w - h w| ≤ η) (v : V) (target : ℝ)
    (herror : |f v - target| < ρ) :
    |(∫ w, g w ∂N.discreteHarmonicMeasure A hpos v) - target| < η + ρ :=
  (N.abs_integral_discreteHarmonicMeasure_sub_le A hpos haccess hf hboundary
    v target).trans_lt (add_lt_add_of_le_of_lt le_rfl herror)

end BouRabeeGwynne.FiniteConductanceNetwork
