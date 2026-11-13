/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ExponentialAreaEndLift at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.QuenchedFormulation
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds

/-!
# The end-labelled lift of the exponential-area clock

`InvarianceAssembly.PathwiseClockClauses` (the body of the `hlift` input of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`) asserts ten
almost-sure clauses for one common choice of the two lifts `Xexp`, `Xexact` and the
spatial extension `M`.  This file supplies three of them for the **exponential-area**
lift `Xexp`, and supplies them *unconditionally* from the environment hypotheses of the
main theorem, given only the `hdata` walk data:

* `∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω` — `Xexp` lifts the
  canonical exponential-area path;
* `IsEndLabeling (decode e) (fun t => Xexp t ω)`;
* `AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)`.

These are the first, third and fifth conjuncts of `PathwiseClockClauses`, verbatim.

The lift itself is `canonicalExpLift`, a pathwise choice of a lift with the three
properties; on the null set where no such lift exists it is junk.  Its three properties
come from the checked
`LogCutoffSpatialBoundedness.reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity_of_logCutoff`,
routed through `QuenchedFormulation.walkConclusion_of_logCutoff_hypotheses`, whose
logarithmic-cutoff hypothesis tuple is discharged almost surely by the checked
`Spatial.AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` from mass transport, the
finite (FE) moment at the root and the quadratic ball bound on the rooted (FE) density.

## What is *not* done here

The remaining seven conjuncts of `PathwiseClockClauses` — the two clock homeomorphisms,
the exact-holding lift `Xexact` and its two clauses, the exact holding lengths and the
regular spatial extension `M` — are untouched.  Nothing here asserts `hlift`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.ExponentialAreaEndLift

open Code EnvironmentFields EnvironmentLaws StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk QuenchedFormulation

variable (e : Env) [Nontrivial (Vertex e.val)]

open Classical in
/-- The canonical end-labelled lift of the exponential-area path: a pathwise choice of a
lift that is an end labelling and avoids spatial infinity, and junk on the null set where
no such lift exists.  Where it exists the lift is unique, so the choice is harmless. -/
noncomputable def canonicalExpLift (D : (decode e).graph.Exhaustion)
    (ω : Existence.Sample (Vertex e.val)) : ℝ≥0 → State (decode e) :=
  if h : ∃ Y : ℝ≥0 → State (decode e),
      (∀ t, collapse (Y t) = exponentialAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) Y ∧ AvoidsSpatialInfinity (decode e) Y then
    h.choose
  else fun _ => Sum.inl (Classical.arbitrary (Vertex e.val))

theorem canonicalExpLift_spec (D : (decode e).graph.Exhaustion)
    {ω : Existence.Sample (Vertex e.val)}
    (h : ∃ Y : ℝ≥0 → State (decode e),
      (∀ t, collapse (Y t) = exponentialAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) Y ∧ AvoidsSpatialInfinity (decode e) Y) :
    (∀ t, collapse (canonicalExpLift e D ω t) = exponentialAreaPath (decode e) D t ω) ∧
      IsEndLabeling (decode e) (canonicalExpLift e D ω) ∧
      AvoidsSpatialInfinity (decode e) (canonicalExpLift e D ω) := by
  rw [canonicalExpLift, dite_eq_left h]
  exact h.choose_spec

/-- **Three conjuncts of `PathwiseClockClauses`, for one environment and one start.**
Given the area-clock reflected-walk data and the logarithmic-cutoff tuple of manuscript
Proposition `r:prop:log`, the canonical exponential-area lift exists and almost surely
lifts the path, is an end labelling and avoids spatial infinity. -/
theorem exists_expLift_of_logCutoff_hypotheses
    (zf : CellField) (hz : IsCellRepresentative zf)
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    {hmin : (decode e).graph.EnergyMinimizer}
    (hwalk : IsReflectedWalk (decode e).graph (areaRate (decode e)) hmin
      (Existence.processFamily D hG (areaRate (decode e))))
    (hrate : ∀ v, 0 < areaRate (decode e) v) (start : Vertex e.val)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖zf.at e start‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
      Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
      Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN (decode e)
          {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
        ≤ ENNReal.ofReal (C * R ^ 2)) :
    ∃ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
      ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
        (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
        IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
        AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω) := by
  refine ⟨fun t ω => canonicalExpLift e D ω t, ?_⟩
  filter_upwards [walkConclusion_of_logCutoff_hypotheses e zf hz D hG hwalk hrate start
    hr₀ hC ho hD hW] with ω hω
  exact canonicalExpLift_spec e D hω.2.exists

/-- **The same three conjuncts, almost surely in the environment**, in the per-label shape
of the `hlift` input of `InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`.
The logarithmic-cutoff hypotheses are discharged from the manuscript's own environment
assumptions by `Spatial.AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses`; the only
hypothesis about the process is the `hdata` walk data itself, carried in the conclusion. -/
theorem ae_exists_expLift_of_massTransport (ν : Measure Env)
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M)
    (zf : CellField) (hz : IsCellRepresentative zf) (n : ℕ) :
    ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∃ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
          ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
            (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
            IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
            AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω) := by
  filter_upwards [AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses ν hν hFE hMax]
    with e hcute hn hnt D hG hdat
  letI := hnt
  obtain ⟨hmin, hrate, hwalk, -⟩ := hdat
  obtain ⟨r₀, C, hr₀, hC, ho, hDiam, hMass⟩ := hcute (zf.at e) ⟨n, hn⟩
  exact exists_expLift_of_logCutoff_hypotheses e zf hz D hG hwalk hrate ⟨n, hn⟩
    hr₀ hC ho hDiam hMass

end ReflectedGMS.ExponentialAreaEndLift
