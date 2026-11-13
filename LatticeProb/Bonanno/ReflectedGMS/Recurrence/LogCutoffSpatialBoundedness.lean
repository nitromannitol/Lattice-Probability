/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.LogCutoffSpatialBoundedness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.LogCutoffTotalEnergy
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ReturnCycleSpatialBoundedness
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedVertexRangeAvoidance
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# From the logarithmic cutoff to compact-time spatial boundedness and end avoidance

`Recurrence/LogCutoffTotalEnergy.lean` proves the manuscript's Proposition `r:prop:log`
(`LogCutoff.logarithmicCutoff_proposition`): for every number of annuli `n ≥ 1` the clipped
logarithmic cutoff `LogCutoff.cutoff r₀ n z` has finite ordinary edge energy, vanishes at the
root, equals `1` on `{v | 2 ^ n * r₀ ≤ ‖z v‖}`, and satisfies

  `E(cutoff r₀ n z) ≤ 32 * C / (n * (log 2) ^ 2)`.

`Recurrence/ExcursionBoundedRange.lean` consumes exactly the `n → ∞` consequence of this
family, in the packaged form `ExcursionBoundedRange.VanishingFarEnergy G o rho`: for every
`ε > 0` some level `R` admits a finite-energy competitor vanishing at `o`, equal to `1` above
radius `R`, with energy ratio `E(f)/π(o) < ε`.  No adapter between the two existed; this file
supplies it and then assembles the spatial conclusions it unlocks.

The adapter is the *direct* limit: the `(n+1)`-annuli cutoffs are a sequence of competitors
for the levels `R n = 2 ^ (n+1) * r₀`, and their energy ratios are squeezed between `0` and
`(32 * C / ((log 2) ^ 2 * π(o))) / (n+1)`, which tends to `0`.  Positivity of `π(o)` is not a
new hypothesis: the connectedness clause of `Geometry F` together with `Nontrivial V` gives it
through `ConductanceGraph.pi_pos_of_connected`.

The two spatial conclusions are then unconditional in the probabilistic inputs:

* `reflected_ae_forall_bddAbove_norm_on_boundedTime` — manuscript Proposition
  `r:prop:criterion` for the actual reflected walk with the *actual* spatial radius
  `rho = fun v => ‖z v‖` of cell representatives, obtained from
  `ReturnCycleSpatialBoundedness.ae_forall_bddAbove_rho_on_boundedTime`;
* `reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity_of_logCutoff` — the
  end-avoidance corollary, obtained from
  `BoundedVertexRangeAvoidance.reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity`,
  whose compact-time bounded-vertex-range hypothesis is exactly the previous conclusion.

Localization uses `StatementIngredients.CellRepresentatives F z`, i.e. `z v ∈ F.cell v` for
every `v`; no claim is made that a centroid lies in its (merely connected) cell.  The
deterministic local diameter hypothesis `hD` and the quadratic local mass hypothesis `hW` are
carried verbatim from `LogCutoffTotalEnergy`; nothing is assumed about how `hW` is produced.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.LogCutoffSpatialBoundedness

open ReflectedWalk

universe u

section Deterministic

variable {V : Type u} [Countable V] [Nontrivial V]

/-- **The `n → ∞` limit of the logarithmic cutoff energies.**  Under the hypotheses of
manuscript Proposition `r:prop:log` the energy ratios `E(cutoff r₀ (n+1) z)/π(o)` tend to
zero: they are nonnegative and bounded by `(32 C/((log 2)^2 π(o)))/(n+1)`. -/
theorem tendsto_cutoff_energy_div_pi_atTop
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z) (o : V)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ => F.graph.Energy (LogCutoff.cutoff r₀ (n + 1) z) / F.graph.pi o)
      Filter.atTop (nhds 0) := by
  have hG : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  have hpi : 0 < F.graph.pi o := F.graph.pi_pos_of_connected hG o
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlimit : Filter.Tendsto
      (fun n : ℕ => (32 * C / ((Real.log 2) ^ 2 * F.graph.pi o)) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat
          (32 * C / ((Real.log 2) ^ 2 * F.graph.pi o))).comp
        (Filter.tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hlimit
  · exact div_nonneg (F.graph.Energy_nonneg (LogCutoff.cutoff r₀ (n + 1) z)) hpi.le
  · have hb : F.graph.Energy (LogCutoff.cutoff r₀ (n + 1) z) ≤
        32 * C / (((n + 1 : ℕ) : ℝ) * (Real.log 2) ^ 2) :=
      LogCutoff.cutoff_energy_le (V := V) F hF z hz hr₀ hC (n := n + 1)
        (Nat.le_add_left 1 n) hD hW
    have h1 : F.graph.Energy (LogCutoff.cutoff r₀ (n + 1) z) / F.graph.pi o ≤
        (32 * C / (((n + 1 : ℕ) : ℝ) * (Real.log 2) ^ 2)) / F.graph.pi o :=
      (div_le_div_iff_of_pos_right hpi).2 hb
    refine h1.trans_eq ?_
    rw [div_div, div_div]
    congr 1
    ring

/-- **The direct adapter.**  Manuscript Proposition `r:prop:log` supplies the
vanishing-energy hypothesis of the spatial cutoff criterion for the actual radius of cell
representatives, `rho = fun v => ‖z v‖`.

The competitors are the cutoffs with `n+1` annuli and the levels `2 ^ (n+1) * r₀`; the far
value `1` of `cutoff` holds on `{2 ^ (n+1) * r₀ ≤ ‖z v‖}`, hence in particular strictly above
that level.  All hypotheses are those of `r:prop:log`: `r₀ > 0`, `C ≥ 0`, `‖z o‖ ≤ r₀`, the
local diameter bound and the quadratic local mass bound. -/
theorem vanishingFarEnergy_norm_of_logCutoff
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z) (o : V)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖z o‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    ExcursionBoundedRange.VanishingFarEnergy F.graph o (fun v : V => ‖z v‖) := by
  have hfE : ∀ n : ℕ, F.graph.HasFiniteEnergy (LogCutoff.cutoff r₀ (n + 1) z) :=
    fun n => LogCutoff.cutoff_hasFiniteEnergy (V := V) F hF z hz hr₀ hC (n := n + 1)
      (Nat.le_add_left 1 n) hD hW
  have hfo : ∀ n : ℕ, LogCutoff.cutoff r₀ (n + 1) z o = 0 :=
    fun n => LogCutoff.cutoff_eq_zero (V := V) hr₀ (n + 1) z ho
  have hfR : ∀ n : ℕ, ∀ y : V, (2 : ℝ) ^ (n + 1) * r₀ < ‖z y‖ →
      LogCutoff.cutoff r₀ (n + 1) z y = 1 :=
    fun n y hy => LogCutoff.cutoff_eq_one (V := V) hr₀ (n := n + 1) (Nat.le_add_left 1 n) z
      (le_of_lt hy)
  exact ExcursionBoundedRange.vanishingFarEnergy_of_tendsto
    (G := F.graph) (o := o) (rho := fun v : V => ‖z v‖)
    (fun n : ℕ => (2 : ℝ) ^ (n + 1) * r₀)
    (fun n : ℕ => LogCutoff.cutoff r₀ (n + 1) z)
    hfE hfo hfR (tendsto_cutoff_energy_div_pi_atTop F hF z hz o hr₀ hC hD hW)

end Deterministic

section Process

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V]

/-- **Manuscript Proposition `r:prop:criterion` for the actual spatial radius.**  For the
actual reflected walk started at `o`, under the hypotheses of Proposition `r:prop:log`, almost
surely the norms of the cell representatives of the visited vertices are bounded on every
bounded time interval, simultaneously for all finite horizons.

The vanishing-energy input is discharged by `vanishingFarEnergy_norm_of_logCutoff`; no
spatial local finiteness, no spatial extension and no new path law is used. -/
theorem reflected_ae_forall_bddAbove_norm_on_boundedTime
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z)
    {w : V → ℝ} {hmin : F.graph.EnergyMinimizer} (PF : ProcessFamily V)
    (hPF : IsReflectedWalk F.graph w hmin PF) (hw : ∀ v, 0 < w v) (o : V)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖z o‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    ∀ᵐ ω ∂(PF.P o), ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t : ℝ≥0, t ≤ T →
      ∀ v : V, PF.X t ω = some v → ‖z v‖ ≤ M := by
  have hG : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  have hvan : ExcursionBoundedRange.VanishingFarEnergy F.graph o (fun v : V => ‖z v‖) :=
    vanishingFarEnergy_norm_of_logCutoff F hF z hz o hr₀ hC ho hD hW
  filter_upwards [ReturnCycleSpatialBoundedness.ae_forall_bddAbove_rho_on_boundedTime
    (G := F.graph) (w := w) (hmin := hmin) (PF := PF) hPF hG hw
    (o := o) (rho := fun v : V => ‖z v‖) hvan] with ω hω
  intro T
  obtain ⟨M, hM⟩ := hω T
  exact ⟨M, fun t ht v hv => hM t ht v hv⟩

/-- **The end-avoidance corollary for the logarithmic cutoff.**  Almost every trajectory of
the actual reflected walk started at `o` has a unique end-labelled lift, and that lift avoids
every spatially escaping graph end.

All probabilistic inputs are actual results about the reflected walk: rational-time vertex
density, finite-cut pathwise component stabilization, and the return-cycle spatial bound whose
vanishing-energy hypothesis is now supplied by manuscript Proposition `r:prop:log`.  This is
pathwise existence and uniqueness; no measurable selection of lifts and no continuous spatial
extension is claimed. -/
theorem reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity_of_logCutoff
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z)
    {w : V → ℝ} {hmin : F.graph.EnergyMinimizer} (PF : ProcessFamily V)
    (hPF : IsReflectedWalk F.graph w hmin PF) (hw : ∀ v, 0 < w v) (o : V)
    {r₀ C : ℝ} (hr₀ : 0 < r₀) (hC : 0 ≤ C) (ho : ‖z o‖ ≤ r₀)
    (hD : ∀ R : ℝ, r₀ ≤ R → ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
      Metric.diam (F.cell v : Set Plane) ≤ R / 100)
    (hW : ∀ R : ℝ, r₀ ≤ R →
      LogCutoff.localMassENN F {v : V | Hits F (Metric.closedBall (0 : Plane) R) v} ≤
        ENNReal.ofReal (C * R ^ 2)) :
    ∀ᵐ ω ∂(PF.P o), ∃! Y : ℝ≥0 → SpatialEnds.State F,
      (∀ t, SpatialEnds.collapse (Y t) = PF.X t ω) ∧
      SpatialEnds.IsEndLabeling F Y ∧ SpatialEnds.AvoidsSpatialInfinity F Y := by
  have hG : F.graph.toSimpleGraph.Connected := hF.2.2.2.2.2.1
  exact BoundedVertexRangeAvoidance.reflected_ae_existsUnique_endLabelLift_avoidsSpatialInfinity
    (V := V) F z hz (w := w) (hmin := hmin) PF hPF hG hw o
    (reflected_ae_forall_bddAbove_norm_on_boundedTime F hF z hz PF hPF hw o hr₀ hC ho hD hW)

end Process

end ReflectedGMS.LogCutoffSpatialBoundedness
