/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.AreaClockFastSpeedOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockLevelZeroFiniteness
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockLocalFiniteness
import Mathlib.Data.Finsupp.Encodable

/-!
# The area clock as an occupation clock of a *summable-speed* fast walk

`EnvironmentWalkDataProducer.EnvironmentAreaClockAdmissible` is the sole open input behind
the `hdata` clause of the invariance assembly.  By
`AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_iff_environmentWalkData` it is
*equivalent* to `hdata`, so it is the one obligation left.  This file repairs the route to it.

## Why the two routes on record do not work as stated

* **Lemma 3.5 domination.**  `Exhaustion.rateFunction_ae_holdingTimesSummable` needs
  `areaRate ≥ D.rateFunction hG` off a finite set.  `D.rateFunction x = max 1 (layerBound (nz x))`
  and `layerBound` is a finite sum of `layerConst`s, each a `Classical.choose` from
  `exists_layerConst` **for the same `D`**.  Two separate obstructions, not one:
  (i) the constant produced by `exists_layer_threshold` is `max 1 (m₀ / c₀)` with
  `c₀ = (2⁻ⁿ / |B|)`, so it grows at least geometrically in the layer index for *every*
  exhaustion, while `areaRate = π/a` is a fixed function of the environment with no growth at
  all (for a unit-square tiling it is constant); and (ii) nothing but positivity of
  `Classical.choose` is available, so no *upper* bound on `layerBound` is even expressible.
  Re-choosing `D` to outrun its own `layerBound` is circular, because `layerConst` depends on
  the whole exhaustion (through `E.coupling`), not on its first levels.  **This route is
  abandoned, and not because it is hard: the hypothesis it needs is not provable.**

* **The occupation route as previously scoped.**  `AreaClockLocalFiniteness` is stated for a
  *general* speed measure `m` with `IsReflectedWalk G (fun v => G.pi v / m v) hmin PF` and
  `hmsum : Summable m`.  Read at `m = cellArea F` — the reading that makes the rate literally
  `AreaClocks.areaRate` — it is doubly unusable: `IsReflectedWalk` at the area rate is exactly
  what is to be proved, and `Summable (cellArea F)` is **false** at the canonical data (the
  cells are compact and cover the plane, so their total area is infinite; compare the standing
  note on `canonicalBracket_of_parts`).

## The repair: read the same theorems at a *different* `m`

The speed measure is not forced to be the cell area.  `IsReflectedWalk` holds unconditionally
for **every** rate above `D.rateFunction` (`Forms.canonical_isReflectedWalk_of_rate_le`), and
`FullNetworkForm.exists_summable_fast_speed` produces such a rate `w` whose speed measure
`m = π/w` is **summable**.  For that pair:

* `IsReflectedWalk G (fun v => G.pi v / m v) hmin (Existence.processFamily D hG w)` holds with
  no open input at all (`isReflectedWalk_pi_div_speed` below);
* `hmsum : Summable m` holds by construction;
* the occupation density of `AreaClockLocalFiniteness.areaClock F m PF` is
  `cellArea F v / m v = cellArea F v * w v / π v`, and against the vertex speed measure
  `m` its integral is `∑ cellArea F v` over the cells hitting a ball — i.e. exactly the
  **local** area summability of `Process/LocalAreaSummability`, which is true, rather than the
  global one, which is false.

So `AreaClockLocalFiniteness.areaClock_finite_on_compact_times` becomes instantiable, and it
gives, for a.e. path and **every** horizon `T`, that `areaClock F m PF T ω < ∞`.

## The pathwise comparison, proved here

`tsum_below_mul_le_setLIntegral` is the deterministic half: for the horizon
`T = tau … w … η` — finite with no open input, by `ae_tau_lt_top_of_rateFunction_le` — the fast
holding windows `[τ_ξ, τ_ξ̂) ⊆ [0,T]` of the indices `ξ < η` are pairwise disjoint (this is
`Consistent.inInterval_unique`) and the fast path is constantly `Y_ξ` on each, so

`∑_{ξ < η} q(Y_ξ) · T^w_ξ ≤ ∫₀ᵀ q(X_s) ds`

for every density `q`.  At `q = cellArea F / m` with `m = π/w` the summand is exactly the
**area** holding time of `ξ` (`holding_areaRate_eq`), because
`(cellArea/(π/w)) · (E_ξ/w) = E_ξ · cellArea/π = E_ξ / areaRate`.  Summing gives
`tau … (areaRate F) … η ≤ areaClock F m PF T ω`.  No probability and no geometry enter.

## What is left

Only the three geometric inputs of `AreaClockLocalFiniteness.areaClock_finite_on_compact_times`,
each with a known producer and none of them about clocks:
`hzrep` (a choice of cell representatives), `hD`
(`Spatial.ae_maxDiamHittingBall_finite_and_sublinear`) and `hvan`
(`Recurrence.LogCutoffTotalEnergy.logarithmicCutoff_proposition` through
`ExcursionBoundedRange.vanishingFarEnergy_of_tendsto`).  They are bundled as
`EnvironmentAreaClockGeometry`, and `environmentAreaClockAdmissible_of_geometry` derives the
whole residual from them.  Nothing below asserts them.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AreaClockFastSpeedOccupation

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk ReflectedWalk.IndexSet
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.InvarianceAssemblyNoReturn ReflectedGMS.AreaClockLevelZeroFiniteness

universe u

/-! ## The fast walk with a summable speed measure -/

section FastSpeed

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **A rate above `w*` whose speed measure is summable always exists.**  This is
`FullNetworkForm.exists_summable_fast_speed` at the rate function of Lemma 3.5; it is recorded
here in the exact shape consumed below, to make plain that the `w` of every statement in this
file is free — it costs no hypothesis on the environment. -/
theorem exists_rate_summable_speed (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected) :
    ∃ w : V → ℝ, (∀ v, 0 < w v) ∧ (∀ v, D.rateFunction hG v ≤ w v) ∧
      Summable fun v => G.pi v / w v := by
  obtain ⟨w, hpos, hdom, _, hsum⟩ :=
    FullNetworkForm.exists_summable_fast_speed G hG (D.rateFunction hG) (D.rateFunction_pos hG)
  exact ⟨w, hpos, hdom, hsum⟩

/-- `π / (π / w) = w`: the rate attached to the speed measure `m = π/w` is `w` again. -/
theorem pi_div_pi_div_eq (hG : G.toSimpleGraph.Connected) (w : V → ℝ) :
    (fun v => G.pi v / (G.pi v / w v)) = w := by
  funext v
  have hpi : G.pi v ≠ 0 := (G.pi_pos_of_connected hG v).ne'
  rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self hpi, mul_one]

/-- **The fast walk is a reflected walk for the speed measure `m = π/w`, unconditionally.**
This is the hypothesis `h` of every theorem of `Process/AreaClockLocalFiniteness`, in the form
that file takes it, with no open input: `Forms.canonical_isReflectedWalk_of_rate_le` needs only
that `w` dominates `D.rateFunction`. -/
theorem isReflectedWalk_pi_div_speed (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    (hmin : G.EnergyMinimizer) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, D.rateFunction hG v ≤ w v) :
    IsReflectedWalk G (fun v => G.pi v / (G.pi v / w v)) hmin
      (Existence.processFamily D hG w) := by
  rw [pi_div_pi_div_eq hG w]
  exact canonical_isReflectedWalk_of_rate_le D hG hmin w hw hdom

/-- The speed measure `m = π/w` is strictly positive. -/
theorem pi_div_pos (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ v, 0 < w v) (v : V) :
    0 < G.pi v / w v :=
  div_pos (G.pi_pos_of_connected hG v) (hw v)

/-- **(3.16) for the fast clock, unconditionally.**  `{x | w x < D.rateFunction hG x}` is empty
when `w` dominates, so Lemma 3.5 applies with no finiteness side condition. -/
theorem ae_holdingTimesSummable_of_rateFunction_le (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2 := by
  have hfin : {x : V | w x < D.rateFunction hG x}.Finite := by
    have he : {x : V | w x < D.rateFunction hG x} = (∅ : Set V) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hdom x
    rw [he]
    exact Set.finite_empty
  exact D.rateFunction_ae_holdingTimesSummable hG w hw hfin (D.nz z) (D.mem_Gsub_nz z)

/-- **The horizon of the occupation comparison is finite, with no open input.**  For the fast
clock every level-`0` index is reached in finite time; this is the `T` that
`AreaTimeDominatedByOccupation` is meant to be applied with. -/
theorem ae_tau_lt_top_of_rateFunction_le (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w ω.2
        (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤ := by
  filter_upwards [ae_holdingTimesSummable_of_rateFunction_le D hG w hw hdom z] with ω hω K
  obtain ⟨-, h2⟩ := hω
  exact h2 _ (realized_addr _ _ 0 K)

end FastSpeed

/-! ## The occupation comparison, deterministic core -/

section Occupation

variable {V : Type u}

open Classical in
/-- The fast-clock holding window `[τ_ξ, τ_ξ̂) ⊆ ℝ` of an index `ξ` lying strictly below `η`;
the empty set for every other index. -/
noncomputable def window (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (η a : ℕ →₀ ℕ) : Set ℝ :=
  if a ∈ below Gs Y η then
    Set.Ico (tau Gs Y w Eh a).toReal (tau Gs Y w Eh (succ Gs Y a)).toReal
  else ∅

theorem window_of_mem (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (Eh : (ℕ →₀ ℕ) → ℝ)
    {η a : ℕ →₀ ℕ} (ha : a ∈ below Gs Y η) :
    window Gs Y w Eh η a =
      Set.Ico (tau Gs Y w Eh a).toReal (tau Gs Y w Eh (succ Gs Y a)).toReal := by
  unfold window
  exact if_pos ha

theorem window_of_notMem (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (Eh : (ℕ →₀ ℕ) → ℝ)
    {η a : ℕ →₀ ℕ} (ha : a ∉ below Gs Y η) : window Gs Y w Eh η a = ∅ := by
  unfold window
  exact if_neg ha

theorem measurableSet_window (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (η a : ℕ →₀ ℕ) : MeasurableSet (window Gs Y w Eh η a) := by
  by_cases ha : a ∈ below Gs Y η
  · rw [window_of_mem Gs Y w Eh ha]
    exact measurableSet_Ico
  · rw [window_of_notMem Gs Y w Eh ha]
    exact MeasurableSet.empty

/-- `τ_ξ` is finite for every `ξ` below a `η` with finite clock. -/
theorem tau_ne_top_of_mem_below (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) {η a : ℕ →₀ ℕ} (ha : a ∈ below Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) : tau Gs Y w Eh a ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (tau_mono Gs Y w Eh ha.2.le)

/-- `τ_ξ̂ ≤ τ_η` for `ξ < η`: the holding window of `ξ` closes before `η` starts. -/
theorem tau_succ_le_of_mem_below (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η a : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (ha : a ∈ below Gs Y η) : tau Gs Y w Eh (succ Gs Y a) ≤ tau Gs Y w Eh η :=
  hc.tau_succ_le Gs Y w Eh hGm hcov ha.1 hη ha.2

/-- A real time in the window of `ξ` lies in the holding interval `[τ_ξ, τ_ξ̂)` of (3.26). -/
theorem inInterval_of_mem_window (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) {a : ℕ →₀ ℕ} {s : ℝ} (hs : s ∈ window Gs Y w Eh η a) :
    InInterval Gs Y w Eh a (ENNReal.ofReal s) := by
  by_cases ha : a ∈ below Gs Y η
  · rw [window_of_mem Gs Y w Eh ha] at hs
    obtain ⟨h1, h2⟩ := hs
    have hs0 : (0 : ℝ) ≤ s := le_trans ENNReal.toReal_nonneg h1
    have hta : tau Gs Y w Eh a ≠ ⊤ := tau_ne_top_of_mem_below Gs Y w Eh ha hfin
    have hts : tau Gs Y w Eh (succ Gs Y a) ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (tau_succ_le_of_mem_below Gs Y w Eh hc hGm hcov hη ha)
    refine ⟨ha.1, ?_, ?_⟩
    · rw [← ENNReal.ofReal_toReal hta]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [← ENNReal.ofReal_toReal hts]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0).2 h2
  · rw [window_of_notMem Gs Y w Eh ha] at hs
    exact hs.elim

/-- **The deterministic occupation bound.**  For every nonnegative density `q` and every
realised `η` with finite fast clock, the `q`-weighted sum of the fast holding times below `η`
is at most the occupation integral of `q` along the path on `[0, τ_η]`.

The proof is the disjointness of the holding intervals (`Consistent.inInterval_unique`), the
identification of the path on each of them (`Consistent.X_eq_of_inInterval`) and
`τ_ξ̂ = τ_ξ + T_ξ` (`PathProperties.tau_succ`).  No probability enters. -/
theorem tsum_below_mul_le_setLIntegral (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (Eh : (ℕ →₀ ℕ) → ℝ) (hc : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (q : V → ℝ≥0∞) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η)
    (hfin : tau Gs Y w Eh η ≠ ⊤) :
    ∑' a, (below Gs Y η).indicator
        (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a ≤
      ∫⁻ s in Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal,
        (X Gs Y w Eh (Real.toNNReal s)).elim 0 q := by
  have hterm : ∀ a, (below Gs Y η).indicator
      (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a ≤
      ∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q := by
    intro a
    by_cases ha : a ∈ below Gs Y η
    · have hta : tau Gs Y w Eh a ≠ ⊤ := tau_ne_top_of_mem_below Gs Y w Eh ha hfin
      have hvol : volume (window Gs Y w Eh η a) = holding Gs Y w Eh a := by
        rw [window_of_mem Gs Y w Eh ha, Real.volume_Ico,
          PathProperties.tau_succ Gs Y w Eh hc hGm hcov ha.1,
          ENNReal.toReal_add hta (holding_ne_top Gs Y w Eh a), add_sub_cancel_left]
        exact ENNReal.ofReal_toReal (holding_ne_top Gs Y w Eh a)
      simp only [Set.indicator_of_mem ha]
      calc q (Yxi Gs Y a) * holding Gs Y w Eh a
          = ∫⁻ _s in window Gs Y w Eh η a, q (Yxi Gs Y a) := by
            rw [setLIntegral_const, hvol]
        _ ≤ ∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q := by
            refine lintegral_mono_ae ?_
            filter_upwards [self_mem_ae_restrict (measurableSet_window Gs Y w Eh η a)] with s hs
            rw [hc.X_eq_of_inInterval Gs Y w Eh hGm hcov
              (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hs)]
            exact le_rfl
    · simp only [Set.indicator_of_notMem ha]
      exact zero_le
  have hdisj : Pairwise (Function.onFun Disjoint (window Gs Y w Eh η)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro s hsa hsb
    exact hab (hc.inInterval_unique Gs Y w Eh hGm hcov
      (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hsa)
      (inInterval_of_mem_window Gs Y w Eh hc hGm hcov hη hfin hsb))
  have hsub : (⋃ a, window Gs Y w Eh η a) ⊆ Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal := by
    intro s hs
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hs
    by_cases hab : a ∈ below Gs Y η
    · rw [window_of_mem Gs Y w Eh hab] at ha
      refine ⟨le_trans ENNReal.toReal_nonneg ha.1, le_trans ha.2.le ?_⟩
      exact ENNReal.toReal_mono hfin (tau_succ_le_of_mem_below Gs Y w Eh hc hGm hcov hη hab)
    · rw [window_of_notMem Gs Y w Eh hab] at ha
      exact ha.elim
  calc ∑' a, (below Gs Y η).indicator (fun b => q (Yxi Gs Y b) * holding Gs Y w Eh b) a
      ≤ ∑' a, ∫⁻ s in window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q :=
        ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ s in ⋃ a, window Gs Y w Eh η a, (X Gs Y w Eh (Real.toNNReal s)).elim 0 q :=
        (lintegral_iUnion (measurableSet_window Gs Y w Eh η) hdisj _).symm
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) (tau Gs Y w Eh η).toReal,
          (X Gs Y w Eh (Real.toNNReal s)).elim 0 q :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end Occupation

/-! ## The area clock as the occupation clock of the fast walk -/

section AreaOccupation

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] [DecidableEq V]

/-- **The pointwise time-change identity.**  The area holding time of `ξ` is the fast holding
time of `ξ` times the area-clock density `cellArea/m` at `Y_ξ`, for the speed measure
`m = π/w`: `(a/(π/w)) · (E_ξ/w) = E_ξ · a/π = E_ξ / areaRate`. -/
theorem holding_areaRate_eq (F : IndexedCells V) (hF : Geometry F)
    (hG : F.graph.toSimpleGraph.Connected) (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (Eh : (ℕ →₀ ℕ) → ℝ) (a : ℕ →₀ ℕ) :
    holding Gs Y (areaRate F) Eh a =
      AreaClockLocalFiniteness.areaClockDensity F (fun v => F.graph.pi v / w v)
          (Yxi Gs Y a) * holding Gs Y w Eh a := by
  have hpi : F.graph.pi (Yxi Gs Y a) ≠ 0 :=
    (F.graph.pi_pos_of_connected hG (Yxi Gs Y a)).ne'
  have harea : cellArea F (Yxi Gs Y a) ≠ 0 := (cellArea_pos F hF (Yxi Gs Y a)).ne'
  have hwv : w (Yxi Gs Y a) ≠ 0 := (hw (Yxi Gs Y a)).ne'
  have hnn : (0 : ℝ) ≤ cellArea F (Yxi Gs Y a) /
      (F.graph.pi (Yxi Gs Y a) / w (Yxi Gs Y a)) :=
    div_nonneg (cellArea_pos F hF (Yxi Gs Y a)).le
      (div_pos (F.graph.pi_pos_of_connected hG (Yxi Gs Y a)) (hw (Yxi Gs Y a))).le
  simp only [holding, AreaClockLocalFiniteness.areaClockDensity, areaRate,
    ← ENNReal.ofReal_mul hnn]
  congr 1
  first
  | (field_simp; ring)
  | field_simp

/-- **The area clock at a level-`0` index is dominated by the fast walk's occupation clock.**
Almost surely, for every `K`, with the horizon `T = τ^w_{[(0,K)]}` — finite by
`ae_tau_lt_top_of_rateFunction_le`, with no open input. -/
theorem ae_tau_areaRate_le_areaClock (F : IndexedCells V) (hF : Geometry F)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ, ∃ T : ℝ≥0,
      tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
          (addr (D.levelSets (D.nz z)) ω.1 0 K) ≤
        AreaClockLocalFiniteness.areaClock F (fun v => F.graph.pi v / w v)
          (Existence.processFamily D hG w) T ω := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z,
    ae_tau_lt_top_of_rateFunction_le D hG w hw hdom z] with ω hcons hstart hfin K
  refine ⟨(tau (D.levelSets (D.nz z)) ω.1 w ω.2
    (addr (D.levelSets (D.nz z)) ω.1 0 K)).toNNReal, ?_⟩
  have hbound := tsum_below_mul_le_setLIntegral (D.levelSets (D.nz z)) ω.1 w ω.2 hcons
    (D.levelSets_mono (D.nz z)) (D.exists_mem_levelSets (D.nz z))
    (AreaClockLocalFiniteness.areaClockDensity F (fun v => F.graph.pi v / w v))
    (realized_addr _ _ 0 K) (hfin K).ne
  have hEq : tau (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2
        (addr (D.levelSets (D.nz z)) ω.1 0 K) =
      ∑' a, (below (D.levelSets (D.nz z)) ω.1
          (addr (D.levelSets (D.nz z)) ω.1 0 K)).indicator
        (fun b => AreaClockLocalFiniteness.areaClockDensity F
            (fun v => F.graph.pi v / w v) (Yxi (D.levelSets (D.nz z)) ω.1 b) *
          holding (D.levelSets (D.nz z)) ω.1 w ω.2 b) a := by
    unfold tau
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ below (D.levelSets (D.nz z)) ω.1
        (addr (D.levelSets (D.nz z)) ω.1 0 K)
    · simp only [Set.indicator_of_mem ha]
      exact holding_areaRate_eq F hF hG _ _ w hw _ a
    · simp only [Set.indicator_of_notMem ha]
  have hXeq : ∀ t : ℝ≥0, X (D.levelSets (D.nz z)) ω.1 w ω.2 t = Existence.process D w t ω :=
    fun t => (Existence.process_eq D w (hstart 0) hcons t).symm
  rw [hEq]
  refine le_trans hbound (le_of_eq (lintegral_congr fun s => ?_))
  exact congrArg (fun o : Option V => Option.elim o 0
    (AreaClockLocalFiniteness.areaClockDensity F (fun v => F.graph.pi v / w v)))
    (hXeq (Real.toNNReal s))

end AreaOccupation

/-! ## The residual clock clause of `hdata`, from the occupation route -/

section Environment

variable (e : Env) [Nontrivial (Vertex e.val)]

/-- **The residual clock clause of `hdata`, from the geometric inputs alone.**  `hzrep`, `hD`,
`hvan` are exactly the hypotheses of
`AreaClockLocalFiniteness.areaClock_finite_on_compact_times`; the rate `w` and its summable
speed measure are supplied internally by `exists_rate_summable_speed`, and the comparison
between the area clock and the fast walk's occupation clock by
`ae_tau_areaRate_le_areaClock`.  No clock hypothesis is carried. -/
theorem areaClockReachesLevelZeroIndices_of_vanishingFarEnergy
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (zrep : Vertex e.val → Plane) (hzrep : CellRepresentatives (decode e) zrep)
    (hD : ∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall (decode e) R < ∞)
    (hvan : ∀ o : Vertex e.val,
      ExcursionBoundedRange.VanishingFarEnergy (decode e).graph o fun v => ‖zrep v‖) :
    AreaClockReachesLevelZeroIndices e D hG := by
  obtain ⟨w, hw, hdom, hmsum⟩ := exists_rate_summable_speed D hG
  intro z
  have hfin : ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ T : ℝ≥0,
      AreaClockLocalFiniteness.areaClock (decode e)
          (fun v => (decode e).graph.pi v / w v) (Existence.processFamily D hG w) T ω < ∞ :=
    AreaClockLocalFiniteness.areaClock_finite_on_compact_times (decode e)
      (isReflectedWalk_pi_div_speed D hG (energyMinimizer e) w hw hdom)
      (decode_geometry e) (pi_div_pos hG w hw) hmsum zrep hzrep hD z (hvan z)
  filter_upwards [hfin,
    ae_tau_areaRate_le_areaClock (decode e) (decode_geometry e) D hG w hw hdom z]
    with ω h1 h2 K
  obtain ⟨T, hT⟩ := h2 K
  exact lt_of_le_of_lt hT (h1 T)

end Environment

/-- **The per-environment geometric inputs of the occupation route, bundled.**  Existence of
the exhaustion is free (`ReflectedWalk.Existence.exists_exhaustion`) and so is the fast rate
(`exists_rate_summable_speed`); what is left is a choice of cell representatives, finiteness of
the largest cell diameter meeting each ball, and vanishing far-field energy — no clock, no
process, no probability. -/
def EnvironmentAreaClockGeometry (e : Env) : Prop :=
  letI := nontrivial_vertex e
  ∃ zrep : Vertex e.val → Plane,
    CellRepresentatives (decode e) zrep ∧
    (∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall (decode e) R < ∞) ∧
    ∀ o : Vertex e.val,
      ExcursionBoundedRange.VanishingFarEnergy (decode e).graph o fun v => ‖zrep v‖

/-- **The environment-level residual, discharged from the geometric inputs.** -/
theorem environmentAreaClockAdmissible_of_geometry (e : Env)
    (h : EnvironmentAreaClockGeometry e) : EnvironmentAreaClockAdmissible e := by
  letI := nontrivial_vertex e
  obtain ⟨zrep, hzrep, hD, hvan⟩ := h
  obtain ⟨D⟩ := Existence.exists_exhaustion (decode_connected e)
  exact ⟨D, areaClockReachesLevelZeroIndices_of_vanishingFarEnergy e D (decode_connected e)
    zrep hzrep hD hvan⟩

/-- **`hdata` for the invariance assembly, from the geometric inputs.**  The conclusion is the
`hdata` clause of `InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`, copied
verbatim. -/
theorem ae_environmentWalkData_of_ae_geometry (ν : Measure Env)
    (hinp : ∀ᵐ e ∂ν, EnvironmentAreaClockGeometry e) :
    ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG :=
  ae_environmentWalkData_of_ae_areaClockAdmissible ν
    (hinp.mono fun e he => environmentAreaClockAdmissible_of_geometry e he)

end ReflectedGMS.AreaClockFastSpeedOccupation
