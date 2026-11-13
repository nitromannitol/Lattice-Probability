/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.FlowSpaceTimeScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowGateRootChainGate
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowSpaceBlockSystem
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FlowCodingKernel
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# The concrete gated local time scale on the flow carrier

`Temporal/FlowSpaceBlockSystem.gatedRootChainBlocks_of_localTimeScaleOn` produces the gated block
data of the root-chain system from a covariant local time scale
`LocalTimeScaleOn G reRootFlow reScale τ` on `FlowSpace = Env × (CadlagPath ℕ∞ × CadlagPath Plane)`,
and `Temporal/FlowGateRootChainGate.scaledRootChainSystemOn_markedFlowGate` wants that data on the
gate `flowGate` itself.  This module builds such a `τ`, on the gate `flowGate`, with no path gate.

## The time scale

For a compact cell `K` and a point `x`, the **reach** of `K` from `x` is
`(diam K - dist(x, K))⁺`, and the **spatial scale** of an environment at `x` is the supremal reach
of its cells:
```
  ρ(e, x) = sup_H (diam H - dist(x, H))⁺ ∈ (0, ∞],        τ(ω, u) = ρ(e, Z_u)²,
```
where `ω = (e, Y, Z)` and `Z` is the position path.
* **Covariance, at every point** (`spatialScale_of_isSimilarity`): under the canonical similarity
  `z ↦ s (z - u)` of an environment, `ρ` is multiplied by `s`, so the re-rooting flow (a unit-scale
  translation by the displacement, `flowTimeScale_shift`) moves `τ` in time and the parabolic
  scaling multiplies it by `C²` (`flowTimeScale_scale`).  Off the gate `ρ` may be `∞` and `τ = 0`;
  the identities still hold there (`toReal ∞ = 0`).
* **Positivity** (`spatialScale_pos`): the cell containing `x` has positive diameter.
* **Finiteness and Lipschitz continuity on the gate** (`spatialScale_lt_top`,
  `lipschitz_scaleReal`): the reach of a cell is `1`-Lipschitz in `x`; at `x = 0` the sublinear
  large-cell decay of a `similarityClosedGate` environment bounds every reach by
  `maxDiamHittingBall R₀`.
* **Regularity along paths** (`locallyBoundedBelow_flowTimeScale`, `rightUSC_flowTimeScale`): a
  càdlàg position path is bounded on compact time intervals (mathlib's
  `isBounded_image_of_isCadlag_of_isCompact`), and a positive continuous function has a positive
  minimum on a closed ball; right-continuity of `Z` and continuity of `ρ(e, ·)` give right
  (upper semi)continuity.  **No property of the path beyond being a point of the carrier is used**:
  the gate is `flowGate` (an environment-coordinate condition) and nothing else.
* Joint measurability (`measurable_flowTimeScale`): `ρ` is a countable supremum over code slots of
  jointly measurable reaches (`NonemptyCompacts.lipschitz_infDist`).

`localTimeScaleOn_flowTimeScale : LocalTimeScaleOn flowGate reRootFlow reScale flowTimeScale`.

## Why not the handoff's "area of the occupied cell" (argued, not formalized)

`outputs/flowspace-block-system-handoff.2026-09-18.md` §4.2 suggested `τ(ω, u) = |cell_{Y_u}|`
gated on "the label path takes finitely many active labels on bounded time intervals".  That gate
is not conull at the actual law in the manuscript's generality: the walk is **reflected off
infinity** (manuscript abstract, tex:66: bounded sets may contain infinitely many cells;
tex:1340: "the interpolation remains continuous through an accumulation of holding intervals"),
so the label path is at the cemetery `⊤` at the end-valued times and visits infinitely many
labels near them; there `|cell_{Y_u}| → 0` (the visited diameters tend to zero, tex:1340), and at
the cemetery itself `τ = 0`, violating `LocallyBoundedBelow`.  The gate would therefore demand
"no end-valued times", which fails with positive probability whenever cells accumulate — a
probable vacuity trap.  The spatial scale above is a *non-local* length (large cells at finite
distance count), so it stays bounded below along bounded position paths through accumulations.

## Results

* `gatedRootChainBlocks_flowTimeScale`: the gated block data on `flowGate` for
  `gridFlow`/`gridScaleFlow`, no hypotheses.
* `scaledRootChainSystemOn_flowTimeScale`: **the gated root-chain system on `markedFlowGate` from
  the unmarked transport alone**, for every s-finite law `Q` on `FlowSpace` whose environment
  coordinate lies a.s. in `similarityClosedGate` (the ONLY regularity requirement; no path
  regularity).  `_iff`: with these blocks the gated system is equivalent to the marked transport.
* `ae_mem_similarityClosedGate_map_rootMap`, `ae_mem_similarityClosedGate_of_ae_similar`: the
  gate requirement survives re-rooting (`rootMap c`) and any a.s. similarity of the environment,
  so it does not depend on the origin- vs cell-rooting decision.
* `scaledRootChainSystemOn_flowTimeScale_of_marginal`: the same when `Q.map Prod.fst ≪ ν` for an
  MTP+FE law `ν` (either rooting, provided its environment marginal is `≪ ν`).
* `scaledRootChainSystemOn_flowTimeScale_compProd`, `…_flowKernel`: at the origin-rooted annealed
  law `ν ⊗ₘ κ` of ANY Markov kernel, in particular `FlowCodingKernel.flowKernel`, the gate
  requirement is discharged (environment marginal `= ν`); only `transport` remains.

Nothing here proves the transport, `p:lem:timeMTP`, `p:lem:regeninvariant` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal

namespace ReflectedGMS.FlowSpaceTimeScale

open Code EnvironmentLaws HarmonicLawIngredients
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationFlowGrid ReflectedGMS.ActualMarkedBlockTransport
open ReflectedGMS.SimilarityClosedGate ReflectedGMS.SimilarityClosedGateFlow
open ReflectedGMS.FlowSpaceBlockSystem ReflectedGMS.FlowGateRootChainGate
open ReflectedGMS.ScaledRootChainGated ReflectedGMS.ScaledRootChain
open ReflectedGMS.ParabolicTransport ReflectedGMS.DyadicApproximation
open ReflectedGMS.RootedFiniteEnergyDensityMeasurable

/-! ## 1. The spatial scale of an environment -/

/-- **The reach of a compact cell from a point**: its diameter minus its distance from the point,
truncated at `0`. -/
noncomputable def cellReach (x : Plane) (K : CompactCell) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (K : Set Plane) - Metric.infDist x (K : Set Plane))

/-- **The spatial scale of an environment at a point**: the supremal reach of its cells. -/
noncomputable def spatialScale (e : Env) (x : Plane) : ℝ≥0∞ :=
  ⨆ v : Vertex e.val, cellReach x ((decode e).cell v)

theorem cellReach_transformCell (s : ℝ) (u : Plane) (hs : 0 < s) (x : Plane) (K : CompactCell) :
    cellReach (positiveSimilarity s u x) (transformCell s u hs K)
      = ENNReal.ofReal s * cellReach x K := by
  unfold cellReach
  rw [coe_transformCell, Spatial.diam_image_positiveSimilarity s u hs,
    Spatial.infDist_image_positiveSimilarity s u hs, ← mul_sub, ENNReal.ofReal_mul hs.le]

/-- **Similarity covariance of the spatial scale**, at every pair of similar environments. -/
theorem spatialScale_of_isSimilarity {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    (h : IsSimilarity s u hs e e') (x : Plane) :
    spatialScale e' (positiveSimilarity s u x) = ENNReal.ofReal s * spatialScale e x := by
  obtain ⟨σ, hcell, -⟩ := h
  have h1 : (⨆ v' : Vertex e'.val, cellReach (positiveSimilarity s u x) ((decode e').cell v'))
      = ⨆ v : Vertex e.val, cellReach (positiveSimilarity s u x) ((decode e').cell (σ v)) :=
    (σ.iSup_comp (g := fun v' : Vertex e'.val =>
      cellReach (positiveSimilarity s u x) ((decode e').cell v'))).symm
  show (⨆ v' : Vertex e'.val, cellReach (positiveSimilarity s u x) ((decode e').cell v'))
    = ENNReal.ofReal s * ⨆ v : Vertex e.val, cellReach x ((decode e).cell v)
  rw [h1, ENNReal.mul_iSup]
  refine iSup_congr fun v => ?_
  rw [hcell v, cellReach_transformCell]

theorem cellReach_le_add (x y : Plane) (K : CompactCell) :
    cellReach y K ≤ cellReach x K + ENNReal.ofReal (dist x y) := by
  unfold cellReach
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  have h : Metric.infDist x (K : Set Plane) ≤ Metric.infDist y (K : Set Plane) + dist x y :=
    Metric.infDist_le_infDist_add_dist
  linarith

/-- The spatial scale is `1`-Lipschitz in the extended sense. -/
theorem spatialScale_le_add (e : Env) (x y : Plane) :
    spatialScale e y ≤ spatialScale e x + ENNReal.ofReal (dist x y) := by
  refine iSup_le fun v => (cellReach_le_add x y _).trans ?_
  gcongr
  exact le_iSup (fun w : Vertex e.val => cellReach x ((decode e).cell w)) v

theorem diam_cell_pos (e : Env) (v : Vertex e.val) :
    0 < Metric.diam ((decode e).cell v : Set Plane) := by
  refine Metric.diam_pos ?_ ((decode e).cell v).isCompact.isBounded
  by_contra hnt
  have hsub : ((decode e).cell v : Set Plane).Subsingleton := Set.not_nontrivial_iff.1 hnt
  have hnull : volume ((decode e).cell v : Set Plane) = 0 := hsub.measure_zero volume
  exact ((decode_geometry e).2.1 v).ne_empty
    (MeasureTheory.Measure.interior_eq_empty_of_null hnull)

theorem spatialScale_zero_lt_top {e : Env} (he : e ∈ similarityClosedGate) :
    spatialScale e 0 < ∞ := by
  obtain ⟨⟨hfin, hsub⟩, -⟩ := he
  obtain ⟨R₀, hR₀, hR₀b⟩ := hsub 1 one_pos
  refine lt_of_le_of_lt ?_ (hfin R₀ hR₀.le)
  refine iSup_le fun v => ?_
  have hr0 : 0 ≤ Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) :=
    Metric.infDist_nonneg
  by_cases hrR : Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) ≤ R₀
  · have hv : Hits (decode e) (Metric.closedBall (0 : Plane) R₀) v :=
      (GoodEnvironmentSet.cell_inter_closedBall_nonempty_iff _ R₀).2 hrR
    calc cellReach 0 ((decode e).cell v)
        ≤ ENNReal.ofReal (Metric.diam ((decode e).cell v : Set Plane)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ Spatial.maxDiamHittingBall (decode e) R₀ :=
          le_iSup (fun w : {w : Vertex e.val //
              Hits (decode e) (Metric.closedBall (0 : Plane) R₀) w} =>
            ENNReal.ofReal (Metric.diam ((decode e).cell w.1 : Set Plane))) ⟨v, hv⟩
  · have hrR' : R₀ ≤ Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) :=
      (not_le.1 hrR).le
    have hv : Hits (decode e) (Metric.closedBall (0 : Plane)
        (Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane))) v :=
      (GoodEnvironmentSet.cell_inter_closedBall_nonempty_iff _ _).2 le_rfl
    have hd : ENNReal.ofReal (Metric.diam ((decode e).cell v : Set Plane))
        ≤ ENNReal.ofReal (1 * Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane)) :=
      (le_iSup (fun w : {w : Vertex e.val // Hits (decode e) (Metric.closedBall (0 : Plane)
          (Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane))) w} =>
        ENNReal.ofReal (Metric.diam ((decode e).cell w.1 : Set Plane))) ⟨v, hv⟩).trans
        (hR₀b _ hrR')
    rw [one_mul] at hd
    have hd' : Metric.diam ((decode e).cell v : Set Plane)
        ≤ Metric.infDist (0 : Plane) ((decode e).cell v : Set Plane) :=
      (ENNReal.ofReal_le_ofReal_iff hr0).1 hd
    have hz : cellReach 0 ((decode e).cell v) = 0 := by
      unfold cellReach
      exact ENNReal.ofReal_eq_zero.2 (by linarith)
    rw [hz]
    exact zero_le

/-- **The spatial scale is finite everywhere on the gate.** -/
theorem spatialScale_lt_top {e : Env} (he : e ∈ similarityClosedGate) (x : Plane) :
    spatialScale e x < ∞ :=
  (spatialScale_le_add e 0 x).trans_lt
    (ENNReal.add_lt_top.2 ⟨spatialScale_zero_lt_top he, ENNReal.ofReal_lt_top⟩)

theorem lipschitz_scaleReal {e : Env} (he : e ∈ similarityClosedGate) :
    LipschitzWith 1 fun x : Plane => (spatialScale e x).toReal := by
  refine LipschitzWith.of_le_add fun x y => ?_
  have h := spatialScale_le_add e y x
  have hy := spatialScale_lt_top he y
  calc (spatialScale e x).toReal
      ≤ (spatialScale e y + ENNReal.ofReal (dist y x)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hy, ENNReal.ofReal_lt_top⟩).ne h
    _ = (spatialScale e y).toReal + dist y x := by
        rw [ENNReal.toReal_add hy.ne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal dist_nonneg]
    _ = (spatialScale e y).toReal + dist x y := by rw [dist_comm]

/-! ### Joint measurability -/

theorem spatialScale_eq_iSup_slot (e : Env) (x : Plane) :
    spatialScale e x
      = ⨆ n : ℕ, if (e.val.1 n).isSome then cellReach x (slotCell e n) else 0 := by
  refine le_antisymm (iSup_le fun v => ?_) (iSup_le fun n => ?_)
  · refine le_iSup_of_le v.val ?_
    rw [if_pos v.property, slotCell_eq_cell]
  · by_cases h : (e.val.1 n).isSome
    · rw [if_pos h, slotCell_eq_cell e ⟨n, h⟩]
      exact le_iSup (fun w : Vertex e.val => cellReach x ((decode e).cell w)) ⟨n, h⟩
    · rw [if_neg h]
      exact zero_le

theorem measurable_infDist_joint :
    Measurable fun q : Plane × CompactCell => Metric.infDist q.1 (q.2 : Set Plane) :=
  (NonemptyCompacts.lipschitz_infDist (α := Plane)).continuous.measurable

/-- **The spatial scale is jointly measurable** in the environment and the point. -/
theorem measurable_spatialScale : Measurable fun p : Env × Plane => spatialScale p.1 p.2 := by
  have hEq : (fun p : Env × Plane => spatialScale p.1 p.2) = fun p : Env × Plane =>
      ⨆ n : ℕ, if (p.1.val.1 n).isSome then cellReach p.2 (slotCell p.1 n) else 0 :=
    funext fun p => spatialScale_eq_iSup_slot p.1 p.2
  rw [hEq]
  refine Measurable.iSup fun n => ?_
  have hK : Measurable fun p : Env × Plane => slotCell p.1 n :=
    (measurable_slotCell_env n).comp measurable_fst
  have hd : Measurable fun p : Env × Plane => Metric.diam (slotCell p.1 n : Set Plane) :=
    Spatial.measurable_cellDiam.comp hK
  have hic : Measurable ((fun q : Plane × CompactCell => Metric.infDist q.1 (q.2 : Set Plane))
      ∘ fun p : Env × Plane => (p.2, slotCell p.1 n)) :=
    measurable_infDist_joint.comp (measurable_snd.prodMk hK)
  have hi : Measurable fun p : Env × Plane => Metric.infDist p.2 (slotCell p.1 n : Set Plane) := by
    simpa only [Function.comp_def] using hic
  have hr : Measurable fun p : Env × Plane => cellReach p.2 (slotCell p.1 n) :=
    (hd.sub hi).ennreal_ofReal
  have hs : MeasurableSet {p : Env × Plane | (p.1.val.1 n).isSome = true} :=
    ((measurable_isSome_slot n).comp measurable_fst) (measurableSet_singleton true)
  exact Measurable.ite hs hr measurable_const

/-! ## 2. The time scale on the flow carrier -/

/-- **The local time scale** `τ(ω, u) = ρ(e, Z_u)²`: the squared spatial scale of the environment
at the walker's position. -/
noncomputable def flowTimeScale (ω : FlowSpace) (u : ℝ) : ℝ :=
  (spatialScale ω.1 (ω.2.2.toFun u)).toReal ^ 2

/-- **Flow covariance, at every point.** -/
theorem flowTimeScale_shift (r : ℝ) (ω : FlowSpace) (s : ℝ) :
    flowTimeScale (reRootFlow r ω) s = flowTimeScale ω (s + r) := by
  unfold flowTimeScale
  rw [reRootFlow_fst, reRootFlow_pos]
  have hpt : ω.2.2.toFun (s + r) - displacement ω r
      = positiveSimilarity 1 (displacement ω r) (ω.2.2.toFun (s + r)) := by
    rw [positiveSimilarity_apply, one_smul]
  rw [hpt, spatialScale_of_isSimilarity (isSimilarity_translateEnv (displacement ω r) ω.1),
    ENNReal.ofReal_one, one_mul]

/-- **Parabolic covariance, at every point.** -/
theorem flowTimeScale_scale (C : ℝ) (hC : 0 < C) (ω : FlowSpace) (s : ℝ) :
    flowTimeScale (reScale C ω) (C ^ 2 * s) = C ^ 2 * flowTimeScale ω s := by
  unfold flowTimeScale
  rw [reScale_fst hC, reScale_pos hC, inv_mul_cancel_left₀ (pow_ne_zero 2 hC.ne')]
  have hpt : C • ω.2.2.toFun s = positiveSimilarity C 0 (ω.2.2.toFun s) := by
    rw [positiveSimilarity_apply, sub_zero]
  rw [hpt, spatialScale_of_isSimilarity (isSimilarity_similarityTargetEnv C 0 hC ω.1),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
  ring

theorem measurable_flowTimeScale :
    Measurable fun q : FlowSpace × ℝ => flowTimeScale q.1 q.2 := by
  have hP : Measurable fun q : FlowSpace × ℝ => q.1.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hZ : Measurable fun q : FlowSpace × ℝ => q.1.2.2.toFun q.2 :=
    CadlagPath.measurable_eval_uncurry.comp (hP.prodMk measurable_snd)
  have he : Measurable fun q : FlowSpace × ℝ => q.1.1 := measurable_fst.comp measurable_fst
  have hsc : Measurable ((fun p : Env × Plane => spatialScale p.1 p.2)
      ∘ fun q : FlowSpace × ℝ => (q.1.1, q.1.2.2.toFun q.2)) :=
    measurable_spatialScale.comp (he.prodMk hZ)
  have hs : Measurable fun q : FlowSpace × ℝ => spatialScale q.1.1 (q.1.2.2.toFun q.2) := by
    simpa only [Function.comp_def] using hsc
  exact hs.ennreal_toReal.pow_const 2

/-- **Right upper semicontinuity of the local time scale on the gate.** -/
theorem rightUSC_flowTimeScale {ω : FlowSpace} (hω : ω ∈ flowGate) :
    RightUpperSemicontinuous (flowTimeScale ω) := by
  intro s ε hε
  have he : ω.1 ∈ similarityClosedGate := hω
  have h1 : Continuous fun x : Plane => (spatialScale ω.1 x).toReal ^ 2 :=
    (lipschitz_scaleReal he).continuous.pow 2
  have hc : ContinuousWithinAt ((fun x : Plane => (spatialScale ω.1 x).toReal ^ 2) ∘ ω.2.2.toFun)
      (Set.Ici s) s :=
    h1.continuousAt.comp_continuousWithinAt (ω.2.2.continuousWithinAt_Ici s)
  have hcont : ContinuousWithinAt (flowTimeScale ω) (Set.Ici s) s := hc
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hcont ε hε
  refine ⟨δ, hδ, fun u hsu hus => ?_⟩
  have hd : dist u s < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  have h2 := hball (show u ∈ Set.Ici s from le_of_lt hsu) hd
  rw [Real.dist_eq] at h2
  linarith [le_abs_self (flowTimeScale ω u - flowTimeScale ω s)]

/-! ## 3. The gated block data and the gated root-chain system -/
/-! ### The gate requirement is insensitive to the rooting

The one law-level requirement `∀ᵐ ω ∂Q, ω.1 ∈ similarityClosedGate` survives any re-rooting of the
law: the rooting map `rootMap c` (`TwoSidedRegenerationFlow`, the frame change to a reference point
`c e`) preserves the gate exactly, and so does replacing the environment by any similar one. -/

/-- **Re-rooting a gate-conull law keeps it gate-conull**, for every measurable reference point. -/
theorem ae_mem_similarityClosedGate_map_rootMap {Q : Measure FlowSpace}
    (hQ : ∀ᵐ ω ∂Q, ω.1 ∈ similarityClosedGate) {c : Env → Plane} (hc : Measurable c) :
    ∀ᵐ ω ∂(Q.map (rootMap c)), ω.1 ∈ similarityClosedGate := by
  have h : ∀ᵐ ω ∂(Q.map (rootMap c)), ω ∈ flowGate := by
    refine (ae_map_iff (p := fun ω : FlowSpace => ω ∈ flowGate)
      (measurable_rootMap hc).aemeasurable measurableSet_flowGate).2 ?_
    filter_upwards [hQ] with ω hω
    exact (rootMap_mem_flowGate_iff c ω).2 hω
  exact h

end ReflectedGMS.FlowSpaceTimeScale
