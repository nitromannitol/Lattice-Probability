/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CellRootedRegenerativeInvariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CellRootedEncodingRepair
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerativeInvarianceReduction
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleHoldingIndependence
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CycleDecompositionRegeneration
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CompleteCycleReversalProof
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGate
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGateFlow
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
**⚠ VACUOUS/SUPERSEDED (2026-09-18):** the gated (F2′) route of this module,
`FrameSimilarityTransferOn similarityClosedGate κF` at the origin-rooted `κF`, is FALSE (trap #8,
argued, `outputs/final-route-review.2026-09-18.md` §2): a gate environment whose origin lies on the
boundary mask with label `0` inactive has the cemetery fibre
(`FlowCodingKernel.flowFibre_of_not_live`), so the instances of `regenerativeInvariance_cellRooted`
at `κF` and that gate are vacuous; `hregen` itself is true.  Superseded by the
all-starts route `Temporal/CellRootedRegenAllStarts*`
(`CellRootedRegenAllStartsWeld.hregen_validLaw_interior_of_ratShiftBridge`), which still reuses
`const_eq_of_shiftInvariantMixture` and `RatShiftBridge` from this file.  Also stale below: the
positivity input IS proved (`AreaWalkFixedTimePositivityWeld.areaWalkFixedTimePositivity_of_admissible`).

# `hregen` at the cell-rooted law (rooting-decision packet P3)

Repair R2 (light form, `outputs/rooting-decision-handoff.2026-09-18.md`) states `hregen` at the
cell-rooted law `Q := (ν ⊗ₘ κ).map cellRoot`.  This module proves

  `RegenerativeInvariance ((ν ⊗ₘ κ).map cellRoot) reRootFlow reScale Prod.fst`

from two fixed-environment inputs about `κ` that quantify ONLY over `reFrame`-invariant test
functionals (`CellRootedTest`):

* **(F1′)** `FrameFiberwiseConstant ν κ` — for `ν`-a.e. environment, a test functional is
  `κ e`-a.s. constant.  Implied by the brief's `FiberwiseConstant ν κ plainShift reScale`.
* **(F2′)** `FrameSimilarityTransferOn G κ` — the a.s. value is the same at similar environments,
  for `e` in a measurable, conull, similarity-closed gate `G`.

The pull-back principle: `B ↦ B ∘ cellRoot` maps `reRootFlow`/`reScale`-invariant functionals on
the cell-rooted side to `plainShift`/`reScale`/`reFrame`-invariant ones (`cellRoot_reFrame`), the
environment function is the manuscript's `(G ∩ constantSet).indicator condMean`, and
`b (cellRoot ω).1 = b ω.1` because `(cellRoot ω).1` is a translate of `ω.1`.

## Why (F2′) is GATED

Off the kernel's gate the fibre of `κF = flowKernel …` is the cemetery point mass
`δ cemFlow`, and a test functional may read the (constant) cemetery position relative to the
cells of `e` (e.g. "the constant position lies in the left half of its cell", which is
`plainShift`-, `reScale`- and `reFrame`-invariant).  By `reFrame` invariance
`B (translateEnv u e, cemFlow) = B (e, cemetery label path, constant position u)`, so the brief's
ungated transfer (ii) would force such a functional to be independent of `u` at every environment
off the gate — false as soon as the gate misses one environment (argued, not formalized).  The
gated form is strictly weaker and is all the reduction uses; `regenerativeInvariance_cellRooted_ungated`
records the brief's literal shape as the `G = univ` instance.

## The two halves of (F2′)

* `frameSimilarityTransferOn_of_halves`: (F2′) ⇐ dilation half ∧ translation half
  (`IsSimilarity s u` = dilation by `s` about `0`, then translation by `s • u`).
* **Dilation half** ⇐ `KernelDilationCovariantOn G κ` — the law-level identity
  `(κ e).map (scaleCoding C e) = κ (similarityTargetEnv C 0 hC e)`
  (`dilationTransferOn_of_kernelDilationCovariant`).
* **Translation half** = the manuscript's start-cell independence (tex:1503-1506):
  `const_eq_of_shiftInvariantMixture` proves the manuscript argument abstractly (the σ-finite
  area mixture is shift invariant, so `{X_0 = u, B ≠ b(u)}` is null, so is its shift, hence
  `b(v) = b(u)` on `{X_q = u}`), and `translationTransferOn_of_startIndependence` reduces the
  translation half to a family of start-at-vertex laws `P e n` with: frame identification
  (`hframe`, `hcover`), start (`hstart`), rational-shift invariance of the area mixture
  (`hshift`), pointwise (F1) on the gate, and **positivity** (`hpos`).  No producer of the
  positivity input exists in the tree (see `AreaWalkFixedTimePositivity`, the precise raw form).

## (F1) at the bridge kernel

`fiberwiseConstant_flowKernel_of_ratShiftBridge`: (F1) at `κF` from the PROVED cycle ergodicity
of the actual regeneration kernel at every environment
(`CycleHolding.cycleErgodic_rootedRegKernel`), transported along
`FlowCodingKernel.map_ratRead_flowKernel_eq_rootedRegKernel`, given the carrier bridge
`RatShiftBridge` — the a.e. form of "`ratRead ∘ plainShift τ = rho ∘ ratRead`": along the cycle
orbit, the rational code of `rho^[n+1] w` is the rational reading of a real time shift of a
configuration whose rational reading is the code of `rho^[n] w`.  The rational reading does NOT
commute with irrational shifts pointwise, which is why this is an a.e. statement (no jump of the
path at `q + T_n`, `q ∈ ℚ`) and stays a named input here (the pointwise form `RatShiftBridgeOn` is PROVED:
`RatShiftBridgeProof.ratShiftBridgeOn_interiorField`).

Nothing here constructs the start laws, the covariant representative, the carrier bridge, the
positivity producer, `hsys`, or either main theorem.
-/

-- Merged from `ReflectedGMS/Temporal/CycleHoldingFacts.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_CycleHoldingFacts

/-!
# `hcyc` discharged at the actual regeneration kernel

`CycleDecompositionWeld.hcyc_rootedRegKernel_of_holdings'` reduced cycle ergodicity of the actual
kernel `rootedRegKernel … (measurable_slotTransition …)` to two facts about the first-cycle law
`ν = firstCycleLaw G hwalk (rootLabel e) e` on the live set:

* (R4) `HoldExcIndep ν` — `CycleHoldingIndependence.holdExcIndep_firstCycleLaw`, PROVED;
* (R5) `StraddleAbsCont ν` — `CycleHoldingStraddle.straddleAbsCont_firstCycleLaw`, PROVED.

Both hold at EVERY live environment of EVERY admissible gate, so:

* **`cycleErgodic_rootedRegKernel`**: `CycleErgodic (rootedRegKernel G hG hwalk
  (measurable_slotTransition G hG hwalk) e) rho` at every `e` (off the live set the fibre is the
  cemetery point mass), for every measurable admissible gate `G` — no named input;
* `hcyc_rootedRegKernel_actual`: the a.e. form consumed by the regeneration lane, for every
  environment law;
* **`hcyc_similarityClosedGate`**: at the law-independent similarity-closed gate, from MTP + (FE):
  the gate is conull and `hcyc` holds;
* `fiberwiseConstant_rootedRegKernel_of_hroot`: (F1) of the regeneration lane at the actual kernel
  from the flow owner's `hroot` ALONE (clauses (b), (c) and `hmeas` are all discharged).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleHolding

open Code EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw
open ReflectedGMS.RegenerativeInvarianceFiberwise
open ReflectedGMS.CycleDecomposition
open ReflectedGMS.HarmonicLawIngredients ReflectedGMS.RegenerativeInvarianceReduction

/-- **Cycle ergodicity of the actual regeneration kernel at every environment**, for every
measurable admissible gate. -/
theorem cycleErgodic_rootedRegKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (e : Env) :
    CycleErgodic (rootedRegKernel G hG hwalk
      (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e) rho := by
  by_cases hlive : e ∈ G ∧ (e.val.1 (rootLabel e)).isSome
  · exact cycleErgodic_of_reversal_and_decomposition
      (CycleReversalProof.completeCycleReversal_firstCycleLaw G hwalk (rootLabel e) e)
      (rootedCycleDecomposition_rootedRegKernel_of G hG hwalk hlive.1 hlive.2
        (holdExcIndep_firstCycleLaw G hwalk hlive.1 hlive.2)
        (straddleAbsCont_firstCycleLaw G hwalk hlive.1 hlive.2))
  · rw [rootedRegKernel_of_not_live G hG hwalk _ hlive]
    exact cycleErgodic_dirac _

end ReflectedGMS.CycleHolding

end Merged_CycleHoldingFacts

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CellRootedRegenerativeInvariance

open Code EnvironmentLaws EnvironmentFields
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CellRootedEncodingRepair ReflectedGMS.FlowCodingKernel
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.RegenerativeInvarianceReduction
open ReflectedGMS.RegenerativeInvarianceFiberwise ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.HarmonicLawIngredients ReflectedWalk

/-! ### 1. Frame invariance of the cell-rooted encoding; the test class -/

/-- **The cell-rooted encoding forgets the frame.** -/
theorem cellRoot_reFrame (u : Plane) (ω : FlowSpace) : cellRoot (reFrame u ω) = cellRoot ω := by
  rw [cellRoot_eq_reFrame (reFrame u ω), cellRoot_eq_reFrame ω, reFrame_reFrame]
  congr 1
  show u + (ω.2.2.toFun 0 - u) = ω.2.2.toFun 0
  abel

/-- The environment of the cell-rooted encoding is a translate of the environment. -/
theorem cellRoot_fst (ω : FlowSpace) : (cellRoot ω).1 = translateEnv (ω.2.2.toFun 0) ω.1 := by
  rw [cellRoot_eq_reFrame]
  rfl

/-- **The test class of the cell-rooted repair**: bounded measurable functionals invariant under
the plain time shift, the parabolic scaling and every frame change. -/
structure CellRootedTest (B : FlowSpace → ℝ) : Prop where
  measurable : Measurable B
  bound : ∀ ω : FlowSpace, |B ω| ≤ 1
  shift : ∀ (t : ℝ) (ω : FlowSpace), B (plainShift t ω) = B ω
  scale : ∀ C : ℝ, 0 < C → ∀ ω : FlowSpace, B (reScale C ω) = B ω
  frame : ∀ (u : Plane) (ω : FlowSpace), B (reFrame u ω) = B ω

/-- **Pull-back**: a bounded measurable `reRootFlow`/`reScale`-invariant functional composed with
the cell-rooted encoding is a test functional. -/
theorem cellRootedTest_comp_cellRoot {B : FlowSpace → ℝ} (hB : Measurable B)
    (hb : ∀ ω, |B ω| ≤ 1) (hθ : ∀ (t : ℝ) (ω : FlowSpace), B (reRootFlow t ω) = B ω)
    (hS : ∀ C : ℝ, 0 < C → ∀ ω : FlowSpace, B (reScale C ω) = B ω) :
    CellRootedTest fun ω => B (cellRoot ω) where
  measurable := hB.comp measurable_cellRoot
  bound := fun ω => hb _
  shift := fun t ω => by
    show B (cellRoot (plainShift t ω)) = B (cellRoot ω)
    rw [← reRootFlow_cellRoot]
    exact hθ t _
  scale := fun C hC ω => by
    show B (cellRoot (reScale C ω)) = B (cellRoot ω)
    rw [← reScale_cellRoot hC]
    exact hS C hC _
  frame := fun u ω => by
    show B (cellRoot (reFrame u ω)) = B (cellRoot ω)
    rw [cellRoot_reFrame]

/-! ### 2. The two restricted inputs -/

/-- A set of environments closed under every physical similarity, in both directions. -/
def SimilarityClosed (G : Set Env) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env), IsSimilarity s u hs e e' → (e ∈ G ↔ e' ∈ G)

theorem similarityClosed_similarityClosedGate :
    SimilarityClosed SimilarityClosedGate.similarityClosedGate :=
  fun _ _ _ _ _ h => SimilarityClosedGate.mem_similarityClosedGate_iff_of_isSimilarity h

/-! ### 3. The reduction at the cell-rooted law -/

/-! ### 4. (F2′) from a dilation half and a translation half -/

/-! ### 5. The dilation half from law-level dilation covariance -/

/-! ### 6. The translation half: start-cell independence (tex:1503-1506) -/

/-- **The manuscript's `v`-independence argument, abstractly.**  Let `𝕢 = Σ_i a_i P_i` be
invariant under `θ`, let `P_i` start at `code i`, let `f` be `θ`-invariant with `P_i`-a.s. value
`c i`.  If `a_v ≠ 0` and `P_v (lab ∘ θ = code u) ≠ 0` then `c v = c u`: the event
`{lab = code u, f ≠ c u}` is `𝕢`-null, hence so is its `θ`-preimage, and on
`{lab ∘ θ = code u}` the functional equals both constants. -/
theorem const_eq_of_shiftInvariantMixture {X ι β : Type*} [MeasurableSpace X]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (P : ι → Measure X) (a : ι → ℝ≥0∞) {θ : X → X}
    (hθ : MeasurePreserving θ (Measure.sum fun i => a i • P i) (Measure.sum fun i => a i • P i))
    {lab : X → β} (hlab : Measurable lab) {code : ι → β} (hcode : Function.Injective code)
    (hstart : ∀ i, ∀ᵐ x ∂P i, lab x = code i)
    {f : X → ℝ} (hf : Measurable f) (hfθ : ∀ x, f (θ x) = f x)
    {c : ι → ℝ} (hc : ∀ i, ∀ᵐ x ∂P i, f x = c i)
    {u v : ι} (ha : a v ≠ 0) (hpos : P v {x | lab (θ x) = code u} ≠ 0) : c v = c u := by
  set E : Set X := {x | lab x = code u ∧ f x ≠ c u} with hEdef
  have hEm : MeasurableSet E :=
    (hlab (measurableSet_singleton (code u))).inter (measurableSet_eq_fun hf measurable_const).compl
  have hPE : ∀ i, P i E = 0 := by
    intro i
    by_cases hi : i = u
    · subst hi
      exact measure_mono_null (fun x hx => hx.2) (ae_iff.1 (hc i))
    · refine measure_mono_null (fun x hx => ?_) (ae_iff.1 (hstart i))
      show ¬ (lab x = code i)
      rw [hx.1]
      exact fun h => hi (hcode h).symm
  have hQE : (Measure.sum fun i => a i • P i) E = 0 := by
    rw [Measure.sum_apply _ hEm]
    exact ENNReal.tsum_eq_zero.2 fun i => by rw [Measure.smul_apply, hPE i, smul_zero]
  have hQE' : (Measure.sum fun i => a i • P i) (θ ⁻¹' E) = 0 := by
    rw [hθ.measure_preimage hEm.nullMeasurableSet, hQE]
  have hPv : P v (θ ⁻¹' E) = 0 := by
    have hle : a v • P v ≤ Measure.sum fun i => a i • P i := Measure.le_sum (fun i => a i • P i) v
    have h0 : (a v • P v) (θ ⁻¹' E) = 0 :=
      le_antisymm ((Measure.le_iff'.1 hle _).trans hQE'.le) zero_le
    rw [Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left ha
  by_contra hne
  apply hpos
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hPv (ae_iff.1 (hc v)))
  by_cases hfx : f x = c u
  · right
    show ¬ (f x = c v)
    rw [hfx]
    exact fun h => hne h.symm
  · left
    refine ⟨hx, ?_⟩
    show f (θ x) ≠ c u
    rw [hfθ]
    exact hfx

/-- The plain time shift on the coding: `plainShift t (e, x) = (e, flowShift t x)`. -/
def flowShift (t : ℝ) (x : FlowCoding) : FlowCoding :=
  (CadlagPath.timeShift t x.1, CadlagPath.timeShift t x.2)

/-- **The open probability input, raw form**: fixed-time positivity of the area walk — from
every vertex, every vertex is occupied at every positive time with positive probability.  True
on connected graphs with positive rates (manuscript tex:1504-1505); no producer in the tree
(the nearest ingredients are the first-step law `ExponentialFirstStep`, the embedded-chain
cylinder formula `ReflectedWalk.Theorem16.measure_pairCylEvent`, and detailed balance).
Not asserted anywhere. -/
def AreaWalkFixedTimePositivity (G : Set Env) : Prop :=
  ∀ e ∈ G, ∀ (v u : Vertex e.val) (t : ℝ≥0), 0 < t →
    (areaFamily e).P v {ω | (areaFamily e).X t ω = some u} ≠ 0

/-! ### 7. (F1) at the bridge kernel from cycle ergodicity and the rational shift bridge -/

/-- **The rational-time shift bridge** (the a.e. form of `ratRead ∘ plainShift τ = rho ∘ ratRead`):
along the cycle orbit of `μ`-a.e. regular two-sided path, the rational code of the next
re-rooting is the rational reading of a real time shift of a configuration whose rational
reading is the current code.  Satisfiability (argued): take the càdlàg completion of `rho^[n] w`
and the first return time; it holds whenever no jump of the path falls on `q + T_k` for rational
`q`, which is a.s. by the strong Markov property at the return times and continuity of the
holding laws. -/
def RatShiftBridge (R : TwoSidedReg → RatCode) (μ : Measure TwoSidedReg) : Prop :=
  ∀ᵐ w ∂μ, ∀ n : ℕ, ∃ (x : FlowCoding) (t : ℝ),
    ratRead x = R (rho^[n] w) ∧ ratRead (flowShift t x) = R (rho^[n + 1] w)

/-- **Fixed-environment ergodicity on the flow carrier from cycle ergodicity on the regular
carrier.**  A bounded measurable shift-invariant functional of the configuration factors through
the rational reading; its pull-back to the regular carrier is `rho`-invariant along a.e. orbit
(bridge), is replaced by an everywhere-invariant `limsup` version, and cycle ergodicity makes it
constant. -/
theorem ae_const_of_cycleErgodic_of_bridge {μ : Measure TwoSidedReg} (hcyc : CycleErgodic μ rho)
    {κe : Measure FlowCoding} {R : TwoSidedReg → RatCode} (hR : Measurable R)
    (hlaw : κe.map ratRead = μ.map R) (hbr : RatShiftBridge R μ)
    {f : FlowCoding → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hfθ : ∀ (t : ℝ) (x : FlowCoding), f (flowShift t x) = f x) :
    ∃ c : ℝ, ∀ᵐ x ∂κe, f x = c := by
  have hfs : StronglyMeasurable[MeasurableSpace.comap ratRead inferInstance] f :=
    hf.stronglyMeasurable.mono measurableSpace_flowCoding_eq.le
  obtain ⟨g, hg, hfg⟩ := hfs.exists_eq_measurable_comp
  have hgf : ∀ x, g (ratRead x) = f x := fun x => (congrFun hfg x).symm
  let clamp : ℝ → ℝ := fun r => max (-1) (min 1 r)
  have hclamp_m : Measurable clamp := measurable_const.max (measurable_const.min measurable_id)
  have hclamp_id : ∀ r : ℝ, |r| ≤ 1 → clamp r = r := by
    intro r hr
    have h := abs_le.1 hr
    show max (-1) (min 1 r) = r
    rw [min_eq_right h.2, max_eq_right h.1]
  have hclamp_b : ∀ r : ℝ, |clamp r| ≤ 1 := fun r =>
    abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  let h : TwoSidedReg → ℝ := fun w => clamp (g (R w))
  have hm : Measurable h := hclamp_m.comp (hg.measurable.comp hR)
  have hstep : ∀ᵐ w ∂μ, ∀ n : ℕ, h (rho^[n] w) = h w := by
    filter_upwards [hbr] with w hw
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨x, t, hx0, hx1⟩ := hw n
      rw [← ih]
      show clamp (g (R (rho^[n + 1] w))) = clamp (g (R (rho^[n] w)))
      rw [← hx0, ← hx1, hgf, hgf, hfθ]
  let H : TwoSidedReg → ℝ := fun w => clamp (limsup (fun i : ℕ => h (rho^[i] w)) atTop)
  have hHm : Measurable H :=
    hclamp_m.comp (Measurable.limsup fun i => hm.comp (measurable_rho.iterate i))
  have hHinv : ∀ w, H (rho w) = H w := by
    intro w
    show clamp (limsup (fun i : ℕ => h (rho^[i] (rho w))) atTop) =
      clamp (limsup (fun i : ℕ => h (rho^[i] w)) atTop)
    congr 1
    have hseq : (fun i : ℕ => h (rho^[i] (rho w))) = fun i : ℕ => h (rho^[i + 1] w) := rfl
    rw [hseq, Filter.limsup_nat_add (fun i : ℕ => h (rho^[i] w)) 1]
  obtain ⟨c, hc⟩ := hcyc H hHm (fun w => hclamp_b _) hHinv
  have hhc : ∀ᵐ w ∂μ, h w = c := by
    filter_upwards [hc, hstep] with w hw hs
    have hseq : (fun i : ℕ => h (rho^[i] w)) = fun _ : ℕ => h w := funext hs
    have hHw : H w = h w := by
      show clamp (limsup (fun i : ℕ => h (rho^[i] w)) atTop) = h w
      rw [hseq, limsup_const]
      exact hclamp_id _ (hclamp_b _)
    rw [← hHw]
    exact hw
  have hmeas : MeasurableSet {y : RatCode | clamp (g y) = c} :=
    measurableSet_eq_fun (hclamp_m.comp hg.measurable) measurable_const
  have hR' : ∀ᵐ y ∂μ.map R, clamp (g y) = c :=
    (ae_map_iff hR.aemeasurable hmeas).2 hhc
  rw [← hlaw, ae_map_iff measurable_ratRead.aemeasurable hmeas] at hR'
  refine ⟨c, ?_⟩
  filter_upwards [hR'] with x hx
  rw [hgf, hclamp_id _ (hfb x)] at hx
  exact hx

/-- **(F1) at the bridge kernel, pointwise**, at every environment where the carrier bridge holds
(cycle ergodicity of the actual kernel is PROVED at every environment). -/
theorem ae_const_flowKernel_of_ratShiftBridge (z : CellField) (G : Set Env)
    (hG : MeasurableSet G) (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hext : ExtensionGate z G) (e : Env)
    (hbr : RatShiftBridge (fun w => ratCode z (e, w.val))
      (rootedRegKernel G hG hwalk
        (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e))
    {B : FlowSpace → ℝ} (hB : Measurable B) (hb : ∀ p, |B p| ≤ 1)
    (hθ : ∀ (t : ℝ) (p : FlowSpace), B (plainShift t p) = B p) :
    ∃ c : ℝ, ∀ᵐ x ∂flowKernel z G hG hwalk hext e, B (e, x) = c :=
  ae_const_of_cycleErgodic_of_bridge (CycleHolding.cycleErgodic_rootedRegKernel G hG hwalk e)
    ((measurable_ratCode z).comp (measurable_const.prodMk measurable_subtype_coe))
    (map_ratRead_flowKernel_eq_rootedRegKernel z G hG hwalk hext e) hbr
    (hB.comp measurable_prodMk_left) (fun _ => hb _) (fun t x => hθ t (e, x))

/-! ### 8. Assembled: `hregen` at the cell-rooted law from the carrier bridge and (F2′) -/

end ReflectedGMS.CellRootedRegenerativeInvariance
