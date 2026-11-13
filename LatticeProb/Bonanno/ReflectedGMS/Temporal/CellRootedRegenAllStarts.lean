/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CellRootedRegenAllStarts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ReflectedWalkFixedTimePositivity
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedRegenerativeInvariance
import LatticeProb.Bonanno.ReflectedGMS.Temporal.SimilarityClosedGate
import LatticeProb.Bonanno.ReflectedGMS.Process.ExtensionGateAllStarts
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedTimeMTP
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationLabelExhaustion

/-!
# `hregen` at the cell-rooted law through the ALL-STARTS laws (manuscript tex:1494-1511)

Repair of trap #8 (`outputs/final-route-review.2026-09-18.md` §2).  The previous reduction
(`CellRootedRegenerativeInvariance.regenerativeInvariance_cellRooted`) built the invariant
environment set from the ORIGIN-rooted kernel `κF` and needed the gated transfer (F2′)
`FrameSimilarityTransferOn similarityClosedGate κF`, which is FALSE: a gate environment whose origin
lies on the boundary mask with label `0` inactive has the cemetery fibre (`flowFibre_of_not_live`).

Here the invariant set is the manuscript's (tex:1511): *the set of environments for which the
conditional law of `B` is a point mass for EVERY vertex and all these point masses agree* —
tested by zero conditional deviation and equality of conditional means over the countable label
coding — read through an all-starts family `K n` (`ℙ_H^{H_n}`, the flow carrier law of the
two-sided walk from cell `n`; `FlowSlotKernel.flowSlotKernel` in the tree):

* `allStartsSet K G B := G ∩ ⋂ n, ({n inactive} ∪ {condDev (K n) B = 0 ∧ condMean (K n) B =
  baseMean})`, `allStartsValue := allStartsSet.indicator baseMean` (`baseMean` = conditional mean
  at the least active label).  Measurable (`measurableSet_allStartsSet`), characterized by
  `mem_allStartsSet_iff`.
* **Exact similarity invariance** (`similarityInvariantFun_allStartsValue`) from EXACT similarity
  covariance of the family at active slots of gate environments (`SlotSimilarityCovariantOn`, the
  flow-level `law_φ`, shape of `CellRootedTimeMTP.cellRootedPlainTransport_of_startKernels`'s
  `hcov`).  Only ACTIVE slots are ever evaluated, so no cemetery fibre enters.
* **The assembly** (`regenerativeInvariance_cellRooted_of_allStarts`): `B = b ∘ fst` a.s. at
  `Q = (ν ⊗ₘ κ).map cellRoot` from a.e. liveness + root identification `κ e = K (rootLabel e) e`
  and a.e. all-starts constancy.  No origin-dependent exceptional set enters the definition of `b`.
* **Start-cell independence** (tex:1511, `allStartsConst_of_startIndependence`): per-start
  constants agree, by `CellRootedRegenerativeInvariance.const_eq_of_shiftInvariantMixture` with the
  area mixture `startMixture K e` shift invariant at time `1` and fixed-time positivity PROVED
  (`AreaWalkFixedTimePositivityWeld.areaWalkFixedTimePositivity_of_admissible`).
* **(F1) at every start from (F1) at the root** (`allStartsF1_of_root`): the law from cell `n` of
  `e` is the frame-back of the ROOT law of the translate `translateEnv (z e n) e`, whose origin is
  the interior, off-mask point `z e n` (`InteriorOffMask`), hence LIVE; (F1) at a live root is
  cycle ergodicity (PROVED, `CycleHolding.cycleErgodic_rootedRegKernel`) plus the rational-shift
  bridge (`rootF1_of_ratShiftBridgeOn`).
* **Fibre-shape facts** (`SlotFibreShape`, definitional for `flowSlotKernel`, `slotFibre_of_live`):
  root identification, start at the slot, and the one-time marginal comparison with the raw area
  law, from the all-starts extension (`ExtensionGateAllStarts.ExtensionAllStarts`, PROVED on the
  similarity-closed gate).

## Final theorems
* `regenerativeInvariance_cellRooted_allStarts` — any measurable, similarity-closed, conull,
  admissible gate `G`, any interior representative `z`, any all-starts family `K` with the fibre
  shape and the exact covariance on `G`;
* `regenerativeInvariance_validLaw_interior_allStarts` — the frontier binder `hregen` of
  `CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier` at the interior
  representative, exact shape.

Remaining named inputs (all stated here, none asserted): `hfib` + `hcov` (the all-starts kernel and
its exact covariance: `FlowSlotKernel`, P2b/A1), `hshift` (A2: two-sided real-time shift invariance
of `Σ_v a_v κ_v(e)`, the same binder as P2b's `cellRootedPlainTransport_of_startKernels`), `hbr`
(B1: `RatShiftBridge` POINTWISE at every live gate environment).
-/

-- Merged from `ReflectedGMS/Temporal/AreaWalkFixedTimePositivityWeld.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_AreaWalkFixedTimePositivityWeld

/-! # `AreaWalkFixedTimePositivity` is PROVED on every admissible gate

`CellRootedRegenerativeInvariance.AreaWalkFixedTimePositivity G` (the raw positivity input of
the translation half of (F2′), manuscript tex:1504-1505) holds for every set `G` of admissible
environments: at an admissible environment the area-clock family is a reflected walk
(`TwoSidedRegenerationCoding.isReflectedWalk_areaFamily`) with positive rates
(`EnvironmentWalkDataProducer.areaRate_pos`) on a connected cell graph (`decode_connected`), so
`ReflectedWalkFixedTimePositivity.transition_ne_zero` applies.

* `areaWalkFixedTimePositivity_of_admissible` — any gate whose members are admissible;
* `areaWalkFixedTimePositivity_similarityClosedGate` — the weld at `similarityClosedGate`;
* `hpos_of_oneTimeMarginal` — the flow-carrier form `hpos` of
  `translationTransferOn_of_startIndependence`, from a one-time-marginal comparison of the
  carrier family `P e n` with the raw area law (at positive rational times);
* `translationTransferOn_of_startIndependence_of_marginal` — the consumer with `hpos` replaced
  by that comparison.

The carrier family `P e n` itself (start-at-vertex laws on the flow carrier) and its
identification with the raw laws are NOT constructed in the tree; the comparison `hmarg` is
the one-time shadow of that identification and is a hypothesis here.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace ReflectedGMS.AreaWalkFixedTimePositivityWeld

open ProbabilityTheory
open Code EnvironmentLaws EnvironmentFields
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.ActualMarkedBlockTransport ReflectedGMS.MarkedSimilarityActionLaws
open ReflectedGMS.CellRootedEncodingRepair ReflectedGMS.FlowCodingKernel
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.HarmonicLawIngredients ReflectedGMS.CellRootedRegenerativeInvariance

/-- **Fixed-time positivity of the area walk on every admissible gate.** -/
theorem areaWalkFixedTimePositivity_of_admissible {G : Set Env}
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) : AreaWalkFixedTimePositivity G := by
  intro e he v u t ht
  have := nontrivial_vertex e
  exact ReflectedWalkFixedTimePositivity.transition_ne_zero
    (isReflectedWalk_areaFamily e (hwalk e he)) (areaRate_pos e) (decode_connected e) v u ht

end ReflectedGMS.AreaWalkFixedTimePositivityWeld

end Merged_AreaWalkFixedTimePositivityWeld

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CellRootedRegenAllStarts

open Code EnvironmentLaws EnvironmentFields RootDensities
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.ActualMarkedBlockTransport
open ReflectedGMS.CellRootedEncodingRepair ReflectedGMS.FlowCodingKernel
open ReflectedGMS.GridAveragedConstantReduction ReflectedGMS.RegenerativeInvarianceReduction
open ReflectedGMS.RegenerativeInvarianceFiberwise ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.HarmonicLawIngredients ReflectedWalk
open ReflectedGMS.CellRootedRegenerativeInvariance

/-! ### 1. The invariant set of tex:1511 through the all-starts laws -/

/-- **All-starts constancy with a common constant**: from every active vertex, the functional is
almost surely the constant `c`. -/
def AllStartsConst (K : ℕ → Kernel Env FlowCoding) (B : FlowSpace → ℝ) (e : Env) (c : ℝ) :
    Prop :=
  ∀ n : ℕ, (e.val.1 n).isSome → ∀ᵐ x ∂K n e, B (e, x) = c

/-- The conditional mean from the least active label (the "common mean" of tex:1511). -/
noncomputable def baseMean (K : ℕ → Kernel Env FlowCoding) (B : FlowSpace → ℝ) (e : Env) : ℝ :=
  condMean (K (RegenerationLabelExhaustion.baseLabel e)) B e

/-- **The invariant set of tex:1511**: gate environments at which, for EVERY active label, the
conditional deviation vanishes and the conditional mean is the common (base) mean. -/
def allStartsSet (K : ℕ → Kernel Env FlowCoding) (G : Set Env) (B : FlowSpace → ℝ) : Set Env :=
  G ∩ ⋂ n : ℕ, ({e : Env | (e.val.1 n).isSome}ᶜ ∪
    ({e : Env | condDev (K n) B e = 0} ∩ {e : Env | condMean (K n) B e = baseMean K B e}))

/-- **The exactly invariant version of the common constant**: the common mean on the invariant
set, zero elsewhere. -/
noncomputable def allStartsValue (K : ℕ → Kernel Env FlowCoding) (G : Set Env)
    (B : FlowSpace → ℝ) : Env → ℝ :=
  (allStartsSet K G B).indicator (baseMean K B)

section Kernels

variable {K : ℕ → Kernel Env FlowCoding} [∀ n, IsMarkovKernel (K n)]

theorem measurable_baseMean {B : FlowSpace → ℝ} (hB : Measurable B) :
    Measurable (baseMean K B) := by
  have h : Measurable fun p : Env × ℕ => condMean (K p.2) B p.1 :=
    measurable_from_prod_countable_left fun n => measurable_condMean (K n) hB
  exact h.comp (measurable_id.prodMk RegenerationLabelExhaustion.measurable_baseLabel)

theorem measurableSet_allStartsSet {G : Set Env} (hG : MeasurableSet G) {B : FlowSpace → ℝ}
    (hB : Measurable B) : MeasurableSet (allStartsSet K G B) := by
  refine hG.inter (MeasurableSet.iInter fun n => ?_)
  exact (RegenerationKernel.measurableSet_slotPresent n).compl.union
    ((measurableSet_constantSet (K n) hB).inter
      (measurableSet_eq_fun (measurable_condMean (K n) hB) (measurable_baseMean hB)))

theorem measurable_allStartsValue {G : Set Env} (hG : MeasurableSet G) {B : FlowSpace → ℝ}
    (hB : Measurable B) : Measurable (allStartsValue K G B) :=
  (measurable_baseMean hB).indicator (measurableSet_allStartsSet hG hB)

/-- **The invariant set is the set of all-starts constancy** (tex:1511: "test zero conditional
variance and equality of means on the countable vertex coding"). -/
theorem mem_allStartsSet_iff {G : Set Env} {B : FlowSpace → ℝ} (hB : Measurable B)
    (hb : ∀ p : FlowSpace, |B p| ≤ 1) {e : Env} :
    e ∈ allStartsSet K G B ↔ e ∈ G ∧ ∃ c : ℝ, AllStartsConst K B e c := by
  constructor
  · rintro ⟨heG, he⟩
    refine ⟨heG, baseMean K B e, fun n hn => ?_⟩
    rcases Set.mem_iInter.1 he n with hn' | ⟨hdev, hmean⟩
    · exact absurd hn hn'
    · have h := ae_eq_condMean_of_mem_constantSet (K n) hB hb (e := e) hdev
      filter_upwards [h] with x hx
      rw [hx]
      exact hmean
  · rintro ⟨heG, c, hc⟩
    refine ⟨heG, Set.mem_iInter.2 fun n => ?_⟩
    by_cases hn : (e.val.1 n).isSome
    · have hbase : baseMean K B e = c :=
        condMean_eq_of_ae_const (K (RegenerationLabelExhaustion.baseLabel e))
          (hc _ (RegenerationLabelExhaustion.baseLabel_isSome e))
      have hmean : condMean (K n) B e = baseMean K B e := by
        rw [hbase]
        exact condMean_eq_of_ae_const (K n) (hc n hn)
      exact Or.inr ⟨mem_constantSet_of_ae_const (K n) ⟨c, hc n hn⟩, hmean⟩
    · exact Or.inl hn

/-- On the invariant set the version is the common constant. -/
theorem allStartsValue_eq {G : Set Env} {B : FlowSpace → ℝ} (hB : Measurable B)
    (hb : ∀ p : FlowSpace, |B p| ≤ 1) {e : Env} {c : ℝ} (heG : e ∈ G)
    (hc : AllStartsConst K B e c) : allStartsValue K G B e = c := by
  rw [allStartsValue, Set.indicator_of_mem ((mem_allStartsSet_iff hB hb).2 ⟨heG, c, hc⟩)]
  exact condMean_eq_of_ae_const (K (RegenerationLabelExhaustion.baseLabel e))
    (hc _ (RegenerationLabelExhaustion.baseLabel_isSome e))

end Kernels

/-! ### 2. Exact similarity invariance from exact covariance of the all-starts laws -/

/-- **Exact similarity covariance of an all-starts family on a gate** (flow-level `law_φ`,
manuscript tex:1345 "reindexing the cells and scaling time are measurable operations on this
coding"): at every gate environment, every ACTIVE slot and every similarity `x ↦ s • (x - u)`,
the law from the image slot in the image environment is the image of the law under the coding
part of `reScale s ∘ reFrame u`.  Same shape as the `hcov` binder of
`CellRootedTimeMTP.cellRootedPlainTransport_of_startKernels`; at `FlowSlotKernel.flowSlotKernel`
it is `FlowSlotKernel.map_simCoding_flowSlotKernel` (symmetric form). -/
def SlotSimilarityCovariantOn (G : Set Env) (K : ℕ → Kernel Env FlowCoding) : Prop :=
  ∀ e ∈ G, ∀ n : ℕ, (e.val.1 n).isSome → ∀ (s : ℝ) (u : Plane) (hs : 0 < s),
    K (simLabel s u hs e n) (similarityTargetEnv s u hs e) =
      (K n e).map (CellRootedTimeMTP.simCoding s u e)

section Covariance

variable {K : ℕ → Kernel Env FlowCoding}

/-- **Transfer of an almost-sure value along a similarity**, for a test functional. -/
theorem ae_const_iff_of_covariant {G : Set Env} (hcov : SlotSimilarityCovariantOn G K)
    {B : FlowSpace → ℝ} (hB : CellRootedTest B) {e : Env} (he : e ∈ G) {n : ℕ}
    (hn : (e.val.1 n).isSome) {s : ℝ} (u : Plane) (hs : 0 < s) (c : ℝ) :
    (∀ᵐ x ∂K (simLabel s u hs e n) (similarityTargetEnv s u hs e),
        B (similarityTargetEnv s u hs e, x) = c) ↔ ∀ᵐ x ∂K n e, B (e, x) = c := by
  have hmeas : MeasurableSet {x : FlowCoding | B (similarityTargetEnv s u hs e, x) = c} :=
    measurableSet_eq_fun (hB.measurable.comp measurable_prodMk_left) measurable_const
  rw [hcov e he n hn s u hs,
    ae_map_iff (CellRootedTimeMTP.measurable_simCoding hs u e).aemeasurable hmeas]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  have hx : B (similarityTargetEnv s u hs e, CellRootedTimeMTP.simCoding s u e x) = B (e, x) := by
    rw [← CellRootedTimeMTP.reScale_reFrame_mk hs u e x, hB.scale s hs, hB.frame]
  rw [hx]

/-- All-starts constancy pulls back along a similarity from a gate environment. -/
theorem allStartsConst_of_isSimilarity {G : Set Env} (hcov : SlotSimilarityCovariantOn G K)
    {B : FlowSpace → ℝ} (hB : CellRootedTest B) {s : ℝ} {u : Plane} {hs : 0 < s} {e e' : Env}
    (hee' : IsSimilarity s u hs e e') (he : e ∈ G) {c : ℝ} (hc : AllStartsConst K B e' c) :
    AllStartsConst K B e c := by
  have he' : e' = similarityTargetEnv s u hs e := eq_similarityTargetEnv_of_isSimilarity hee'
  subst he'
  intro n hn
  exact (ae_const_iff_of_covariant hcov hB he hn u hs c).1 (hc _ (isSome_simLabel hn))

/-- **The version is exactly similarity invariant** (tex:1511: "It is preserved by similarities
because `B` is covariant and the conditional area-clock law transforms canonically"). -/
theorem similarityInvariantFun_allStartsValue [∀ n, IsMarkovKernel (K n)] {G : Set Env}
    (hGsim : SimilarityClosed G) (hcov : SlotSimilarityCovariantOn G K) {B : FlowSpace → ℝ}
    (hB : CellRootedTest B) : SimilarityInvariantFun (allStartsValue K G B) := by
  intro s u hs e e' hee'
  have hm := hB.measurable
  have hb := hB.bound
  by_cases he' : e' ∈ allStartsSet K G B
  · obtain ⟨he'G, c, hc⟩ := (mem_allStartsSet_iff hm hb).1 he'
    have heG : e ∈ G := (hGsim s u hs e e' hee').2 he'G
    rw [allStartsValue_eq hm hb heG (allStartsConst_of_isSimilarity hcov hB hee' heG hc),
      allStartsValue_eq hm hb he'G hc]
  · have he : e ∉ allStartsSet K G B := by
      intro he
      obtain ⟨heG, c, hc⟩ := (mem_allStartsSet_iff hm hb).1 he
      have he'G : e' ∈ G := (hGsim s u hs e e' hee').1 heG
      exact he' ((mem_allStartsSet_iff hm hb).2 ⟨he'G, c,
        allStartsConst_of_isSimilarity hcov hB (SimilarityClosedGate.isSimilarity_symm hee')
          he'G hc⟩)
    rw [allStartsValue, Set.indicator_of_notMem he, Set.indicator_of_notMem he']

end Covariance

/-! ### 3. The assembly at the cell-rooted law -/

/-- **`hregen` at the cell-rooted law from all-starts constancy** (tex:1511).  `b` is the exactly
invariant version `allStartsValue K G (B ∘ cellRoot)`; the identity `B = b ∘ fst` holds at every
live environment where the root law is the root member of the family and all-starts constancy
holds. -/
theorem regenerativeInvariance_cellRooted_of_allStarts (ν : Measure Env)
    (κ : Kernel Env FlowCoding) [IsMarkovKernel κ] {G : Set Env} (hGm : MeasurableSet G)
    (hGsim : SimilarityClosed G) (K : ℕ → Kernel Env FlowCoding) [∀ n, IsMarkovKernel (K n)]
    (hcov : SlotSimilarityCovariantOn G K)
    (hroot : ∀ᵐ e ∂ν, e ∈ G ∧ (e.val.1 (rootLabel e)).isSome ∧ κ e = K (rootLabel e) e)
    (hconst : ∀ B : FlowSpace → ℝ, CellRootedTest B →
      ∀ᵐ e ∂ν, ∃ c : ℝ, AllStartsConst K B e c) :
    RegenerativeInvariance ((ν ⊗ₘ κ).map cellRoot) reRootFlow reScale Prod.fst := by
  intro B hB hb hθ hS
  have hT : CellRootedTest fun ω => B (cellRoot ω) := cellRootedTest_comp_cellRoot hB hb hθ hS
  set B' : FlowSpace → ℝ := fun ω => B (cellRoot ω) with hB'def
  have hB'm : Measurable B' := hT.measurable
  have hb' : ∀ p : FlowSpace, |B' p| ≤ 1 := hT.bound
  set b : Env → ℝ := allStartsValue K G B' with hbdef
  have hbm : Measurable b := measurable_allStartsValue hGm hB'm
  have hbsim : SimilarityInvariantFun b := similarityInvariantFun_allStartsValue hGsim hcov hT
  refine ⟨b, hbm, hbsim, ?_⟩
  have hid : ∀ᵐ ω ∂(ν ⊗ₘ κ), B' ω = b ω.1 := by
    refine Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hB'm (hbm.comp measurable_fst)) ?_
    filter_upwards [hroot, hconst B' hT] with e he hce
    obtain ⟨heG, hlive, hκ⟩ := he
    obtain ⟨c, hc⟩ := hce
    have hbe : b e = c := allStartsValue_eq hB'm hb' heG hc
    rw [hκ]
    filter_upwards [hc _ hlive] with x hx
    show B' (e, x) = b e
    rw [hx, hbe]
  have hmeasQ : MeasurableSet {ω : FlowSpace | B ω = b ω.1} :=
    measurableSet_eq_fun hB (hbm.comp measurable_fst)
  rw [ae_map_iff measurable_cellRoot.aemeasurable hmeasQ]
  filter_upwards [hid] with ω hω
  have h1 : b ω.1 = b (cellRoot ω).1 := by
    rw [cellRoot_fst]
    exact hbsim 1 (ω.2.2.toFun 0) one_pos ω.1 _ (isSimilarity_translateEnv _ _)
  rw [← h1]
  exact hω

/-! ### 4. Start-cell independence (tex:1511, second paragraph) -/

/-- **The constant does not depend on the start** (tex:1511): per-start a.s. constants of a
`plainShift`-invariant functional agree when the area mixture `Σ_v a_v K_v(e)` is invariant under
the time shift by `1`, each `K_v(e)` starts at `v`, and every label is charged at time `1` at least
as much as by the raw area walk, which charges it (fixed-time positivity, PROVED). -/
theorem allStartsConst_of_startIndependence {G : Set Env}
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (he : e ∈ G)
    {K : ℕ → Kernel Env FlowCoding} [∀ n, IsMarkovKernel (K n)] {B : FlowSpace → ℝ}
    (hB : CellRootedTest B)
    (hF1 : ∀ n : ℕ, (e.val.1 n).isSome → ∃ c : ℝ, ∀ᵐ x ∂K n e, B (e, x) = c)
    (hstart : ∀ v : Vertex e.val, ∀ᵐ x ∂K v.val e, x.1.toFun 0 = ((v.val : ℕ) : ℕ∞))
    (hshift : MeasurePreserving (CellRootedTimeMTP.codingShift 1)
      (CellRootedTimeMTP.startMixture K e) (CellRootedTimeMTP.startMixture K e))
    (hmarg : ∀ v u : Vertex e.val, (areaFamily e).P v {ω | (areaFamily e).X 1 ω = some u} ≤
      K v.val e {x | x.1.toFun 1 = ((u.val : ℕ) : ℕ∞)}) :
    ∃ c : ℝ, AllStartsConst K B e c := by
  choose cv hcv using fun v : Vertex e.val => hF1 v.val v.property
  have hsame : ∀ v u : Vertex e.val, cv v = cv u := by
    intro v u
    have hraw := AreaWalkFixedTimePositivityWeld.areaWalkFixedTimePositivity_of_admissible hwalk
      e he v u 1 one_pos
    have hpos : K v.val e {x | x.1.toFun 1 = ((u.val : ℕ) : ℕ∞)} ≠ 0 := fun h0 =>
      hraw (le_antisymm ((hmarg v u).trans h0.le) bot_le)
    have hcode : Function.Injective fun v : Vertex e.val => ((v.val : ℕ) : ℕ∞) := by
      intro a b hab
      have hab' : ((a.val : ℕ) : ℕ∞) = ((b.val : ℕ) : ℕ∞) := hab
      exact Subtype.ext (by exact_mod_cast hab')
    have hlab : Measurable fun y : FlowCoding => y.1.toFun 0 :=
      (CadlagPath.measurable_eval 0).comp measurable_fst
    refine const_eq_of_shiftInvariantMixture (fun v : Vertex e.val => K v.val e)
      (fun v : Vertex e.val => volume ((decode e).cell v : Set Plane)) hshift
      hlab hcode hstart
      (hB.measurable.comp measurable_prodMk_left) (fun x => hB.shift 1 (e, x)) hcv
      (cellVolume_pos_lt_top (decode e) (decode_geometry e) v).1.ne' ?_
    refine fun h0 => hpos (measure_mono_null (fun x hx => ?_) h0)
    show x.1.toFun (0 + 1) = ((u.val : ℕ) : ℕ∞)
    rw [zero_add]
    exact hx
  refine ⟨cv (RegenerationLabelExhaustion.baseVertex e), fun n hn => ?_⟩
  have h := hcv ⟨n, hn⟩
  rw [hsame ⟨n, hn⟩ (RegenerationLabelExhaustion.baseVertex e)] at h
  exact h

/-! ### 5. (F1) at every start from (F1) at the root of an interior translate -/

/-- **(F1) at every active start of a gate environment** from (F1) at every LIVE gate
environment: with `w := z e n` interior to cell `n` and off the mask, the translate
`translateEnv w e` is live with root label `simLabel 1 w e n`, and the law from `n` is the
frame-back of its root law (exact covariance at `s = 1`). -/
theorem allStartsF1_of_root {G : Set Env} (hGsim : SimilarityClosed G)
    {κ : Kernel Env FlowCoding} {K : ℕ → Kernel Env FlowCoding}
    (hcov : SlotSimilarityCovariantOn G K) (hroot : ∀ e, Live G e → κ e = K (rootLabel e) e)
    {z : Env → ℕ → Plane} (hz : InteriorOffMask z) {B : FlowSpace → ℝ} (hB : CellRootedTest B)
    (hF1 : ∀ e, Live G e → ∃ c : ℝ, ∀ᵐ x ∂κ e, B (e, x) = c) {e : Env} (he : e ∈ G)
    {n : ℕ} (hn : (e.val.1 n).isSome) : ∃ c : ℝ, ∀ᵐ x ∂K n e, B (e, x) = c := by
  obtain ⟨v', hv', hlab⟩ := (OriginRootedTransportObstruction.rootedAt_similarity_iff
    (u := z e n) one_pos e ((n : ℕ) : ℕ∞)).2 ⟨⟨n, hn⟩, rootAt_of_interiorOffMask hz e n hn, rfl⟩
  have he'' : similarityTargetEnv 1 (z e n) one_pos e ∈ G :=
    (hGsim 1 (z e n) one_pos e _ (isSimilarity_similarityTargetEnv 1 (z e n) one_pos e)).1 he
  have hroot'' : rootLabel (similarityTargetEnv 1 (z e n) one_pos e) =
      simLabel 1 (z e n) one_pos e n := by
    rw [rootLabel_of_some hv']
    rw [liftLabel_natCast] at hlab
    exact_mod_cast hlab.symm
  have hlive : Live G (similarityTargetEnv 1 (z e n) one_pos e) :=
    ⟨he'', by rw [rootLabel_of_some hv']; exact v'.property⟩
  obtain ⟨c, hc⟩ := hF1 _ hlive
  rw [hroot _ hlive, hroot''] at hc
  exact ⟨c, (ae_const_iff_of_covariant hcov hB he hn (z e n) one_pos c).1 hc⟩

/-! ### 6. (F1) at a live root from cycle ergodicity: the rational-shift bridge, POINTWISE -/

/-- **B1: the rational-shift bridge at EVERY live gate environment** (not only `ν`-a.e.: the
all-starts set at a typical `e` needs (F1) at the interior translates of `e`, which are not
`ν`-typical).  Argued TRUE in `CellRootedRegenerativeInvariance.RatShiftBridge`: a.s. no jump of
the path at `q + T_k` (`q ∈ ℚ`, `T_k` the return times) by the strong Markov property at the
return times and continuity of the exponential holding laws — a fixed-environment statement, so
pointwise in `e` is its natural form.  Not proved in this file; PROVED at `interiorField` and the similarity-closed gate by
`RatShiftBridgeProof.ratShiftBridgeOn_interiorField` (2026-09-18). -/
def RatShiftBridgeOn (z : CellField) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) : Prop :=
  ∀ e, Live G e → RatShiftBridge (fun w => ratCode z (e, w.val))
    (rootedRegKernel G hG hwalk (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e)

/-- **(F1) at every live gate environment** from the PROVED cycle ergodicity and B1. -/
theorem rootF1_of_ratShiftBridgeOn {z : CellField} {G : Set Env} {hG : MeasurableSet G}
    {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} (hext : ExtensionGate z G)
    (hbr : RatShiftBridgeOn z G hG hwalk) {B : FlowSpace → ℝ} (hB : CellRootedTest B) (e : Env)
    (he : Live G e) : ∃ c : ℝ, ∀ᵐ x ∂flowKernel z G hG hwalk hext e, B (e, x) = c :=
  ae_const_flowKernel_of_ratShiftBridge z G hG hwalk hext e (hbr e he) hB.measurable hB.bound
    hB.shift

/-! ### 7. The fibre shape of the all-starts kernel and its consequences -/

/-- **The fibre shape of an all-starts family** (definitional for `FlowSlotKernel.flowSlotKernel`:
`slotFibre_of_live`): at a gate environment the law from an active vertex `v` is the image of two
independent area walks from `v` under `FlowCodingKernel.build`. -/
def SlotFibreShape (z : CellField) (G : Set Env) (K : ℕ → Kernel Env FlowCoding) : Prop :=
  ∀ e ∈ G, ∀ v : Vertex e.val,
    K v.val e = (((areaFamily e).P v).prod ((areaFamily e).P v)).map (build z e v)

/-- The good sample pairs are conull from every start with an a.s. extension (the all-starts form
of `FlowCodingKernel.ae_mem_goodSet`; identical to `FlowSlotKernel.ae_mem_goodSet_of_ext`, whose
module is not yet checked — replace by it once it is). -/
theorem ae_mem_goodSet_allStarts {z : CellField} {e : Env}
    (hadm : EnvironmentAreaClockAdmissible e) (r : Vertex e.val)
    (hext : ∀ᵐ ω ∂(areaFamily e).P r, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t v, (areaFamily e).X t ω = some v → Z t = z.at e v) :
    ∀ᵐ ω ∂(((areaFamily e).P r).prod ((areaFamily e).P r)), ω ∈ goodSet z e r := by
  set P := (areaFamily e).P r with hPdef
  have hw := isReflectedWalk_areaFamily e hadm
  have hhalf : ∀ᵐ ω ∂P, HalfGood z e r ω := by
    have hfix : ∀ᵐ ω ∂P, ∀ q : ℚ, (∃ v, (areaFamily e).X (q : ℝ).toNNReal ω = some v) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball ((q : ℝ).toNNReal) ε,
          (areaFamily e).X s ω = (areaFamily e).X (q : ℝ).toNNReal ω :=
      ae_all_iff.2 fun q => (hw r).2.1 ((q : ℝ).toNNReal)
    filter_upwards [TwoSidedCycleSplice.ae_isRegLL_label e hadm r, hext, hfix, (hw r).1]
      with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hpair : ∀ᵐ ω ∂(P.prod P), HalfGood z e r ω.1 ∧ HalfGood z e r ω.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hhalf,
      Measure.quasiMeasurePreserving_snd.ae hhalf] with ω h1 h2
    exact ⟨h1, h2⟩
  have hnull : (P.prod P) (toMeasurable (P.prod P)
      {ω | ¬ (HalfGood z e r ω.1 ∧ HalfGood z e r ω.2)}) = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hpair
  rw [ae_iff]
  have hc : {ω | ¬ ω ∈ goodSet z e r} = toMeasurable (P.prod P)
      {ω | ¬ (HalfGood z e r ω.1 ∧ HalfGood z e r ω.2)} := by
    ext ω
    simp [goodSet, hPdef]
  rw [hc]
  exact hnull

section FibreShape

variable {z : CellField} {G : Set Env} {K : ℕ → Kernel Env FlowCoding}

/-- **Root identification**: at a live environment the origin-rooted bridge kernel is the root
member of the family. -/
theorem flowKernel_eq_of_slotFibreShape (hfib : SlotFibreShape z G K) {hG : MeasurableSet G}
    {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} {hext : ExtensionGate z G} {e : Env}
    (h : Live G e) : flowKernel z G hG hwalk hext e = K (rootLabel e) e := by
  rw [flowKernel_apply, flowFibre_of_live h]
  exact (hfib e h.1 (rootVertex h)).symm

/-- **The law from `v` starts at `v`.** -/
theorem ae_start_of_slotFibreShape (hfib : SlotFibreShape z G K)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hextA : ∀ e ∈ G, ExtensionGateAllStarts.ExtensionAllStarts z e) {e : Env} (he : e ∈ G)
    (v : Vertex e.val) : ∀ᵐ x ∂K v.val e, x.1.toFun 0 = ((v.val : ℕ) : ℕ∞) := by
  have hS : MeasurableSet {x : FlowCoding | x.1.toFun 0 = ((v.val : ℕ) : ℕ∞)} :=
    ((CadlagPath.measurable_eval 0).comp measurable_fst) (measurableSet_singleton _)
  rw [hfib e he v]
  refine (ae_map_iff (measurable_build z e v).aemeasurable hS).2 ?_
  filter_upwards [ae_mem_goodSet_allStarts (hwalk e he) v (hextA e he v)] with ω hω
  exact build_label_zero hω

/-- **One-time marginal comparison with the raw area law** at time `1`. -/
theorem raw_le_of_slotFibreShape (hfib : SlotFibreShape z G K)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hextA : ∀ e ∈ G, ExtensionGateAllStarts.ExtensionAllStarts z e) {e : Env} (he : e ∈ G)
    (v u : Vertex e.val) :
    (areaFamily e).P v {ω | (areaFamily e).X 1 ω = some u} ≤
      K v.val e {x | x.1.toFun 1 = ((u.val : ℕ) : ℕ∞)} := by
  set P := (areaFamily e).P v with hPdef
  have hS : MeasurableSet {x : FlowCoding | x.1.toFun 1 = ((u.val : ℕ) : ℕ∞)} :=
    ((CadlagPath.measurable_eval 1).comp measurable_fst) (measurableSet_singleton _)
  have hgood := ae_mem_goodSet_allStarts (hwalk e he) v (hextA e he v)
  rw [hfib e he v, Measure.map_apply (measurable_build z e v) hS]
  calc P {ω | (areaFamily e).X 1 ω = some u}
      = (P.prod P) ({ω | (areaFamily e).X 1 ω = some u} ×ˢ univ) := by
        rw [Measure.prod_prod, measure_univ, mul_one]
    _ = (P.prod P) ({ω | (areaFamily e).X 1 ω = some u} ×ˢ univ ∩ goodSet z e v) :=
        (measure_inter_conull (mem_ae_iff.1 hgood)).symm
    _ ≤ (P.prod P) (build z e v ⁻¹' {x | x.1.toFun 1 = ((u.val : ℕ) : ℕ∞)}) := by
        refine measure_mono fun ω hω => ?_
        have h1 : (areaFamily e).X 1 ω.1 = some u := hω.1.1
        show (build z e v ω).1.toFun 1 = ((u.val : ℕ) : ℕ∞)
        rw [build_label_of_nonneg hω.2 zero_le_one, Real.toNNReal_one, h1]
        rfl

end FibreShape

/-! ### 8. The final theorems -/

/-- **`hregen` at the cell-rooted law, the manuscript's way**, at any measurable, similarity-closed,
conull, admissible gate `G`, any interior off-mask representative `z`, and any all-starts family
`K` with the fibre shape and exact covariance on `G`.

CONDITIONAL on `hfib`, `hcov` (the all-starts kernel: `FlowSlotKernel`, A1), `hshift` (A2) and
`hbr` (B1). -/
theorem regenerativeInvariance_cellRooted_allStarts (ν : Measure Env) (hmt : MassTransport ν)
    {z : CellField} (hz : InteriorOffMask z.value) {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hGsim : SimilarityClosed G)
    (hGc : ν Gᶜ = 0) (hextA : ∀ e ∈ G, ExtensionGateAllStarts.ExtensionAllStarts z e)
    (hext : ExtensionGate z G) (K : ℕ → Kernel Env FlowCoding) [∀ n, IsMarkovKernel (K n)]
    (hfib : SlotFibreShape z G K) (hcov : SlotSimilarityCovariantOn G K)
    (hshift : ∀ᵐ e ∂ν, ∀ r : ℝ, MeasurePreserving (CellRootedTimeMTP.codingShift r)
      (CellRootedTimeMTP.startMixture K e) (CellRootedTimeMTP.startMixture K e))
    (hbr : RatShiftBridgeOn z G hG hwalk) :
    RegenerativeInvariance ((ν ⊗ₘ flowKernel z G hG hwalk hext).map cellRoot) reRootFlow
      reScale Prod.fst := by
  have hGae : ∀ᵐ e ∂ν, e ∈ G := ae_iff.2 hGc
  refine regenerativeInvariance_cellRooted_of_allStarts ν _ hG hGsim K hcov ?_ ?_
  · filter_upwards [hGae, Spatial.ae_notMem_boundaryMask_of_massTransport ν hmt] with e he hm
    obtain ⟨root, hroot, -⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode e)
      (decode_geometry e) hm
    have hlive : Live G e := ⟨he, by rw [rootLabel_of_some hroot]; exact root.property⟩
    exact ⟨he, hlive.2, flowKernel_eq_of_slotFibreShape hfib hlive⟩
  · intro B hB
    filter_upwards [hGae, hshift] with e he hsh
    exact allStartsConst_of_startIndependence hwalk he hB
      (fun n hn => allStartsF1_of_root hGsim hcov
        (fun e' he' => flowKernel_eq_of_slotFibreShape (hG := hG) (hwalk := hwalk) (hext := hext)
          hfib he') hz hB
        (fun e' he' => rootF1_of_ratShiftBridgeOn hext hbr hB e' he') he hn)
      (ae_start_of_slotFibreShape hfib hwalk hextA he) (hsh 1)
      (raw_le_of_slotFibreShape hfib hwalk hextA he)

/-- **The frontier binder `hregen`** of
`CellRootedFrontier.reflectedInvarianceConclusions_validLaw_cellRootedFrontier` at the interior
representative, in its exact shape
(any conull admissible gate `G` of the frontier), from the all-starts family at the
similarity-closed gate.  Gate data, closure, extension at all starts, positivity, cycle
ergodicity and the representative are all discharged.

CONDITIONAL on `hfib`, `hcov` (A1, `FlowSlotKernel`), `hshift` (A2), `hbr` (B1). -/
theorem regenerativeInvariance_validLaw_interior_allStarts (P : Measure RawCode)
    [IsProbabilityMeasure P] (hP : SupportedOnValid P) (hmt : AmbientMassTransport P hP)
    (hFE : FiniteEnergyMoment (validLaw P hP)) (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e)
    (hext : ExtensionGate InteriorRepresentative.interiorField G)
    (hGc : validLaw P hP Gᶜ = 0) (K : ℕ → Kernel Env FlowCoding) [∀ n, IsMarkovKernel (K n)]
    (hfib : SlotFibreShape InteriorRepresentative.interiorField
      SimilarityClosedGate.similarityClosedGate K)
    (hcov : SlotSimilarityCovariantOn SimilarityClosedGate.similarityClosedGate K)
    (hshift : ∀ᵐ e ∂validLaw P hP, ∀ r : ℝ, MeasurePreserving (CellRootedTimeMTP.codingShift r)
      (CellRootedTimeMTP.startMixture K e) (CellRootedTimeMTP.startMixture K e))
    (hbr : RatShiftBridgeOn InteriorRepresentative.interiorField
      SimilarityClosedGate.similarityClosedGate SimilarityClosedGate.measurableSet_similarityClosedGate
      (fun _ he => SimilarityClosedGate.environmentAreaClockAdmissible_of_mem he)) :
    RegenerativeInvariance
      ((validLaw P hP ⊗ₘ flowKernel InteriorRepresentative.interiorField G hG hwalk hext).map
        cellRoot) reRootFlow reScale Prod.fst := by
  rw [ExtensionGateAllStarts.compProd_closedGateFlowKernel (validLaw P hP) hmt hFE hG hwalk hext
    hGc]
  exact regenerativeInvariance_cellRooted_allStarts (validLaw P hP) hmt
    InteriorRepresentative.interiorOffMask_interiorField
    SimilarityClosedGate.measurableSet_similarityClosedGate
    (fun _ he => SimilarityClosedGate.environmentAreaClockAdmissible_of_mem he)
    similarityClosed_similarityClosedGate
    (SimilarityClosedGate.measure_compl_similarityClosedGate (validLaw P hP) hmt hFE)
    (fun _ he => ExtensionGateAllStarts.extensionAllStarts_interiorField he)
    ExtensionGateAllStarts.extensionGate_interiorField_similarityClosedGate K hfib hcov hshift hbr

end ReflectedGMS.CellRootedRegenAllStarts
