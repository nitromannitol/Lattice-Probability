/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RegenerationKernelMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RegenerationLabelExhaustion
import LatticeProb.Bonanno.ReflectedWalk.Step1

/-!
# `hmeas` of the regeneration kernel is PROVED: the area-clock transition function is measurable

`Temporal/RegenerationKernel.rootedKernel G hG hwalk hmeas` builds the two-sided regeneration
kernel `κ : Kernel Code.Env TwoSidedCoding` from ONE open input,

  `hmeas : ∀ n t m, Measurable (slotTransition G n t m)`,

the area-clock transition function `e ↦ P_e^{H_n}(X_t = H_m)` on an admissible gate `G`.  This
module proves it (`measurable_slotTransition`), with no hypothesis beyond the gate's own
(`MeasurableSet G`, `∀ e ∈ G, EnvironmentAreaClockAdmissible e`), and gives the kernel with
`hmeas` discharged (`regenerationKernel`, `exists_regenerationKernel`).

## The route (Gwynne–Sung Step 1–2, along a label-canonical exhaustion)

* **Step 1–2 identify the transition function at every admissible environment.**  At `e ∈ G`
  the area family is a reflected walk (`isReflectedWalk_areaFamily`), so for ANY exhaustion
  `E` of the cell graph the measurable time changes `X̃ⁿ` of (3.32) approximate it at fixed
  times, with one-time marginals the transition function of the level chain `Xⁿ` of (3.15)
  (`ReflectedWalk.Theorem16.exists_approximant`, the holding-time divergence being
  `ae_tsum_stepHolding_eq_top`); bounded convergence gives
  `P_e^{H_n}(X_t = H_m) = lim_k (E.chainLaw (n_x + k) x ⊗ₘ holdingKernel w){jumpPath · t = y}`
  (`tendsto_labelPairLaw`).  We take `E := RegenerationLabelExhaustion.labelExhaustion e`,
  whose levels are measurable in the labels — NOT the `Classical.choose` exhaustion of
  `areaFamily`: the limit does not see the exhaustion.
* **Each level-chain law is measurable in the environment.**  `labelPairLaw N x e` is the law of
  the level-`N` embedded chain from label `x` and its area holding times, read in the labels, on
  the environment-independent space `(ℕ → ℕ) × (ℕ → ℝ)`.  Its masses on the prefix rectangles
  `Theorem16.pairRect` (a generating π-system, `generateFrom_pairRects`) are products of the
  label transition probabilities (3.2)–(3.3) and of exponential masses at the area rates
  (`labelPairLaw_pairRect`, the prefix law `chainLaw_prefixEvent` and the product form
  `holdingKernel_apply`), all measurable (`RegenerationLabelExhaustion`: the harmonic measure of
  the actual graph is measurable), so `e ↦ labelPairLaw N x e` is measurable (π-λ,
  `measurable_labelPairLaw`).  The level `n_x + k` is itself measurable
  (`measurable_levelIndex`).
* **The limit of measurable functions is measurable** (`measurable_of_tendsto_metrizable`), and
  the gate is a measurable indicator.

## By-product: exhaustion independence of the area-clock law (at admissible exhaustions)

`areaTransition_eq_of_exhaustion` / `identDistrib_areaFamily_of_exhaustion`: at an environment
where the area clock construction on an exhaustion `D` satisfies the clock clause
`AreaClockReachesLevelZeroIndices e D`, its transition function and its trajectory law from every
start agree with those of `areaFamily e`.  This is Theorem 1.6 uniqueness (both are reflected walks
with the same data) and says nothing about exhaustions violating the clock clause.

Nothing here certifies `p:lem:regeninvariant`, `p:prop:timeergodic`, `p:lem:bracketlimit`,
`p:thm:areaclt` or either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.RegenerationKernelMeasurability

open Code EnvironmentLaws AreaClocks
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.TwoSidedRegenerationCoding
open ReflectedGMS.RegenerationKernel ReflectedGMS.RegenerationLabelExhaustion

/-! ### 1. Reading a chain-and-holding-times pair in the labels -/

/-- The label coding of a pair (embedded chain, holding times). -/
def labelPair {r : RawCode} (p : (ℕ → Vertex r) × (ℕ → ℝ)) : (ℕ → ℕ) × (ℕ → ℝ) :=
  (fun i => (p.1 i).val, p.2)

theorem measurable_labelPair {r : RawCode} : Measurable (labelPair (r := r)) := by
  have h1 : Measurable fun p : (ℕ → Vertex r) × (ℕ → ℝ) => fun i => (p.1 i).val :=
    measurable_pi_iff.2 fun i =>
      measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst)
  exact h1.prodMk measurable_snd

/-- The time change (3.15) commutes with the label coding. -/
theorem jumpPath_labelPair {r : RawCode} (p : (ℕ → Vertex r) × (ℕ → ℝ)) (t : ℝ≥0) :
    ContinuousTimeChain.jumpPath (labelPair p) t =
      (ContinuousTimeChain.jumpPath p t).map Subtype.val := by
  by_cases h : ∃ k, ContinuousTimeChain.InJump p.2 k (t : ℝ≥0∞)
  · obtain ⟨k, hk⟩ := h
    rw [ContinuousTimeChain.jumpPath_eq_of_inJump (p := labelPair p) hk,
      ContinuousTimeChain.jumpPath_eq_of_inJump hk]
    rfl
  · rw [(ContinuousTimeChain.jumpPath_eq_none_iff (labelPair p) t).2 h,
      (ContinuousTimeChain.jumpPath_eq_none_iff p t).2 h]
    rfl

/-- A label path read in the vertices, with the base vertex at absent labels. -/
noncomputable def vertexPath (e : Env) (g : ℕ → ℕ) (j : ℕ) : Vertex e.val :=
  if h : (e.val.1 (g j)).isSome then ⟨g j, h⟩ else baseVertex e

theorem vertexPath_of_isSome {e : Env} {g : ℕ → ℕ} {j : ℕ} (h : (e.val.1 (g j)).isSome) :
    vertexPath e g j = ⟨g j, h⟩ := dif_pos h

theorem labelPair_preimage_pairRect_of_active (e : Env) (m : ℕ) (g : ℕ → ℕ) (B : ℕ → Set ℝ)
    (hall : ∀ j ≤ m, (e.val.1 (g j)).isSome) :
    labelPair (r := e.val) ⁻¹' pairRect m g B = pairRect m (vertexPath e g) B := by
  ext p
  simp only [Set.mem_preimage, pairRect, Set.mem_prod, Set.mem_ofPred_eq, labelPair]
  refine and_congr_left fun _ => forall₂_congr fun j hj => ?_
  rw [vertexPath_of_isSome (hall j hj), Subtype.ext_iff]

theorem labelPair_preimage_pairRect_of_not (e : Env) (m : ℕ) (g : ℕ → ℕ) (B : ℕ → Set ℝ)
    (hall : ¬ ∀ j ≤ m, (e.val.1 (g j)).isSome) :
    labelPair (r := e.val) ⁻¹' pairRect m g B = ∅ := by
  ext p
  simp only [Set.mem_preimage, pairRect, Set.mem_prod, Set.mem_ofPred_eq, labelPair,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro h1
  exact absurd (fun j hj => (h1 j hj) ▸ (p.1 j).property) hall

/-! ### 2. The labelled pair law of a level chain -/

/-- **The labelled pair law**: the joint law of the level-`N` embedded chain of the
label-canonical exhaustion started at label `x` and of its area holding times, read in the
labels; a point mass at an absent start. -/
noncomputable def labelPairLaw (N x : ℕ) (e : Env) : Measure ((ℕ → ℕ) × (ℕ → ℝ)) :=
  if hx : (e.val.1 x).isSome then
    letI := nontrivial_vertex e
    ((labelExhaustion e).chainLaw (decode_connected e) N ⟨x, hx⟩ ⊗ₘ
      holdingKernel (areaRate (decode e))).map labelPair
  else Measure.dirac (fun _ => x, fun _ => 1)

instance labelPairLaw_isProbabilityMeasure (N x : ℕ) (e : Env) :
    IsProbabilityMeasure (labelPairLaw N x e) := by
  unfold labelPairLaw
  split_ifs with hx
  · haveI := nontrivial_vertex e
    infer_instance
  · infer_instance

/-- **The mass of a prefix rectangle** (the label form of the right-hand side of
`Theorem16.map_embeddedPairOf`): exponential masses at the area rates times the prefix
probabilities of the level chain. -/
theorem labelPairLaw_pairRect (N x : ℕ) (e : Env) (hx : (e.val.1 x).isSome) (m : ℕ)
    (g : ℕ → ℕ) {B : ℕ → Set ℝ} (hB : ∀ j, MeasurableSet (B j))
    (hall : ∀ j ≤ m, (e.val.1 (g j)).isSome) :
    labelPairLaw N x e (pairRect m g B) =
      (∏ i ∈ Finset.range m, ProbabilityTheory.expMeasure (labelRate e (g i)) (B i)) *
        ((if g 0 = x then 1 else 0) *
          ∏ i ∈ Finset.range m, ENNReal.ofReal (labelTransProb N e (g i) (g (i + 1)))) := by
  haveI := nontrivial_vertex e
  have hw : ∀ v : Vertex e.val, 0 < areaRate (decode e) v := areaRate_pos e
  rw [labelPairLaw, dif_pos hx,
    Measure.map_apply measurable_labelPair (measurableSet_pairRect m g hB),
    labelPair_preimage_pairRect_of_active e m g B hall]
  have hA : MeasurableSet {y : ℕ → Vertex e.val | ∀ j ≤ m, y j = vertexPath e g j} :=
    measurableSet_prefixEvent (vertexPath e g) m
  have hD : MeasurableSet (Set.pi (↑(Finset.range m)) B) :=
    MeasurableSet.pi (Finset.range m).countable_toSet fun j _ => hB j
  have hker : ∀ y ∈ {y : ℕ → Vertex e.val | ∀ j ≤ m, y j = vertexPath e g j},
      holdingKernel (areaRate (decode e)) y (Set.pi (↑(Finset.range m)) B) =
        ∏ i ∈ Finset.range m,
          ProbabilityTheory.expMeasure (areaRate (decode e) (vertexPath e g i)) (B i) := by
    intro y hy
    haveI : ∀ i : ℕ, IsProbabilityMeasure
        (ProbabilityTheory.expMeasure (areaRate (decode e) (y i))) :=
      fun i => ProbabilityTheory.isProbabilityMeasure_expMeasure (hw (y i))
    rw [holdingKernel_apply hw y, Measure.infinitePi_pi _ fun j _ => hB j]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hy i (le_of_lt (Finset.mem_range.1 hi))]
  rw [pairRect, Measure.compProd_apply_prod hA hD,
    lintegral_congr_ae ((ae_restrict_iff' hA).2 (ae_of_all _ hker)), setLIntegral_const,
    ConductanceGraph.Exhaustion.chainLaw,
    chainLaw_prefixEvent ((labelExhaustion e).stepKernel (decode_connected e) N) m ⟨x, hx⟩
      (vertexPath e g)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : (e.val.1 (g i)).isSome := hall i (le_of_lt (Finset.mem_range.1 hi))
    rw [vertexPath_of_isSome hi', labelRate_of_isSome hi']
  · congr 1
    · have h0 : (e.val.1 (g 0)).isSome := hall 0 (Nat.zero_le m)
      rw [vertexPath_of_isSome h0]
      by_cases hg : g 0 = x
      · have hv : (⟨g 0, h0⟩ : Vertex e.val) = ⟨x, hx⟩ := Subtype.ext hg
        rw [if_pos hv, if_pos hg]
      · have hv : (⟨g 0, h0⟩ : Vertex e.val) ≠ ⟨x, hx⟩ :=
          fun h => hg (congrArg Subtype.val h)
        rw [if_neg hv, if_neg hg]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi1 : (e.val.1 (g i)).isSome := hall i (le_of_lt (Finset.mem_range.1 hi))
      have hi2 : (e.val.1 (g (i + 1))).isSome := hall (i + 1) (Finset.mem_range.1 hi)
      rw [ConductanceGraph.Exhaustion.stepKernel_singleton, vertexPath_of_isSome hi1,
        vertexPath_of_isSome hi2, labelTransProb_of_isSome hi1 hi2]
      rfl

/-- The exponential mass of a Borel set is measurable in the rate. -/
theorem measurable_expMeasure_apply {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun r : ℝ => ProbabilityTheory.expMeasure r B := by
  have heq : (fun r : ℝ => ProbabilityTheory.expMeasure r B) =
      fun r => ∫⁻ y in B, ProbabilityTheory.exponentialPDF r y := by
    funext r
    rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure, withDensity_apply _ hB]
    rfl
  rw [heq]
  have hf : Measurable fun q : ℝ × ℝ => ProbabilityTheory.exponentialPDF q.1 q.2 := by
    have hq : (fun q : ℝ × ℝ => ProbabilityTheory.exponentialPDF q.1 q.2) =
        fun q => ENNReal.ofReal (if 0 ≤ q.2 then q.1 * Real.exp (-(q.1 * q.2)) else 0) :=
      funext fun q => ProbabilityTheory.exponentialPDF_eq q.1 q.2
    rw [hq]
    refine ENNReal.measurable_ofReal.comp
      (Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ measurable_const)
    exact measurable_fst.mul (Real.measurable_exp.comp ((measurable_fst.mul measurable_snd).neg))
  exact hf.lintegral_prod_right'

/-- The prefix-rectangle masses of the labelled pair law are measurable in the environment. -/
theorem measurable_labelPairLaw_pairRect (N x m : ℕ) (g : ℕ → ℕ) {B : ℕ → Set ℝ}
    (hB : ∀ j, MeasurableSet (B j)) :
    Measurable fun e : Env => labelPairLaw N x e (pairRect m g B) := by
  classical
  set A : Set Env := ⋂ j : Fin (m + 1), {e : Env | (e.val.1 (g j)).isSome} with hAdef
  have hAiff : ∀ e : Env, e ∈ A ↔ ∀ j ≤ m, (e.val.1 (g j)).isSome := by
    intro e
    rw [hAdef, Set.mem_iInter]
    exact ⟨fun h j hj => h ⟨j, Nat.lt_succ_of_le hj⟩, fun h j => h j (Nat.le_of_lt_succ j.isLt)⟩
  have heq : (fun e : Env => labelPairLaw N x e (pairRect m g B)) = fun e =>
      if e ∈ {e : Env | (e.val.1 x).isSome} then
        (if e ∈ A then
          (∏ i ∈ Finset.range m, ProbabilityTheory.expMeasure (labelRate e (g i)) (B i)) *
            ((if g 0 = x then 1 else 0) *
              ∏ i ∈ Finset.range m, ENNReal.ofReal (labelTransProb N e (g i) (g (i + 1))))
         else 0)
      else Measure.dirac ((fun _ => x, fun _ => 1) : (ℕ → ℕ) × (ℕ → ℝ)) (pairRect m g B) := by
    funext e
    by_cases hx : (e.val.1 x).isSome
    · have hxS : e ∈ {e : Env | (e.val.1 x).isSome} := hx
      rw [if_pos hxS]
      by_cases hall : ∀ j ≤ m, (e.val.1 (g j)).isSome
      · rw [if_pos ((hAiff e).2 hall), labelPairLaw_pairRect N x e hx m g hB hall]
      · haveI := nontrivial_vertex e
        rw [if_neg (fun h => hall ((hAiff e).1 h)), labelPairLaw, dif_pos hx,
          Measure.map_apply measurable_labelPair (measurableSet_pairRect m g hB),
          labelPair_preimage_pairRect_of_not e m g B hall, measure_empty]
    · have hxS : e ∉ {e : Env | (e.val.1 x).isSome} := hx
      rw [if_neg hxS, labelPairLaw, dif_neg hx]
  rw [heq]
  have hAm : MeasurableSet A :=
    MeasurableSet.iInter fun j => RegenerationKernel.measurableSet_slotPresent (g j)
  refine Measurable.ite (RegenerationKernel.measurableSet_slotPresent x)
    (Measurable.ite hAm ?_ measurable_const) measurable_const
  refine (Finset.measurable_prod _ fun i _ =>
    (measurable_expMeasure_apply (hB i)).comp (measurable_labelRate (g i))).mul
    (measurable_const.mul (Finset.measurable_prod _ fun i _ =>
      (measurable_labelTransProb N (g i) (g (i + 1))).ennreal_ofReal))

/-- **The labelled pair law is measurable in the environment** (π-λ on the prefix
rectangles). -/
theorem measurable_labelPairLaw (N x : ℕ) : Measurable (labelPairLaw N x) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable fun e : Env => labelPairLaw N x e s)
    (generateFrom_pairRects (V := ℕ) 0).symm isPiSystem_pairRects ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]
    exact measurable_const
  · rintro t ⟨m, g, B, hB, rfl⟩
    exact measurable_labelPairLaw_pairRect N x m g hB
  · intro t htm hC
    have heq : (fun e : Env => labelPairLaw N x e tᶜ) = fun e => 1 - labelPairLaw N x e t := by
      funext e
      rw [measure_compl htm (measure_ne_top _ _), measure_univ]
    rw [heq]
    exact measurable_const.sub hC
  · intro f hdisj hfm hC
    have heq : (fun e : Env => labelPairLaw N x e (⋃ k, f k)) =
        fun e => ∑' k, labelPairLaw N x e (f k) := by
      funext e
      exact measure_iUnion hdisj hfm
    rw [heq]
    exact Measurable.ennreal_tsum hC

/-- The labelled pair law at the level `n_x + k` of the start is measurable in the
environment. -/
theorem measurable_labelPairLaw_levelIndex (x k : ℕ) {s : Set ((ℕ → ℕ) × (ℕ → ℝ))}
    (hs : MeasurableSet s) :
    Measurable fun e : Env => labelPairLaw (levelIndex e x + k) x e s := by
  have h2 : Measurable fun q : Env × ℕ => labelPairLaw q.2 x q.1 s :=
    measurable_from_prod_countable_left fun N =>
      (Measure.measurable_coe hs).comp (measurable_labelPairLaw N x)
  have hlev : Measurable fun e : Env => levelIndex e x + k :=
    (Measurable.of_discrete (f := fun a : ℕ => a + k)).comp (measurable_levelIndex x)
  exact h2.comp (measurable_id.prodMk hlev)

/-! ### 3. The level-chain transition in the labels, and Step 1–2 -/

/-- The level-chain transition probability is the labelled pair law of the time-change event. -/
theorem chainTransition_eq_labelPairLaw (e : Env) (N : ℕ) {x y : ℕ} (hx : (e.val.1 x).isSome)
    (hy : (e.val.1 y).isSome) (t : ℝ≥0) :
    letI := nontrivial_vertex e
    ((labelExhaustion e).chainLaw (decode_connected e) N ⟨x, hx⟩ ⊗ₘ
        holdingKernel (areaRate (decode e)))
        {p | ContinuousTimeChain.jumpPath p t = some (⟨y, hy⟩ : Vertex e.val)} =
      labelPairLaw N x e {p | ContinuousTimeChain.jumpPath p t = some y} := by
  haveI := nontrivial_vertex e
  have hS : MeasurableSet {p : (ℕ → ℕ) × (ℕ → ℝ) | ContinuousTimeChain.jumpPath p t = some y} :=
    ContinuousTimeChain.measurable_jumpPath t (measurableSet_singleton _)
  rw [labelPairLaw, dif_pos hx, Measure.map_apply measurable_labelPair hS]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, jumpPath_labelPair]
  cases h : ContinuousTimeChain.jumpPath p t with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun hv => congrArg Subtype.val hv, fun hv => Subtype.ext hv⟩

/-- **Step 1–2 along the label-canonical exhaustion**: at an admissible environment the
area-clock transition function is the limit of the labelled level-chain transitions. -/
theorem tendsto_labelPairLaw (e : Env) (he : EnvironmentAreaClockAdmissible e) {n m : ℕ}
    (hn : (e.val.1 n).isSome) (hm : (e.val.1 m).isSome) (t : ℝ≥0) :
    Tendsto (fun k => labelPairLaw (levelIndex e n + k) n e
        {p | ContinuousTimeChain.jumpPath p t = some m}) atTop
      (𝓝 ((areaFamily e).transition ⟨n, hn⟩ t ⟨m, hm⟩)) := by
  haveI := nontrivial_vertex e
  have hrw := isReflectedWalk_areaFamily e he
  have hw : ∀ v : Vertex e.val, 0 < areaRate (decode e) v := areaRate_pos e
  have hR : ∀ v, RightContinuousAtInfty ((areaFamily e).P v) (areaFamily e).X :=
    fun v => (hrw v).2.2.2.1
  obtain ⟨Xn, hXn, happ, hlaw⟩ := exists_approximant hrw (decode_connected e) hw hR
    (labelExhaustion e) ⟨n, hn⟩ fun k =>
      ae_tsum_stepHolding_eq_top hrw (decode_connected e) hw hR (labelExhaustion e) ⟨n, hn⟩
        ((labelExhaustion e).nz ⟨n, hn⟩ + k)
  have h := tendsto_measure_of_approximated hXn (areaFamily e).measurable_X happ t ⟨m, hm⟩
  refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
  rw [hlaw k t ⟨m, hm⟩, ProcessFamily.transition,
    ContinuousTimeChain.chainFamily_transition (labelExhaustion e) (areaRate (decode e))
      (decode_connected e) hw k ⟨n, hn⟩ t ⟨m, hm⟩,
    levelIndex_of_isSome hn]
  exact chainTransition_eq_labelPairLaw e _ hn hm t

/-! ### 4. `hmeas` -/

theorem slotTransition_of_mem {G : Set Env} {n : ℕ} {t : ℝ≥0} {m : ℕ} {e : Env}
    (h : e ∈ G ∧ (e.val.1 n).isSome ∧ (e.val.1 m).isSome) :
    slotTransition G n t m e = (areaFamily e).transition ⟨n, h.2.1⟩ t ⟨m, h.2.2⟩ := by
  unfold slotTransition
  rw [dif_pos h]

/-- **`hmeas` of `RegenerationKernel.rootedKernel`, PROVED**: on any measurable admissible gate
the area-clock transition function `e ↦ P_e^{H_n}(X_t = H_m)` is a measurable function of the
environment. -/
theorem measurable_slotTransition (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (n : ℕ) (t : ℝ≥0) (m : ℕ) :
    Measurable (slotTransition G n t m) := by
  set S : Set Env := G ∩ ({e : Env | (e.val.1 n).isSome} ∩ {e : Env | (e.val.1 m).isSome})
    with hSdef
  have hS : MeasurableSet S := hG.inter
    ((RegenerationKernel.measurableSet_slotPresent n).inter
      (RegenerationKernel.measurableSet_slotPresent m))
  have hEv : MeasurableSet
      {p : (ℕ → ℕ) × (ℕ → ℝ) | ContinuousTimeChain.jumpPath p t = some m} :=
    ContinuousTimeChain.measurable_jumpPath t (measurableSet_singleton _)
  have hF : ∀ k : ℕ, Measurable (S.indicator fun e : Env => labelPairLaw (levelIndex e n + k) n e
      {p | ContinuousTimeChain.jumpPath p t = some m}) :=
    fun k => (measurable_labelPairLaw_levelIndex n k hEv).indicator hS
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun e => ?_)
  by_cases he : e ∈ S
  · simp only [Set.indicator_of_mem he]
    rw [slotTransition_of_mem he]
    exact tendsto_labelPairLaw e (hwalk e he.1) he.2.1 he.2.2 t
  · simp only [Set.indicator_of_notMem he]
    rw [slotTransition_of_not he]
    exact tendsto_const_nhds

/-! ### 5. The regeneration kernel with `hmeas` discharged -/

/-- **The two-sided rooted kernel `κ` of the regeneration lane, with `hmeas` discharged**: its
only inputs are the gate's (`hG`, `hwalk`). -/
noncomputable def regenerationKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) : Kernel Env TwoSidedCoding :=
  rootedKernel G hG hwalk (measurable_slotTransition G hG hwalk)

theorem regenerationKernel_apply (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (e : Env) :
    regenerationKernel G hG hwalk e = rootedLaw G e := rfl

instance regenerationKernel_isMarkovKernel (G : Set Env) (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) :
    IsMarkovKernel (regenerationKernel G hG hwalk) :=
  rootedKernel_isMarkovKernel G hG hwalk (measurable_slotTransition G hG hwalk)

/-! ### 6. By-product: the area-clock law does not depend on the (admissible) exhaustion -/

end ReflectedGMS.RegenerationKernelMeasurability
