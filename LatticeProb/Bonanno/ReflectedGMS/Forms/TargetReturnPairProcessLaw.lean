/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetReturnPairProcessLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnRecursion
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide

/-!
# Law of the original-process target-return pair

The recursive return times retain the holding time at each vertex of the
finite target and delete the duration of every excursion outside it.
-/

-- Merged from `ReflectedGMS/Forms/ChainHoldingPrefixLaw.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ChainHoldingPrefixLaw

/-! Reuse the existing prefix rectangles and their generating pi-system to
identify a chain together with its exponential holding times. This factors out
the measure-extensionality part of the original trace-law argument. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [DecidableEq V]

/-- Exact finite-prefix law of a chain and its conditional exponential holds. -/
theorem chainLaw_compProd_holdingKernel_pairRect
    (κ : Kernel V V) [IsMarkovKernel κ] (w : V → ℝ) (hw : ∀ x, 0 < w x)
    (z : V) (m : ℕ) (g : ℕ → V) (B : ℕ → Set ℝ) (hB : ∀ j, MeasurableSet (B j)) :
    (MarkovChain.chainLaw κ z ⊗ₘ holdingKernel w) (pairRect m g B) =
      (if g 0 = z then 1 else 0) *
        ∏ i ∈ Finset.range m, (expMeasure (w (g i)) (B i) * κ (g i) {g (i + 1)}) := by
  classical
  have hA : MeasurableSet {y : ℕ → V | ∀ j ≤ m, y j = g j} :=
    measurableSet_prefixEvent g m
  have hD : MeasurableSet (Set.pi (↑(Finset.range m)) B) :=
    MeasurableSet.pi (Finset.range m).countable_toSet fun j _ => hB j
  have hker : ∀ y ∈ {y : ℕ → V | ∀ j ≤ m, y j = g j},
      holdingKernel w y (Set.pi (↑(Finset.range m)) B) =
        ∏ i ∈ Finset.range m, expMeasure (w (g i)) (B i) := by
    intro y hy
    haveI : ∀ i : ℕ, IsProbabilityMeasure (expMeasure (w (y i))) :=
      fun i => isProbabilityMeasure_expMeasure (hw (y i))
    rw [holdingKernel_apply hw y, Measure.infinitePi_pi _ fun j _ => hB j]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hy i (le_of_lt (Finset.mem_range.1 hi))]
  rw [pairRect, Measure.compProd_apply_prod hA hD]
  rw [lintegral_congr_ae ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall hker)),
    setLIntegral_const, chainLaw_prefixEvent κ m z g, Finset.prod_mul_distrib]
  ring

/-- The existing prefix rectangles determine the full joint law. -/
theorem measure_eq_chainLaw_compProd_of_pairRect
    (μ : Measure ((ℕ → V) × (ℕ → ℝ))) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (κ : Kernel V V) [IsMarkovKernel κ] (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V)
    (hrect : ∀ (m : ℕ) (g : ℕ → V) (B : ℕ → Set ℝ), (∀ j, MeasurableSet (B j)) →
      μ (pairRect m g B) = (if g 0 = z then 1 else 0) *
        ∏ i ∈ Finset.range m, (expMeasure (w (g i)) (B i) * κ (g i) {g (i + 1)})) :
    μ = MarkovChain.chainLaw κ z ⊗ₘ holdingKernel w := by
  classical
  refine MeasureTheory.ext_of_generate_finite (pairRects V)
    (generateFrom_pairRects z).symm isPiSystem_pairRects ?_ ?_
  · rintro C ⟨m, g, B, hB, rfl⟩
    rw [hrect m g B hB, chainLaw_compProd_holdingKernel_pairRect κ w hw z m g B hB]
  · simp [hμ]

/-- Only the initial prefix and the one-step prefix multiplication rule remain
to be shown for a concrete stopped trace process. -/
theorem measure_eq_chainLaw_compProd_of_prefix_recursion
    (μ : Measure ((ℕ → V) × (ℕ → ℝ))) [IsFiniteMeasure μ] (hμ : μ univ = 1)
    (κ : Kernel V V) [IsMarkovKernel κ] (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V)
    (hzero : ∀ (g : ℕ → V) (B : ℕ → Set ℝ), (∀ j, MeasurableSet (B j)) →
      μ (pairRect 0 g B) = if g 0 = z then 1 else 0)
    (hstep : ∀ (m : ℕ) (g : ℕ → V) (B : ℕ → Set ℝ), (∀ j, MeasurableSet (B j)) →
      μ (pairRect (m + 1) g B) = μ (pairRect m g B) *
        (expMeasure (w (g m)) (B m) * κ (g m) {g (m + 1)})) :
    μ = MarkovChain.chainLaw κ z ⊗ₘ holdingKernel w := by
  apply measure_eq_chainLaw_compProd_of_pairRect μ hμ κ w hw z
  intro m g B hB
  induction m with
  | zero => simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using hzero g B hB
  | succ m ih => rw [hstep m g B hB, ih, Finset.prod_range_succ, mul_assoc]

end ReflectedGMS

end Merged_ChainHoldingPrefixLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TargetReturnPairProcessLaw

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnKernelLaw TargetReturnRecursion

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- The successive vertices of the original path on returning to `A`. -/
noncomputable def targetReturnVertexSeq {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (default : V) (ω : Ω) (n : ℕ) : V :=
  (stoppedValue X (targetReturnTime X A n) ω).getD default

/-- The holding times retained by the target trace, represented on `ℝ`. -/
noncomputable def targetReturnHolding {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  exitAfter X (targetReturnTime X A n) ω - targetReturnTime X A n ω

/-- The holding times retained by the target trace, represented on `ℝ`. -/
noncomputable def targetReturnHoldingSeq {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (ω : Ω) (n : ℕ) : ℝ :=
  ENNReal.toReal (targetReturnHolding X A n ω)

/-- The whole vertex/holding pair extracted directly from the original path. -/
noncomputable def targetReturnPair {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (default : V) (ω : Ω) : (ℕ → V) × (ℕ → ℝ) :=
  (targetReturnVertexSeq X A default ω, targetReturnHoldingSeq X A ω)

private def targetPairCylEvent {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (g : ℕ → V) (B : ℕ → Set ℝ) : ℕ → Set Ω
  | 0 => stopEvent X (targetReturnTime X A 0) (g 0)
  | m + 1 => targetPairCylEvent X A g B m ∩
      ({ω | ENNReal.toReal (targetReturnHolding X A m ω) ∈ B m} ∩
        stopEvent X (targetReturnTime X A (m + 1)) (g (m + 1)))

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [Nontrivial V] in
lemma targetReturnTime_le_succ {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (m : ℕ) (ω : Ω) :
    targetReturnTime X A m ω ≤ targetReturnTime X A (m + 1) ω := by
  exact (le_hitAfter ω).trans (le_hitAfter ω)

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [Nontrivial V] in
lemma exitAfter_targetReturnTime_le_succ {Ω : Type u}
    (X : ℝ≥0 → Ω → Option V) (A : Finset V) (m : ℕ) (ω : Ω) :
    exitAfter X (targetReturnTime X A m) ω ≤ targetReturnTime X A (m + 1) ω := by
  exact le_hitAfter ω

private lemma targetPairCylEvent_subset (X : ℝ≥0 → PF.Ω → Option V)
    (A : Finset V) (g : ℕ → V) (B : ℕ → Set ℝ) (m : ℕ) :
    targetPairCylEvent X A g B m ⊆
      stopEvent X (targetReturnTime X A m) (g m) := by
  cases m with
  | zero => exact subset_rfl
  | succ m => exact Set.inter_subset_right.trans Set.inter_subset_right

private lemma aemeasurableSetStopped_targetPairCylEvent
    (h : IsReflectedWalk G w hmin PF) (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A)
    (g : ℕ → V) {B : ℕ → Set ℝ} (hB : ∀ k, MeasurableSet (B k)) (m : ℕ) :
    AEMeasurableSetStopped PF.naturalFiltration (PF.P x)
      (targetReturnTime PF.X A m) (targetPairCylEvent PF.X A g B m) := by
  have hii := (h x).2.2.1
  have hR := (h x).2.2.2.1
  have hτ (j : ℕ) := isAEStoppingTime_targetReturnTime h hG hA hx j
  have hτm (j : ℕ) := aemeasurable_targetReturnTime h hG hA hx j
  have hval (j : ℕ) : ∀ᵐ ω ∂PF.P x,
      ∃ v : V, stoppedValue PF.X (targetReturnTime PF.X A j) ω = some v := by
    filter_upwards [ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hω
    obtain ⟨v, -, hv⟩ := (hω j).2
    exact ⟨v, hv.symm⟩
  induction m with
  | zero =>
      exact aemeasurableSetStopped_stopEvent PF.measurable_X hii hR (hτ 0) (g 0)
  | succ m ih =>
      have hhold : AEStoppedTime PF.naturalFiltration (PF.P x)
          (targetReturnTime PF.X A (m + 1))
          (targetReturnHolding PF.X A m) := by
        change AEStoppedTime PF.naturalFiltration (PF.P x)
          (targetReturnTime PF.X A (m + 1))
          (fun ω => exitAfter PF.X (targetReturnTime PF.X A m) ω -
            targetReturnTime PF.X A m ω)
        have he : AEStoppedTime PF.naturalFiltration (PF.P x)
            (targetReturnTime PF.X A (m + 1))
            (exitAfter PF.X (targetReturnTime PF.X A m)) :=
          AEStoppedTime.of_le
            (isAEStoppingTime_exitAfter PF.measurable_X hii hR (hτ m) (hval m))
            (exitAfter_targetReturnTime_le_succ PF.X A m)
        have ht : AEStoppedTime PF.naturalFiltration (PF.P x)
            (targetReturnTime PF.X A (m + 1))
            (targetReturnTime PF.X A m) :=
          AEStoppedTime.of_le (hτ m) (targetReturnTime_le_succ PF.X A m)
        exact he.comp₂ ht measurable_sub_withTop
      refine AEMeasurableSetStopped.inter
        (ih.mono (hτ (m + 1)) (targetReturnTime_le_succ PF.X A m))
        (AEMeasurableSetStopped.inter ?_
          (aemeasurableSetStopped_stopEvent PF.measurable_X hii hR
            (hτ (m + 1)) (g (m + 1))))
      change AEMeasurableSetStopped PF.naturalFiltration (PF.P x)
        (targetReturnTime PF.X A (m + 1))
        {ω | targetReturnHolding PF.X A m ω ∈ ENNReal.toReal ⁻¹' B m}
      exact hhold.preimage (hτ (m + 1)) (ENNReal.measurable_toReal (hB m))

private lemma mem_targetPairCylEvent_iff {Ω : Type u}
    (X : ℝ≥0 → Ω → Option V) (A : Finset V) (g : ℕ → V)
    (B : ℕ → Set ℝ) (m : ℕ) (ω : Ω) :
    ω ∈ targetPairCylEvent X A g B m ↔
      ((∀ i ≤ m, ω ∈ stopEvent X (targetReturnTime X A i) (g i)) ∧
        ∀ i < m, targetReturnHoldingSeq X A ω i ∈ B i) := by
  induction m with
  | zero =>
      constructor
      · intro hω
        exact ⟨fun i hi => Nat.le_zero.1 hi ▸ hω,
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · intro hω
        exact hω.1 0 le_rfl
  | succ m ih =>
      rw [targetPairCylEvent, Set.mem_inter_iff, Set.mem_inter_iff, ih]
      constructor
      · rintro ⟨⟨hpos, hhold⟩, hm, hnext⟩
        exact ⟨fun i hi => by
          rcases Nat.lt_or_eq_of_le hi with hi | rfl
          · exact hpos i (Nat.le_of_lt_succ hi)
          · exact hnext,
          fun i hi => by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with him | rfl
            · exact hhold i him
            · exact hm⟩
      · rintro ⟨hpos, hhold⟩
        exact ⟨⟨fun i hi => hpos i (hi.trans (Nat.le_succ m)),
          fun i hi => hhold i (hi.trans_le (Nat.le_succ m))⟩,
          hhold m (Nat.lt_succ_self m), hpos (m + 1) le_rfl⟩

theorem aemeasurable_targetReturnPair (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) :
    AEMeasurable (targetReturnPair PF.X A x) (PF.P x) := by
  have hii := (h x).2.2.1
  have hR := (h x).2.2.2.1
  have hall := ae_forall_targetReturnTime_finite_mem h hG hA hx
  have hZ (j : ℕ) : AEMeasurable (targetReturnVertexSeq PF.X A x · j) (PF.P x) := by
    exact (measurable_of_countable (fun o : Option V => o.getD x)).comp_aemeasurable
      (aemeasurable_stoppedValue PF.measurable_X hii hR
        (aemeasurable_targetReturnTime h hG hA hx j))
  have hT (j : ℕ) : AEMeasurable (targetReturnHoldingSeq PF.X A · j) (PF.P x) := by
    have hval : ∀ᵐ ω ∂PF.P x,
        ∃ v : V, stoppedValue PF.X (targetReturnTime PF.X A j) ω = some v := by
      filter_upwards [hall] with ω hω
      obtain ⟨v, -, hv⟩ := (hω j).2
      exact ⟨v, hv.symm⟩
    have he := aemeasurable_exitAfter PF.measurable_X hii hR
      (aemeasurable_targetReturnTime h hG hA hx j) hval
    change AEMeasurable (fun ω => ENNReal.toReal
      (exitAfter PF.X (targetReturnTime PF.X A j) ω - targetReturnTime PF.X A j ω)) (PF.P x)
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (measurable_sub_withTop.comp_aemeasurable
        (he.prodMk (aemeasurable_targetReturnTime h hG hA hx j)))
  refine ⟨fun ω => (fun j => (hZ j).mk _ ω, fun j => (hT j).mk _ ω),
    (Measurable.of_eval fun j => (hZ j).measurable_mk).prodMk
      (Measurable.of_eval fun j => (hT j).measurable_mk), ?_⟩
  filter_upwards [ae_all_iff.2 fun j => (hZ j).ae_eq_mk,
    ae_all_iff.2 fun j => (hT j).ae_eq_mk] with ω hZω hTω
  show (targetReturnVertexSeq PF.X A x ω, targetReturnHoldingSeq PF.X A ω) = _
  rw [Prod.mk.injEq]
  exact ⟨funext fun j => hZω j, funext fun j => hTω j⟩

/-- The actual original-process trace on `A`, with only its target holding
times retained, has the induced-chain/exponential-holding joint law. -/
theorem map_targetReturnPair (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A) :
    (PF.P x).map (targetReturnPair PF.X A x) =
      MarkovChain.chainLaw (G.inducedKernel hG hA) x ⊗ₘ holdingKernel w := by
  classical
  let μ := (PF.P x).map (targetReturnPair PF.X A x)
  have hpairm := aemeasurable_targetReturnPair h hG hA hx
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [Measure.map_apply_of_aemeasurable hpairm MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top _ _
  apply ReflectedGMS.measure_eq_chainLaw_compProd_of_prefix_recursion
      μ (by simp [μ, Measure.map_apply_of_aemeasurable hpairm])
      (G.inducedKernel hG hA) w hw x
  · intro g B hB
    rw [Measure.map_apply_of_aemeasurable hpairm (measurableSet_pairRect 0 g hB)]
    have hset : targetReturnPair PF.X A x ⁻¹' pairRect 0 g B =ᵐ[PF.P x]
        targetPairCylEvent PF.X A g B 0 := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [ae_forall_targetReturnTime_finite_mem h hG hA hx] with ω hall
      rw [mem_targetPairCylEvent_iff]
      simp only [Set.mem_preimage, pairRect, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_pi, Finset.coe_range, Set.mem_Iio, targetReturnPair,
        targetReturnVertexSeq, targetReturnHoldingSeq]
      constructor
      · rintro ⟨hpos, -⟩
        obtain ⟨v, -, hv⟩ := (hall 0).2
        have hgv : v = g 0 := by
          have hgi := hpos 0 le_rfl
          rw [← hv] at hgi
          simp only [Option.getD_some] at hgi
          exact hgi
        exact ⟨fun i hi => by
          rw [Nat.le_zero.1 hi]
          exact ⟨(hall 0).1, by rw [← hv, hgv]⟩,
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      · rintro ⟨hpos, -⟩
        exact ⟨fun i hi => by
          obtain ⟨v, -, hv⟩ := (hall i).2
          have hstop := hpos i hi
          rw [← hv]
          exact Option.some_inj.1 (hv.trans hstop.2),
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    rw [measure_congr hset]
    by_cases hgx : g 0 = x
    · rw [ite_eq_left hgx]
      calc
        PF.P x (targetPairCylEvent PF.X A g B 0) = PF.P x Set.univ := by
          apply measure_congr
          refine Filter.eventuallyEqSet_iff.2 ?_
          filter_upwards [(h x).1] with ω hzero
          simp [targetPairCylEvent, targetReturnTime, stopEvent, hgx, stoppedValue, hzero]
        _ = 1 := measure_univ
    · rw [ite_eq_right hgx]
      calc
        PF.P x (targetPairCylEvent PF.X A g B 0) = PF.P x ∅ := by
          apply measure_congr
          refine Filter.eventuallyEqSet_iff.2 ?_
          filter_upwards [(h x).1] with ω hzero
          simp only [targetPairCylEvent, targetReturnTime, stopEvent, Set.mem_empty_iff_false,
            iff_false]
          rintro ⟨-, hval⟩
          exact hgx (Option.some_inj.1 (hzero.symm.trans hval)).symm
        _ = 0 := measure_empty
  · intro m g B hB
    rw [Measure.map_apply_of_aemeasurable hpairm (measurableSet_pairRect (m + 1) g hB),
      Measure.map_apply_of_aemeasurable hpairm (measurableSet_pairRect m g hB)]
    have hall := ae_forall_targetReturnTime_finite_mem h hG hA hx
    have hset (j : ℕ) : targetReturnPair PF.X A x ⁻¹' pairRect j g B =ᵐ[PF.P x]
        targetPairCylEvent PF.X A g B j := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hall] with ω hallω
      rw [mem_targetPairCylEvent_iff]
      simp only [Set.mem_preimage, pairRect, Set.mem_prod, Set.mem_ofPred_eq,
        Set.mem_pi, Finset.coe_range, Set.mem_Iio, targetReturnPair,
        targetReturnVertexSeq, targetReturnHoldingSeq]
      constructor
      · rintro ⟨hpos, hhold⟩
        exact ⟨fun i hi => by
          obtain ⟨v, -, hv⟩ := (hallω i).2
          have hfin := (hallω i).1
          refine ⟨hfin, ?_⟩
          have hgi := hpos i hi
          rw [← hv] at hgi
          simp only [Option.getD_some] at hgi
          exact hv.symm.trans (congrArg some hgi),
          hhold⟩
      · rintro ⟨hpos, hhold⟩
        refine ⟨fun i hi => ?_, hhold⟩
        obtain ⟨v, -, hv⟩ := (hallω i).2
        rw [← hv]
        simp only [Option.getD_some]
        exact Option.some_inj.1 (hv.trans (hpos i hi).2)
    rw [measure_congr (hset (m + 1)), measure_congr (hset m)]
    have hsub : targetPairCylEvent PF.X A g B m ∩
        stopEvent PF.X (targetReturnTime PF.X A m) (g m) =
        targetPairCylEvent PF.X A g B m :=
      Set.inter_eq_left.2 (targetPairCylEvent_subset PF.X A g B m)
    have zero_of_not_mem (j : ℕ) (hj : g j ∉ A) :
        PF.P x (targetPairCylEvent PF.X A g B j) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hall] with ω hω hmem
      obtain ⟨v, hvA, hv⟩ := (hω j).2
      have hgv := Option.some_inj.1 (hv.trans
        ((targetPairCylEvent_subset PF.X A g B j hmem).2))
      exact hj (hgv ▸ Finset.mem_coe.1 hvA)
    by_cases hgm : g m ∈ A
    · by_cases hgn : g (m + 1) ∈ A
      · have hm := measure_targetReturn_completed h hG x
          (aemeasurable_targetReturnTime h hG hA hx m)
          (isAEStoppingTime_targetReturnTime h hG hA hx m)
          (aemeasurableSetStopped_targetPairCylEvent h hG hA hx g hB m)
          hA hgm hgn (ENNReal.measurable_toReal (hB m))
        rw [hsub] at hm
        calc
          PF.P x (targetPairCylEvent PF.X A g B (m + 1)) =
              PF.P x (targetPairCylEvent PF.X A g B m ∩
                {ω | exitAfter PF.X (targetReturnTime PF.X A m) ω -
                    targetReturnTime PF.X A m ω ∈ ENNReal.toReal ⁻¹' B m ∧
                  targetReturnTime PF.X A (m + 1) ω ≠ ⊤ ∧
                  stoppedValue PF.X (targetReturnTime PF.X A (m + 1)) ω =
                    some (g (m + 1))}) := by
                rfl
          _ = PF.P x (targetPairCylEvent PF.X A g B m) *
                (((expMeasure (w (g m))).map toWithTop) (ENNReal.toReal ⁻¹' B m) *
                  ENNReal.ofReal (G.inducedTransProb hG A (g m) (g (m + 1)))) := hm
          _ = PF.P x (targetPairCylEvent PF.X A g B m) *
                (expMeasure (w (g m)) (B m) *
                  G.inducedKernel hG hA (g m) {g (m + 1)}) := by
              rw [ReflectedWalk.Theorem16.map_toWithTop_expMeasure_toReal_preimage
                (hw (g m)) (hB m), G.inducedKernel_singleton hG hA]
      · rw [zero_of_not_mem (m + 1) hgn]
        rw [G.inducedKernel_singleton hG hA]
        rw [G.inducedTransProb_of_not_mem_right hG hgn]
        simp
    · rw [zero_of_not_mem m hgm]
      have hznext : PF.P x (targetPairCylEvent PF.X A g B (m + 1)) = 0 :=
        measure_mono_null Set.inter_subset_left (zero_of_not_mem m hgm)
      rw [hznext]
      simp

end ReflectedGMS.TargetReturnPairProcessLaw
