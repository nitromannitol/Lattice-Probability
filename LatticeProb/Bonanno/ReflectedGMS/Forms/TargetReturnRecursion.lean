/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetReturnRecursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnKernelLaw

/-!
# Recursive return times to a finite target

The first holding time at each visited target vertex is retained.  A possible
excursion outside the target is deleted: the next clock time is the first
return to the target after exiting the current vertex.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TargetReturnRecursion

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnKernelLaw

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- Successive return times to `A` on the original reflected path. -/
noncomputable def targetReturnTime {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)
  | n + 1 => hitAfter X (some '' (A : Set V)) (exitAfter X (targetReturnTime X A n))

/-- The event that the `n`th return time is finite and is attained in `A`. -/
def targetReturnDefined {Ω : Type u} (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (n : ℕ) : Set Ω :=
  ⋃ x : {x // x ∈ A}, stopEvent X (targetReturnTime X A n) x.1

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Nontrivial V] in
lemma mem_targetReturnDefined_iff {Ω : Type u} {X : ℝ≥0 → Ω → Option V}
    {A : Finset V} {n : ℕ} {ω : Ω} :
    ω ∈ targetReturnDefined X A n ↔
      targetReturnTime X A n ω ≠ ⊤ ∧
        stoppedValue X (targetReturnTime X A n) ω ∈ some '' (A : Set V) := by
  classical
  simp only [targetReturnDefined, Set.mem_iUnion, stopEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hfin, hx⟩
    exact ⟨hfin, x.1, Finset.mem_coe.2 x.2, hx.symm⟩
  · rintro ⟨hfin, x, hx, hval⟩
    exact ⟨⟨x, Finset.mem_coe.1 hx⟩, hfin, hval.symm⟩

private lemma sum_ofReal_inducedTransProb (hG : G.toSimpleGraph.Connected)
    {A : Finset V} (hA : A.Nonempty) (x : V) :
    ∑' y : {y // y ∈ A}, ENNReal.ofReal (G.inducedTransProb hG A x y.1) = 1 := by
  classical
  rw [tsum_fintype]
  have hreal : (∑ y : {y // y ∈ A}, G.inducedTransProb hG A x y.1) = 1 := by
    calc
      (∑ y : {y // y ∈ A}, G.inducedTransProb hG A x y.1) =
          ∑ y ∈ A, G.inducedTransProb hG A x y := Finset.sum_attach A _
      _ = ∑' y : V, G.inducedTransProb hG A x y :=
        (tsum_eq_sum (s := A)
          (fun y hy => G.inducedTransProb_of_not_mem_right hG hy)).symm
      _ = 1 := G.tsum_inducedTransProb hG hA x
  rw [← ENNReal.ofReal_sum_of_nonneg, hreal, ENNReal.ofReal_one]
  intro y hy
  exact G.inducedTransProb_nonneg hG hA x y.1

private lemma ae_mem_of_measure_eq_one {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : Set Ω}
    (hE : NullMeasurableSet E P) (hm : P E = 1) : ∀ᵐ ω ∂P, ω ∈ E := by
  rw [ae_iff]
  have hsum : P E + P Eᶜ = 1 := by
    rw [measure_add_measure_compl₀ hE, measure_univ]
  rw [hm] at hsum
  by_contra hne
  have hlt : (1 : ℝ≥0∞) < 1 + P Eᶜ := ENNReal.lt_add_right (by norm_num) hne
  rw [hsum] at hlt
  exact (lt_irrefl 1 hlt)

/-- Measurability, completed-stopping-time status, and almost-sure target
attainment are propagated together. -/
theorem targetReturnTime_core (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) (n : ℕ) :
    AEMeasurable (targetReturnTime PF.X A n) (PF.P x) ∧
      IsAEStoppingTime PF.naturalFiltration (PF.P x) (targetReturnTime PF.X A n) ∧
      PF.P x (targetReturnDefined PF.X A n) = 1 := by
  classical
  have hii : RightContinuous (PF.P x) PF.X := (h x).2.2.1
  have hR : RightContinuousAtInfty (PF.P x) PF.X := (h x).2.2.2.1
  induction n with
  | zero =>
      refine ⟨aemeasurable_const, isAEStoppingTime_const PF.measurable_X 0, ?_⟩
      have hset : targetReturnDefined PF.X A 0 =ᵐ[PF.P x] (Set.univ : Set PF.Ω) := by
        refine Filter.eventuallyEqSet_iff.2 ?_
        filter_upwards [(h x).1] with ω hzero
        rw [mem_targetReturnDefined_iff]
        exact iff_true_intro ⟨WithTop.coe_ne_top, by
          simpa [targetReturnTime, stoppedValue] using
            (show PF.X 0 ω ∈ some '' (A : Set V) from
              ⟨x, Finset.mem_coe.2 hx, hzero.symm⟩)⟩
      rw [measure_congr hset, measure_univ]
  | succ n ih =>
      rcases ih with ⟨hτm, hτ, hdefined⟩
      have hnull : NullMeasurableSet (targetReturnDefined PF.X A n) (PF.P x) :=
        NullMeasurableSet.iUnion fun y : {y // y ∈ A} =>
          nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm y.1
      have hae : ∀ᵐ ω ∂PF.P x, ω ∈ targetReturnDefined PF.X A n :=
        ae_mem_of_measure_eq_one hnull hdefined
      have hval : ∀ᵐ ω ∂PF.P x,
          ∃ y : V, stoppedValue PF.X (targetReturnTime PF.X A n) ω = some y := by
        filter_upwards [hae] with ω hω
        rw [mem_targetReturnDefined_iff] at hω
        obtain ⟨y, -, hy⟩ := hω.2
        exact ⟨y, hy.symm⟩
      have hρm : AEMeasurable (exitAfter PF.X (targetReturnTime PF.X A n)) (PF.P x) :=
        aemeasurable_exitAfter PF.measurable_X hii hR hτm hval
      have hρ : IsAEStoppingTime PF.naturalFiltration (PF.P x)
          (exitAfter PF.X (targetReturnTime PF.X A n)) :=
        isAEStoppingTime_exitAfter PF.measurable_X hii hR hτ hval
      have hnextm : AEMeasurable (targetReturnTime PF.X A (n + 1)) (PF.P x) := by
        simpa [targetReturnTime] using
          aemeasurable_hitAfter PF.measurable_X hii hR (admissibleTarget_image A) hρm
      have hnext : IsAEStoppingTime PF.naturalFiltration (PF.P x)
          (targetReturnTime PF.X A (n + 1)) := by
        change IsAEStoppingTime (naturalFiltration PF.X PF.measurable_X) (PF.P x)
          (targetReturnTime PF.X A (n + 1))
        simpa only [targetReturnTime] using
          isAEStoppingTime_hitAfter PF.measurable_X hii hR (admissibleTarget_image A) hρ
      refine ⟨hnextm, hnext, ?_⟩
      have hnullNext : NullMeasurableSet (targetReturnDefined PF.X A (n + 1)) (PF.P x) :=
        NullMeasurableSet.iUnion fun y : {y // y ∈ A} =>
          nullMeasurableSet_stopEvent' PF.measurable_X hii hR hnextm y.1
      have hfib (v : {v // v ∈ A}) :
          PF.P x (stopEvent PF.X (targetReturnTime PF.X A n) v.1 ∩
            targetReturnDefined PF.X A (n + 1)) =
          PF.P x (stopEvent PF.X (targetReturnTime PF.X A n) v.1) := by
        rw [targetReturnDefined, Set.inter_iUnion,
          measure_iUnion₀
            (fun y y' hyy' => ((disjoint_stopEvent (fun he => hyy' (Subtype.ext he))).mono
              Set.inter_subset_right Set.inter_subset_right).aedisjoint)
            (fun y => (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm v.1).inter
              (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hnextm y.1))]
        have hstep (y : {y // y ∈ A}) :
            PF.P x (stopEvent PF.X (targetReturnTime PF.X A n) v.1 ∩
              stopEvent PF.X (targetReturnTime PF.X A (n + 1)) y.1) =
            PF.P x (stopEvent PF.X (targetReturnTime PF.X A n) v.1) *
              ENNReal.ofReal (G.inducedTransProb hG A v.1 y.1) := by
          have hm := measure_targetReturn_completed h hG x hτm hτ
            (F := (Set.univ : Set PF.Ω)) (aemeasurableSetStopped_univ hτ)
            hA v.2 y.2 MeasurableSet.univ
          simpa [targetReturnTime, stopEvent, map_toWithTop_expMeasure_univ h v.1] using hm
        simp_rw [hstep]
        rw [ENNReal.tsum_mul_left, sum_ofReal_inducedTransProb hG hA v.1, mul_one]
      have hsplit : targetReturnDefined PF.X A (n + 1) =ᵐ[PF.P x]
          ⋃ v : {v // v ∈ A},
            (stopEvent PF.X (targetReturnTime PF.X A n) v.1 ∩
              targetReturnDefined PF.X A (n + 1)) := by
        refine Filter.eventuallyEqSet_iff.2 ?_
        filter_upwards [hae] with ω hω
        constructor
        · intro hs
          rw [targetReturnDefined, Set.mem_iUnion] at hω
          obtain ⟨v, hv⟩ := hω
          rw [Set.mem_iUnion]
          exact ⟨v, hv, hs⟩
        · rw [Set.mem_iUnion]
          rintro ⟨v, -, hs⟩
          exact hs
      rw [measure_congr hsplit,
        measure_iUnion₀
          (fun v v' hvv' => ((disjoint_stopEvent (fun he => hvv' (Subtype.ext he))).mono
            Set.inter_subset_left Set.inter_subset_left).aedisjoint)
          (fun v => (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm v.1).inter hnullNext)]
      simp_rw [hfib]
      rw [← measure_iUnion₀
        (fun v v' hvv' => (disjoint_stopEvent (fun he => hvv' (Subtype.ext he))).aedisjoint)
        (fun v => nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm v.1)]
      exact hdefined

theorem aemeasurable_targetReturnTime (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) (n : ℕ) :
    AEMeasurable (targetReturnTime PF.X A n) (PF.P x) :=
  (targetReturnTime_core h hG hA hx n).1

theorem isAEStoppingTime_targetReturnTime (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) (n : ℕ) :
    IsAEStoppingTime PF.naturalFiltration (PF.P x) (targetReturnTime PF.X A n) :=
  (targetReturnTime_core h hG hA hx n).2.1

/-- Simultaneously, every recursive return time is finite and is attained in `A`. -/
theorem ae_forall_targetReturnTime_finite_mem (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} (hA : A.Nonempty)
    {x : V} (hx : x ∈ A) :
    ∀ᵐ ω ∂PF.P x, ∀ n : ℕ,
      targetReturnTime PF.X A n ω ≠ ⊤ ∧
        stoppedValue PF.X (targetReturnTime PF.X A n) ω ∈ some '' (A : Set V) := by
  rw [ae_all_iff]
  intro n
  have hτm := aemeasurable_targetReturnTime h hG hA hx n
  have hae := ae_mem_of_measure_eq_one
    (NullMeasurableSet.iUnion fun y : {y // y ∈ A} =>
      nullMeasurableSet_stopEvent' PF.measurable_X (h x).2.2.1 (h x).2.2.2.1 hτm y.1)
    (targetReturnTime_core h hG hA hx n).2.2
  filter_upwards [hae] with ω hω
  exact mem_targetReturnDefined_iff.1 hω

/-- With positive rates, every retained holding duration is strictly positive,
simultaneously for all returns. -/
theorem ae_forall_targetHolding_pos (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (hw : ∀ v, 0 < w v)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A) :
    ∀ᵐ ω ∂PF.P x, ∀ n : ℕ,
      0 < exitAfter PF.X (targetReturnTime PF.X A n) ω -
        targetReturnTime PF.X A n ω := by
  classical
  rw [ae_all_iff]
  intro n
  let τ := targetReturnTime PF.X A n
  let τ' := targetReturnTime PF.X A (n + 1)
  let H : PF.Ω → WithTop ℝ≥0 := fun ω => exitAfter PF.X τ ω - τ ω
  let E : {v // v ∈ A} → {y // y ∈ A} → Set PF.Ω := fun v y =>
    stopEvent PF.X τ v.1 ∩ ({ω | H ω ∈ Set.Iic 0} ∩ stopEvent PF.X τ' y.1)
  have hii : RightContinuous (PF.P x) PF.X := (h x).2.2.1
  have hR : RightContinuousAtInfty (PF.P x) PF.X := (h x).2.2.2.1
  have hτm := aemeasurable_targetReturnTime h hG hA hx n
  have hτ := isAEStoppingTime_targetReturnTime h hG hA hx n
  have hτ'm := aemeasurable_targetReturnTime h hG hA hx (n + 1)
  have hall := ae_forall_targetReturnTime_finite_mem h hG hA hx
  have hcur : ∀ᵐ ω ∂PF.P x,
      targetReturnTime PF.X A n ω ≠ ⊤ ∧
        stoppedValue PF.X (targetReturnTime PF.X A n) ω ∈ some '' (A : Set V) := by
    filter_upwards [hall] with ω hω
    exact hω n
  have hnxt : ∀ᵐ ω ∂PF.P x,
      targetReturnTime PF.X A (n + 1) ω ≠ ⊤ ∧
        stoppedValue PF.X (targetReturnTime PF.X A (n + 1)) ω ∈ some '' (A : Set V) := by
    filter_upwards [hall] with ω hω
    exact hω (n + 1)
  have hval : ∀ᵐ ω ∂PF.P x, ∃ v : V, stoppedValue PF.X τ ω = some v := by
    filter_upwards [hcur] with ω hω
    obtain ⟨v, -, hv⟩ := hω.2
    exact ⟨v, hv.symm⟩
  have hρm : AEMeasurable (exitAfter PF.X τ) (PF.P x) :=
    aemeasurable_exitAfter PF.measurable_X hii hR hτm hval
  have hHm : AEMeasurable H (PF.P x) :=
    measurable_sub_withTop.comp_aemeasurable (hρm.prodMk hτm)
  have hnullE (v : {v // v ∈ A}) (y : {y // y ∈ A}) :
      NullMeasurableSet (E v y) (PF.P x) := by
    change NullMeasurableSet
      (stopEvent PF.X τ v.1 ∩ (H ⁻¹' Set.Iic 0 ∩ stopEvent PF.X τ' y.1)) (PF.P x)
    exact (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτm v.1).inter
      ((nullMeasurableSet_preimage_of_aemeasurable hHm measurableSet_Iic).inter
        (nullMeasurableSet_stopEvent' PF.measurable_X hii hR hτ'm y.1))
  have hmapzero (v : V) :
      ((expMeasure (w v)).map toWithTop) (Set.Iic (0 : WithTop ℝ≥0)) = 0 := by
    rw [Measure.map_apply measurable_toWithTop measurableSet_Iic]
    have hpre : toWithTop ⁻¹' Set.Iic (0 : WithTop ℝ≥0) = Set.Iic (0 : ℝ) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Iic, toWithTop, nonpos_iff_eq_zero]
      norm_cast
      exact Real.toNNReal_eq_zero
    rw [hpre, expMeasure_Iic_zero (hw v)]
  have hmeasureE (v : {v // v ∈ A}) (y : {y // y ∈ A}) :
      PF.P x (E v y) = 0 := by
    have hm := measure_targetReturn_completed h hG x hτm hτ
      (F := (Set.univ : Set PF.Ω)) (aemeasurableSetStopped_univ hτ)
      hA v.2 y.2 (B := Set.Iic (0 : WithTop ℝ≥0)) measurableSet_Iic
    rw [hmapzero v.1] at hm
    simp only [zero_mul, mul_zero] at hm
    calc
      PF.P x (E v y) = PF.P x
          ((Set.univ : Set PF.Ω) ∩ stopEvent PF.X τ v.1 ∩
            {ω | H ω ∈ Set.Iic 0 ∧ τ' ω ≠ ⊤ ∧ stoppedValue PF.X τ' ω = some y.1}) := by
        refine measure_congr (ae_of_all _ fun ω => ?_)
        simp only [E, stopEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ,
          true_and]
      _ = 0 := by simpa only [τ, τ', H, targetReturnTime] using hm
  let U : Set PF.Ω := ⋃ v : {v // v ∈ A}, ⋃ y : {y // y ∈ A}, E v y
  have hmeasureU : PF.P x U = 0 := by
    apply le_zero_iff.mp
    calc
      PF.P x U ≤ ∑' v : {v // v ∈ A}, PF.P x (⋃ y : {y // y ∈ A}, E v y) :=
        by change PF.P x (⋃ v : {v // v ∈ A}, ⋃ y : {y // y ∈ A}, E v y) ≤ _
           exact measure_iUnion_le _
      _ ≤ ∑' v : {v // v ∈ A}, ∑' y : {y // y ∈ A}, PF.P x (E v y) :=
        ENNReal.tsum_le_tsum fun v => measure_iUnion_le _
      _ = 0 := by simp [hmeasureE]
  have hnotU : ∀ᵐ ω ∂PF.P x, ω ∉ U := by
    rw [ae_iff]
    have hset : {ω | ¬ω ∉ U} = U := by ext ω; simp
    rw [hset]
    exact hmeasureU
  filter_upwards [hcur, hnxt, hnotU] with ω hcurω hnxtω hωU
  by_contra hnot
  have hle : H ω ∈ Set.Iic (0 : WithTop ℝ≥0) := by
    exact not_lt.1 hnot
  obtain ⟨v, hvA, hv⟩ := hcurω.2
  obtain ⟨y, hyA, hy⟩ := hnxtω.2
  apply hωU
  refine Set.mem_iUnion.2 ⟨⟨v, Finset.mem_coe.1 hvA⟩,
    Set.mem_iUnion.2 ⟨⟨y, Finset.mem_coe.1 hyA⟩, ?_⟩⟩
  exact ⟨⟨hcurω.1, hv.symm⟩, hle, hnxtω.1, hy.symm⟩

end ReflectedGMS.TargetReturnRecursion
