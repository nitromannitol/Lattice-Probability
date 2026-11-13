/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetReturnKernelLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnConditional

/-!
# The induced target-return kernel after a completed stopping time

The first holding time at the stopped target vertex is retained, while the
duration of a possible excursion outside the finite target is deleted.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TargetReturnKernelLaw

open ReflectedWalk ReflectedWalk.Theorem16
open TargetReturnConditional

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

private lemma nullMeasurableSet_inter_stopEvent_of_stopped
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (hii : RightContinuous P X) (hR : RightContinuousAtInfty P X)
    {σ : Ω → WithTop ℝ≥0} (hσm : AEMeasurable σ P)
    (hσ : IsAEStoppingTime (naturalFiltration X hX) P σ)
    {K : Set Ω} (hK : AEMeasurableSetStopped (naturalFiltration X hX) P σ K)
    (v : V) : NullMeasurableSet (K ∩ stopEvent X σ v) P := by
  choose H hHm hHe using hK
  have hstop : NullMeasurableSet (stopEvent X σ v) P :=
    nullMeasurableSet_stopEvent' hX hii hR hσm v
  rw [show K ∩ stopEvent X σ v =
      ⋃ n : ℕ, (K ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) ∩
        stopEvent X σ v by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq, stopEvent]
    constructor
    · rintro ⟨hKω, hfin, hv⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hfin
      obtain ⟨n, hn⟩ := exists_nat_ge a
      exact ⟨n, ⟨hKω, by rw [← ha]; exact WithTop.coe_le_coe.2 hn⟩, hfin, hv⟩
    · rintro ⟨n, ⟨hKω, -⟩, hfin, hv⟩
      exact ⟨hKω, hfin, hv⟩]
  refine NullMeasurableSet.iUnion fun n => ?_
  have hn : NullMeasurableSet
      (K ∩ {ω | σ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) P :=
    (pastSigma_le hX _ _ (hHm n)).nullMeasurableSet.congr (hHe n).symm
  exact hn.inter hstop

/-- The conditional joint law of the holding time at `x` and the next vertex
of the trace on `A`, after an arbitrary completed stopping time. -/
theorem measure_targetReturn_completed (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (z : V)
    {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
    (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)
    {F : Set PF.Ω} (hF : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) τ F)
    {A : Finset V} (hA : A.Nonempty) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    {B : Set (WithTop ℝ≥0)} (hB : MeasurableSet B) :
    PF.P z (F ∩ stopEvent PF.X τ x ∩
        {ω | exitAfter PF.X τ ω - τ ω ∈ B ∧
          hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ) ω ≠ ⊤ ∧
          stoppedValue PF.X
            (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω = some y}) =
      PF.P z (F ∩ stopEvent PF.X τ x) *
        (((expMeasure (w x)).map toWithTop) B *
          ENNReal.ofReal (G.inducedTransProb hG A x y)) := by
  classical
  let ρ := hitAfter PF.X {s : Option V | s ≠ some x} τ
  let D : Set PF.Ω := F ∩ stopEvent PF.X τ x ∩
    ({ω | ρ ω - τ ω ∈ B} ∩ stopEvent PF.X ρ y)
  let E : V → Set PF.Ω := fun v => if v ∈ A then ∅ else
    (F ∩ stopEvent PF.X τ x ∩
      ({ω | ρ ω - τ ω ∈ B} ∩ stopEvent PF.X ρ v)) ∩
        futureAt PF.X ρ ⁻¹' hitEvent A y
  have hRz : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  have hii : RightContinuous (PF.P z) PF.X := (h z).2.2.1
  have hρm : AEMeasurable ρ (PF.P z) :=
    aemeasurable_hitAfter PF.measurable_X hii hRz (admissibleTarget_ne x) hτm
  have hρ : IsAEStoppingTime PF.naturalFiltration (PF.P z) ρ :=
    isAEStoppingTime_hitAfter PF.measurable_X hii hRz (admissibleTarget_ne x) hτ
  have hfutm : AEMeasurable (futureAt PF.X ρ) (PF.P z) :=
    (aemeasurable_futureAt PF.measurable_X hii hRz hρm.measurable_mk).congr (by
      filter_upwards [hρm.ae_eq_mk] with ω hω
      funext s
      simp only [futureAt, hω])
  have hD : NullMeasurableSet D (PF.P z) := by
    simpa [D, ρ, inter_assoc, inter_self] using
      (nullMeasurableSet_inter_stopEvent_of_stopped PF.measurable_X hii hRz hρm hρ
        (aemeasurableSetStopped_exitPair_history h z hτ hF hB y) y)
  have hE (v : V) : NullMeasurableSet (E v) (PF.P z) := by
    by_cases hv : v ∈ A
    · simp [E, hv]
    · simp only [E, if_neg hv]
      simpa [ρ, inter_assoc, inter_self] using
        ((nullMeasurableSet_inter_stopEvent_of_stopped PF.measurable_X hii hRz hρm hρ
          (aemeasurableSetStopped_exitPair_history h z hτ hF hB v) v).inter
            (nullMeasurableSet_preimage_of_aemeasurable hfutm (measurableSet_hitEvent A y)))
  have hEE : ∀ ⦃v v' : V⦄, v ≠ v' → AEDisjoint (PF.P z) (E v) (E v') := by
    intro v v' hvv'
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.2
    intro ω hv hv'
    by_cases hvA : v ∈ A
    · simpa [E, hvA] using hv
    by_cases hv'A : v' ∈ A
    · simpa [E, hv'A] using hv'
    simp only [E, if_neg hvA] at hv
    simp only [E, if_neg hv'A] at hv'
    exact hvv' (Option.some_inj.1 (hv.1.2.2.2.symm.trans hv'.1.2.2.2))
  have hDE (v : V) : Disjoint D (E v) := by
    apply Set.disjoint_left.2
    intro ω hd he
    by_cases hvA : v ∈ A
    · simpa [E, hvA] using he
    simp only [E, if_neg hvA] at he
    have hyv : stoppedValue PF.X ρ ω = some y := hd.2.2.2
    have hvv : stoppedValue PF.X ρ ω = some v := he.1.2.2.2
    exact hvA (Option.some_inj.1 (hvv.symm.trans hyv) ▸ hy)
  have hDN : AEDisjoint (PF.P z) D (⋃ v, E v) := by
    exact (Set.disjoint_iUnion_right.2 hDE).aedisjoint
  have hN : NullMeasurableSet (⋃ v, E v) (PF.P z) := NullMeasurableSet.iUnion hE
  have hmeasureN : PF.P z (⋃ v, E v) = ∑' v, PF.P z (E v) :=
    measure_iUnion₀ hEE hE
  have hmeasureD : PF.P z D = PF.P z (F ∩ stopEvent PF.X τ x) *
      (((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x y / G.pi x)) := by
    simpa [D, ρ] using measure_exitPair_completed h hG z hτm hτ hF hA hx hB y
  have hmeasureE (v : V) : PF.P z (E v) = if v ∈ A then 0 else
      PF.P z (F ∩ stopEvent PF.X τ x) *
        ((((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x v / G.pi x)) *
          ENNReal.ofReal (G.harmonicMeasure hG A v y)) := by
    by_cases hv : v ∈ A
    · simp [E, hv]
    · simpa [E, hv, ρ] using
        measure_exitPair_then_hit_completed h hG z hτm hτ hF hA hx hB v y
  let K : Set PF.Ω := F ∩ stopEvent PF.X τ x
  let J : V → Set PF.Ω := fun v => K ∩
    ({ω | ρ ω - τ ω ∈ (Set.univ : Set (WithTop ℝ≥0))} ∩ stopEvent PF.X ρ v)
  have hKnull : NullMeasurableSet K (PF.P z) := by
    simpa [K, inter_assoc, inter_self] using
      (nullMeasurableSet_inter_stopEvent_of_stopped PF.measurable_X hii hRz hτm hτ hF x)
  have hJ (v : V) : NullMeasurableSet (J v) (PF.P z) := by
    simpa [J, K, ρ, inter_assoc, inter_self] using
      (nullMeasurableSet_inter_stopEvent_of_stopped PF.measurable_X hii hRz hρm hρ
        (aemeasurableSetStopped_exitPair_history h z hτ hF MeasurableSet.univ v) v)
  have hJJ : ∀ ⦃v v' : V⦄, v ≠ v' → AEDisjoint (PF.P z) (J v) (J v') := by
    intro v v' hvv'
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.2
    intro ω hv hv'
    exact hvv' (Option.some_inj.1 (hv.2.2.2.symm.trans hv'.2.2.2))
  have hmeasureJ (v : V) : PF.P z (J v) =
      PF.P z K * ENNReal.ofReal (G.c x v / G.pi x) := by
    have hm := measure_exitPair_completed h hG z hτm hτ hF hA hx MeasurableSet.univ v
    rw [map_toWithTop_expMeasure_univ h x, one_mul] at hm
    simpa [J, K, ρ] using hm
  have hmeasureJU : PF.P z (⋃ v, J v) = PF.P z K := by
    rw [measure_iUnion₀ hJJ hJ]
    simp_rw [hmeasureJ]
    rw [ENNReal.tsum_mul_left, tsum_ofReal_step hG x, mul_one]
  have hJUsub : (⋃ v, J v) ⊆ K := by
    intro ω hω
    obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hω
    exact hv.1
  have hKU : K =ᵐ[PF.P z] ⋃ v, J v :=
    (ae_eq_of_subset_of_measure_ge hJUsub hmeasureJU.ge
      (NullMeasurableSet.iUnion hJ) (measure_ne_top _ _)).symm
  have hdec :
      F ∩ stopEvent PF.X τ x ∩
          {ω | exitAfter PF.X τ ω - τ ω ∈ B ∧
            hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ) ω ≠ ⊤ ∧
            stoppedValue PF.X
              (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω = some y} =ᵐ[PF.P z]
        D ∪ ⋃ v, E v := by
    filter_upwards [hKU, ae_rightRegularAt hii hRz] with ω hKUω hreg
    apply propext
    have exit_eq (hstop : ω ∈ stopEvent PF.X τ x) : exitAfter PF.X τ ω = ρ ω := by
      rw [exitAfter, hstop.2]
    constructor
    · rintro ⟨hKω, hhold, hTfin, hret⟩
      have hKω' : ω ∈ K := hKω
      rw [hKUω] at hKω'
      obtain ⟨v, hv⟩ := Set.mem_iUnion.1 hKω'
      have hvstop : ω ∈ stopEvent PF.X ρ v := hv.2.2
      have hexit := exit_eq hKω.2
      have hstart : hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ) ω =
          hitAfter PF.X (some '' (A : Set V)) ρ ω := by
        unfold hitAfter
        rw [hexit]
      have hvaleq : stoppedValue PF.X
          (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω =
          stoppedValue PF.X (hitAfter PF.X (some '' (A : Set V)) ρ) ω := by
        simp only [stoppedValue, hstart]
      have hret' : stoppedValue PF.X
          (hitAfter PF.X (some '' (A : Set V)) ρ) ω = some y := hvaleq.symm.trans hret
      have hhold' : ρ ω - τ ω ∈ B := by rwa [← hexit]
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hvstop.1
      by_cases hvA : v ∈ A
      · have hXa : PF.X a ω = some v :=
          (stoppedValue_of_eq (X := PF.X) ha.symm).symm.trans hvstop.2
        have htime : hitAfter PF.X (some '' (A : Set V)) ρ ω = ρ ω := by
          rw [hitAfter_coe ha.symm]
          rw [← ha]
          apply le_antisymm
          · exact hittingAfter_le_of_mem le_rfl
              (show PF.X a ω ∈ some '' (A : Set V) from
                ⟨v, Finset.mem_coe.2 hvA, hXa.symm⟩)
          · exact le_hittingAfter ω
        have hvy : v = y := by
          apply Option.some_inj.1
          calc
            some v = stoppedValue PF.X ρ ω := hvstop.2.symm
            _ = stoppedValue PF.X (hitAfter PF.X (some '' (A : Set V)) ρ) ω := by
                  simp only [stoppedValue, htime]
            _ = some y := hret'
        subst v
        left
        exact ⟨hKω, hhold', hvstop⟩
      · right
        refine Set.mem_iUnion.2 ⟨v, ?_⟩
        simp only [E, if_neg hvA]
        refine ⟨⟨hKω, hhold', hvstop⟩, ?_⟩
        have hTne : hitAfter PF.X (some '' (A : Set V)) ρ ω ≠ ⊤ := by
          rwa [← hstart]
        have hiff := mem_hitEvent_futureAt_iff hreg A y ha.symm
        apply hiff.2
        have hrhohit : hitAfter PF.X (some '' (A : Set V)) ρ ω =
            hittingAfter PF.X (some '' (A : Set V)) a ω := hitAfter_coe ha.symm
        have hstopval : stoppedValue PF.X
            (hittingAfter PF.X (some '' (A : Set V)) a) ω = some y := by
          have heq : stoppedValue PF.X (hitAfter PF.X (some '' (A : Set V)) ρ) ω =
              stoppedValue PF.X (hittingAfter PF.X (some '' (A : Set V)) a) ω := by
            simp only [stoppedValue, hrhohit]
          exact heq.symm.trans hret'
        exact ⟨by simpa [hrhohit] using hTne, hstopval⟩
    · rintro (hd | he)
      · have hstop : ω ∈ stopEvent PF.X τ x := hd.1.2
        have hexit := exit_eq hstop
        have hystop : ω ∈ stopEvent PF.X ρ y := hd.2.2
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hystop.1
        have hXa : PF.X a ω = some y :=
          (stoppedValue_of_eq (X := PF.X) ha.symm).symm.trans hystop.2
        have htime : hitAfter PF.X (some '' (A : Set V)) ρ ω = ρ ω := by
          rw [hitAfter_coe ha.symm]
          rw [← ha]
          apply le_antisymm
          · exact hittingAfter_le_of_mem le_rfl
              (show PF.X a ω ∈ some '' (A : Set V) from
                ⟨y, Finset.mem_coe.2 hy, hXa.symm⟩)
          · exact le_hittingAfter ω
        have hstart : hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ) ω =
            hitAfter PF.X (some '' (A : Set V)) ρ ω := by
          unfold hitAfter
          rw [hexit]
        have hval : stoppedValue PF.X
            (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω = some y := by
          have heq : stoppedValue PF.X
              (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω =
              stoppedValue PF.X ρ ω := by simp only [stoppedValue, hstart, htime]
          exact heq.trans hystop.2
        exact ⟨hd.1, hexit ▸ hd.2.1, by simpa [hstart, htime] using hystop.1, hval⟩
      · obtain ⟨v, hev⟩ := Set.mem_iUnion.1 he
        by_cases hvA : v ∈ A
        · simpa [E, hvA] using hev
        simp only [E, if_neg hvA] at hev
        have hstop : ω ∈ stopEvent PF.X τ x := hev.1.1.2
        have hexit := exit_eq hstop
        have hvstop : ω ∈ stopEvent PF.X ρ v := hev.1.2.2
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hvstop.1
        have hiff := mem_hitEvent_futureAt_iff hreg A y ha.symm
        have hh := hiff.1 hev.2
        have hrhohit : hitAfter PF.X (some '' (A : Set V)) ρ ω =
            hittingAfter PF.X (some '' (A : Set V)) a ω := hitAfter_coe ha.symm
        have hstart : hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ) ω =
            hitAfter PF.X (some '' (A : Set V)) ρ ω := by
          unfold hitAfter
          rw [hexit]
        have hval : stoppedValue PF.X
            (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω = some y := by
          have heq : stoppedValue PF.X
              (hitAfter PF.X (some '' (A : Set V)) (exitAfter PF.X τ)) ω =
              stoppedValue PF.X (hittingAfter PF.X (some '' (A : Set V)) a) ω := by
            simp only [stoppedValue, hstart, hrhohit]
          exact heq.trans hh.2
        exact ⟨hev.1.1, hexit ▸ hev.1.2.1, by simpa [hstart, hrhohit] using hh.1, hval⟩
  rw [measure_congr hdec, measure_union₀ hN hDN, hmeasureN, hmeasureD]
  simp_rw [hmeasureE]
  have hfactor (v : V) :
      (if v ∈ A then 0 else
        PF.P z (F ∩ stopEvent PF.X τ x) *
          ((((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x v / G.pi x)) *
            ENNReal.ofReal (G.harmonicMeasure hG A v y))) =
      PF.P z (F ∩ stopEvent PF.X τ x) * ((expMeasure (w x)).map toWithTop) B *
        (if v ∈ A then 0 else
          ENNReal.ofReal (G.c x v / G.pi x) *
            ENNReal.ofReal (G.harmonicMeasure hG A v y)) := by
    by_cases hv : v ∈ A <;> simp [hv, mul_assoc]
  simp_rw [hfactor]
  have hjump (v : V) :
      (if v ∈ A then 0 else
        ENNReal.ofReal (G.c x v / G.pi x) *
          ENNReal.ofReal (G.harmonicMeasure hG A v y)) =
        ENNReal.ofReal (G.jumpTerm hG A x y v) := by
    by_cases hv : v ∈ A
    · simp [hv, ConductanceGraph.jumpTerm]
    · rw [if_neg hv, ConductanceGraph.jumpTerm, if_neg hv,
        ← ENNReal.ofReal_mul (div_nonneg (G.c_nonneg x v) (G.pi_nonneg x))]
  simp_rw [hjump]
  rw [ENNReal.tsum_mul_left]
  simp only [← mul_assoc]
  rw [← mul_add]
  rw [← ENNReal.ofReal_tsum_of_nonneg (G.jumpTerm_nonneg hG hA x y)
      (G.summable_jumpTerm hG hA x y),
    ← ENNReal.ofReal_add (div_nonneg (G.c_nonneg x y) (G.pi_nonneg x))
      (tsum_nonneg (G.jumpTerm_nonneg hG hA x y)),
    ← G.inducedTransProb_of_mem_of_mem hG hx hy]

end ReflectedGMS.TargetReturnKernelLaw
