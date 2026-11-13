/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetReturnConditional at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DiscountedTraceStep
import LatticeProb.Bonanno.ReflectedGMS.Forms.FiniteTraceTransition

/-!
# The target-return law after a completed stopping time

This file transfers the checked first-holding/first-return law to an arbitrary
completed stopping time.  The clock records only the holding time at the
stopped target vertex; any subsequent excursion outside the target is deleted.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS.TargetReturnConditional

open ReflectedWalk ReflectedWalk.Theorem16

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

variable {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

/-- The exit holding-time/exit-vertex law after an arbitrary completed stopping
time, on a stopped-past event.  This is the one-step adapter used below. -/
theorem measure_exitPair_completed (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (z : V)
    {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
    (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)
    {F : Set PF.Ω} (hF : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) τ F)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A)
    {B : Set (WithTop ℝ≥0)} (hB : MeasurableSet B) (v : V) :
    PF.P z (F ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) =
      PF.P z (F ∩ stopEvent PF.X τ x) *
        (((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x v / G.pi x)) := by
  have hRz : RightContinuousAtInfty (PF.P z) PF.X := (h z).2.2.2.1
  rw [← G.transProb_of_mem hG hx v]
  rw [← measure_stepPair_one h hG (fun q => (h q).2.2.2.1) hA x hB v,
    ← law_stepPairEvent h x (h x).2.2.2.1 A hB v,
    ← strongMarkov_completed h z hRz hτm hτ x hF
      (measurableSet_stepPairEvent A hB v)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_rightRegularAt (h z).2.2.1 hRz] with ω hω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hFx, hhold, hv⟩
    refine ⟨hFx, ?_⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFx.2.1
    have hexit : exitAfter PF.X τ ω =
        hitAfter PF.X {s : Option V | s ≠ some x} τ ω := by
      rw [exitAfter, hFx.2.2]
    have hnext : nextStep PF.X A τ ω =
        hitAfter PF.X {s : Option V | s ≠ some x} τ ω := by
      rw [nextStep_eq_of_eq hx hFx.2.2]
    have hnextVal : stoppedValue PF.X (nextStep PF.X A τ) ω =
        stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω := by
      simp only [stoppedValue, hnext]
    rw [mem_stepPairEvent_futureAt_iff hω A B v ha.symm
      (by rw [hFx.2.2]; exact admissibleTarget_ne x), hexit, hnext, hnextVal]
    exact ⟨hhold, hv.1, hv.2⟩
  · rintro ⟨hFx, hfut⟩
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hFx.2.1
    have hexit : exitAfter PF.X τ ω =
        hitAfter PF.X {s : Option V | s ≠ some x} τ ω := by
      rw [exitAfter, hFx.2.2]
    have hnext : nextStep PF.X A τ ω =
        hitAfter PF.X {s : Option V | s ≠ some x} τ ω := by
      rw [nextStep_eq_of_eq hx hFx.2.2]
    have hnextVal : stoppedValue PF.X (nextStep PF.X A τ) ω =
        stoppedValue PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ω := by
      simp only [stoppedValue, hnext]
    rw [mem_stepPairEvent_futureAt_iff hω A B v ha.symm
      (by rw [hFx.2.2]; exact admissibleTarget_ne x), hexit, hnext, hnextVal] at hfut
    exact ⟨hFx, hfut.1, hfut.2.1, hfut.2.2⟩

/-- The exit history in `measure_exitPair_completed` belongs to the stopped
sigma-algebra at the exit time.  This permits a second completed strong-Markov
step for an excursion whose exit vertex is outside the finite target. -/
theorem aemeasurableSetStopped_exitPair_history (h : IsReflectedWalk G w hmin PF)
    (z : V) {τ : PF.Ω → WithTop ℝ≥0}
    (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)
    {F : Set PF.Ω} (hF : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) τ F)
    {x : V} {B : Set (WithTop ℝ≥0)} (hB : MeasurableSet B) (v : V) :
    AEMeasurableSetStopped PF.naturalFiltration (PF.P z)
      (hitAfter PF.X {s : Option V | s ≠ some x} τ)
      (F ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) := by
  let ρ := hitAfter PF.X {s : Option V | s ≠ some x} τ
  have hii := (h z).2.2.1
  have hR := (h z).2.2.2.1
  have hρ : IsAEStoppingTime PF.naturalFiltration (PF.P z) ρ :=
    isAEStoppingTime_hitAfter PF.measurable_X hii hR (admissibleTarget_ne x) hτ
  have hτρ : ∀ ω, τ ω ≤ ρ ω := fun ω => le_hitAfter ω
  have hFρ : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) ρ F :=
    hF.mono hρ hτρ
  have hxρ : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) ρ
      (stopEvent PF.X τ x) :=
    (aemeasurableSetStopped_stopEvent PF.measurable_X hii hR hτ x).mono hρ hτρ
  have hholdρ : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) ρ
      {ω | ρ ω - τ ω ∈ B} := by
    have hρρ : AEStoppedTime PF.naturalFiltration (PF.P z) ρ ρ :=
      AEStoppedTime.of_le hρ fun _ => le_rfl
    have hτρ' : AEStoppedTime PF.naturalFiltration (PF.P z) ρ τ :=
      AEStoppedTime.of_le hτ hτρ
    exact (hρρ.comp₂ hτρ' measurable_sub_withTop).preimage hρ hB
  have hvρ : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) ρ
      (stopEvent PF.X ρ v) :=
    aemeasurableSetStopped_stopEvent PF.measurable_X hii hR hρ v
  exact hFρ.inter hxρ |>.inter (hholdρ.inter hvρ)

/-- Conditional mass of an exit through `v`, followed by a return to `A` at
`y`.  The first factor records only the holding time at `x`; the duration of
the outside excursion is absent. -/
theorem measure_exitPair_then_hit_completed (h : IsReflectedWalk G w hmin PF)
    (hG : G.toSimpleGraph.Connected) (z : V)
    {τ : PF.Ω → WithTop ℝ≥0} (hτm : AEMeasurable τ (PF.P z))
    (hτ : IsAEStoppingTime PF.naturalFiltration (PF.P z) τ)
    {F : Set PF.Ω} (hF : AEMeasurableSetStopped PF.naturalFiltration (PF.P z) τ F)
    {A : Finset V} (hA : A.Nonempty) {x : V} (hx : x ∈ A)
    {B : Set (WithTop ℝ≥0)} (hB : MeasurableSet B) (v y : V) :
    PF.P z ((F ∩ stopEvent PF.X τ x ∩
        ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
          stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) ∩
        futureAt PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) ⁻¹'
          hitEvent A y) =
      PF.P z (F ∩ stopEvent PF.X τ x) *
        ((((expMeasure (w x)).map toWithTop) B * ENNReal.ofReal (G.c x v / G.pi x)) *
          ENNReal.ofReal (G.harmonicMeasure hG A v y)) := by
  let ρ := hitAfter PF.X {s : Option V | s ≠ some x} τ
  have hii := (h z).2.2.1
  have hRz := (h z).2.2.2.1
  have hρm : AEMeasurable ρ (PF.P z) :=
    aemeasurable_hitAfter PF.measurable_X hii hRz (admissibleTarget_ne x) hτm
  have hρ : IsAEStoppingTime PF.naturalFiltration (PF.P z) ρ :=
    isAEStoppingTime_hitAfter PF.measurable_X hii hRz (admissibleTarget_ne x) hτ
  have hK := aemeasurableSetStopped_exitPair_history h z hτ hF (x := x) hB v
  have hSM := strongMarkov_completed h z hRz hρm hρ v hK
    (measurableSet_hitEvent A y)
  have hsub :
      (F ∩ stopEvent PF.X τ x ∩
          ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
            stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v)) ∩
        stopEvent PF.X ρ v =
      F ∩ stopEvent PF.X τ x ∩
          ({ω | hitAfter PF.X {s : Option V | s ≠ some x} τ ω - τ ω ∈ B} ∩
            stopEvent PF.X (hitAfter PF.X {s : Option V | s ≠ some x} τ) v) := by
    apply Set.inter_eq_left.2
    intro ω hω
    exact hω.2.2
  rw [hsub] at hSM
  rw [hSM, law_hitEvent h hG v (h v).2.2.2.1 hA y,
    measure_exitPair_completed h hG z hτm hτ hF hA hx hB v, mul_assoc]

end ReflectedGMS.TargetReturnConditional
