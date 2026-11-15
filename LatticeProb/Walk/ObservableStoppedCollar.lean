import LatticeProb.Walk.ObservablePastedCollar
import LatticeProb.Walk.ActualJointStoppedOuterBudget

/-! # Observable stopping and collar failures -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- Failure of the collar conditions, walk stopping, or outer endpoint condition. -/
def pastedStoppedCollarBad {d n : ℕ} (P : TimePartition n) (e : ℝ)
    (U Q : Set (Euc d)) (η : ℝ) :
    Set ((ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)) :=
  pastedCollarBad P e U Q η ∪ {x | (x.1 n).1 = false ∨ x.2 1 ∈ Q}

lemma measurableSet_pastedStoppedCollarBad {d n : ℕ} (P : TimePartition n) (e : ℝ)
    {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q) (η : ℝ) :
    MeasurableSet (pastedStoppedCollarBad (d := d) P e U Q η) := by
  apply (measurableSet_pastedCollarBad P e hU hQ η).union
  exact ((measurableSet_sequenceActive n).preimage measurable_fst).union
    (hQ.measurableSet.preimage ((ContinuousMap.measurable_eval 1).comp measurable_snd))

/-- Outside the enlarged event, both the collar and stopping conditions hold. -/
lemma pastedStoppedCollar_good_of_not_mem {d n : ℕ} (P : TimePartition n)
    {e η : ℝ} {U Q : Set (Euc d)}
    {x : (ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)}
    (hx : x ∉ pastedStoppedCollarBad P e U Q η) :
    (∀ t, dist (pastedWalkCurve P x.1 t) (x.2 t) ≤ e) ∧
      x.2 ∉ unitCurveExitOscillationBad U Q η ∧
      (x.1 n).1 = true ∧ x.2 1 ∉ Q := by
  have hc := pastedCollar_good_of_not_mem P (fun h => hx (Or.inl h))
  have hs : (x.1 n).1 ≠ false := fun h => hx (Or.inr (Or.inl h))
  exact ⟨hc.1, hc.2, Bool.eq_true_of_not_eq_false hs, fun h => hx (Or.inr (Or.inr h))⟩

/-- The enlarged observable event costs the collar budget plus the Brownian
active tail and a second copy of the excursion-pair failure probability. -/
theorem pastedStoppedCollarBad_map_le
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (W : J → Set (Euc d)) (hW : ∀ j, IsOpen (W j))
    (hWb : ∀ j, Bornology.IsBounded (W j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ i, Measurable (select i))
    (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (hE : ∀ i k, MeasurableSet (E i k))
    (hdE : ∀ i, Pairwise (fun j k => Disjoint (E i j) (E i k)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) {n : ℕ} (P : TimePartition n)
    {a R S e η : ℝ} {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q)
    (hnone : ∀ k x, brownianSelectorForWalk select k x = none → x ∉ Q)
    (hdiam : ∀ i ≤ n, ∀ k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hnear : dist (pos v) z ≤ a) (hpoint : R + a + S ≤ e)
    (hwrange : ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ i,
      ClockedWalkExcursion.curve (FiniteConductanceNetwork.actualWalkExcursionSequence
        pos B initial select ω i).2 ∈ curveOscillationLe R)
    (hbrange : ∀ᵐ ω ∂μ, ∀ i,
      (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) i ω).2 ∈
        curveOscillationLe S) :
    ((N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
      initial v z).map (fun p => (p.1, pastedBrownianCurve P p.2)))
        (pastedStoppedCollarBad P e U Q η) ≤
      (N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
        {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} +
      μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad U Q η}) +
      (μ {ω | (brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) n ω).1 = false} +
      N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
        {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a}) := by
  let ρ := N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
  have hmap : Measurable (fun p : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) => (p.1, pastedBrownianCurve P p.2)) :=
    measurable_fst.prodMk ((measurable_pastedBrownianCurve P).comp measurable_snd)
  have hbad : MeasurableSet {x : (ℕ → Bool × ClockedWalkExcursion d) ×
      C(unitInterval, Euc d) | (x.1 n).1 = false ∨ x.2 1 ∈ Q} :=
    ((measurableSet_sequenceActive n).preimage measurable_fst).union
      (hQ.measurableSet.preimage ((ContinuousMap.measurable_eval 1).comp measurable_snd))
  have hstop := actual_joint_stopping_outer_failure_le N hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE hBA hA haccess initial v z P Q hQ.measurableSet hnone a
  calc
    _ ≤ (ρ.map (fun p => (p.1, pastedBrownianCurve P p.2))) (pastedCollarBad P e U Q η) +
        (ρ.map (fun p => (p.1, pastedBrownianCurve P p.2)))
          {x | (x.1 n).1 = false ∨ x.2 1 ∈ Q} := measure_union_le _ _
    _ ≤ _ := add_le_add
      (pastedCollarBad_map_le N hd pos hinj B hB W hW hWb μ hμ select hs m E hE hdE
        hBA hA haccess initial v z P hU hQ hdiam hnear hpoint hwrange hbrange)
      (by rw [Measure.map_apply hmap hbad]; exact hstop)


/-- An observable stopped-collar bound transfers along a lift of the joint law
from excursion sequences to original walk paths. -/
theorem originalWalk_stoppedCollarBad_le {d n : ℕ} {V J : Type*}
    [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (pos : V → Euc d) (B : J → Set V) (initial : J)
    (select : ℕ → Euc d → Option J) (P : TimePartition n) (e : ℝ)
    {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q) (η : ℝ)
    (ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)))
    (ξ : Measure ((ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)))
    (hlift : ρ.map (fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
      pos B initial select x.1, x.2)) = ξ)
    (r : ℝ≥0∞) (hbudget : ξ (pastedStoppedCollarBad P e U Q η) ≤ r) :
    ρ {x | (FiniteConductanceNetwork.actualWalkExcursionSequence
      pos B initial select x.1, x.2) ∈ pastedStoppedCollarBad P e U Q η} ≤ r := by
  have hobs : Measurable (fun x : (ℕ → V) × C(unitInterval, Euc d) =>
      (FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select x.1, x.2)) :=
    ((FiniteConductanceNetwork.measurable_actualWalkExcursionSequence pos B initial select).comp
      measurable_fst).prodMk measurable_snd
  change ρ ((fun x => (FiniteConductanceNetwork.actualWalkExcursionSequence
    pos B initial select x.1, x.2)) ⁻¹' pastedStoppedCollarBad P e U Q η) ≤ r
  rw [← Measure.map_apply hobs (measurableSet_pastedStoppedCollarBad P e hU hQ η), hlift]
  exact hbudget

end LatticeProb
end
