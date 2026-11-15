import LatticeProb.Walk.ObservablePastedDistance
import LatticeProb.Prob.JointBrownianOscillation

/-! # Observable pasted-curve distance and collar oscillation -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- The observable failure of either uniform closeness or the collar
oscillation condition. -/
def pastedCollarBad {d n : ℕ} (P : TimePartition n) (e : ℝ)
    (U Q : Set (Euc d)) (η : ℝ) :
    Set ((ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)) :=
  pastedDistanceBad P e ∪ Prod.snd ⁻¹' unitCurveExitOscillationBad U Q η

lemma measurableSet_pastedCollarBad {d n : ℕ} (P : TimePartition n) (e : ℝ)
    {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q) (η : ℝ) :
    MeasurableSet (pastedCollarBad (d := d) P e U Q η) :=
  (measurableSet_pastedDistanceBad P e).union
    ((measurableSet_unitCurveExitOscillationBad hU hQ η).preimage measurable_snd)

lemma pastedCollar_good_of_not_mem {d n : ℕ} (P : TimePartition n) {e η : ℝ}
    {U Q : Set (Euc d)}
    {p : (ℕ → Bool × ClockedWalkExcursion d) × C(unitInterval, Euc d)}
    (hp : p ∉ pastedCollarBad P e U Q η) :
    (∀ t, dist (pastedWalkCurve P p.1 t) (p.2 t) ≤ e) ∧
      p.2 ∉ unitCurveExitOscillationBad U Q η := by
  constructor
  · intro t
    exact pastedDistance_le_of_not_mem P (fun h => hp (Or.inl h)) t
  · intro h
    exact hp (Or.inr h)

/-- The observable exceptional event is bounded by the joint excursion
failure and the Brownian pasted-curve oscillation probabilities. -/
theorem pastedCollarBad_map_le
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
        (pastedCollarBad P e U Q η) ≤
      N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
        {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} +
      μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad U Q η} := by
  let ρ := N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
  have hmap : Measurable (fun p : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) => (p.1, pastedBrownianCurve P p.2)) :=
    measurable_fst.prodMk ((measurable_pastedBrownianCurve P).comp measurable_snd)
  have ho : (ρ.map (fun p => (p.1, pastedBrownianCurve P p.2)))
      (Prod.snd ⁻¹' unitCurveExitOscillationBad U Q η) =
      μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad U Q η} := by
    rw [Measure.map_apply hmap
      ((measurableSet_unitCurveExitOscillationBad hU hQ η).preimage measurable_snd)]
    change ρ (Prod.snd ⁻¹' {γ | pastedBrownianCurve P γ ∈
      unitCurveExitOscillationBad U Q η}) = _
    have hO : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
        pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η} :=
      (measurableSet_unitCurveExitOscillationBad hU hQ η).preimage
        (measurable_pastedBrownianCurve P)
    rw [← Measure.snd_apply hO]
    exact jointLaw_brownian_pasted_oscillation N hd pos hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z n P hU hQ η
  calc
    _ ≤ (ρ.map (fun p => (p.1, pastedBrownianCurve P p.2))) (pastedDistanceBad P e) +
        (ρ.map (fun p => (p.1, pastedBrownianCurve P p.2)))
          (Prod.snd ⁻¹' unitCurveExitOscillationBad U Q η) := measure_union_le _ _
    _ ≤ _ := add_le_add
      (pastedDistanceBad_map_le_failure N hd pos hinj B hB W hW hWb μ hμ select hs
        m E hE hdE hBA hA haccess initial v z P hdiam hnear hpoint hwrange hbrange)
      (le_of_eq ho)

end LatticeProb
end
