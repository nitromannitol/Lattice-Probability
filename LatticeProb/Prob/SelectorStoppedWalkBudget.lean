import LatticeProb.Prob.SelectorStoppingConditions
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianActiveTransfer

/-! # Stopping conditions and activity budget for a coupled walk -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- A selector active on a closed thickening satisfies the stopping conditions,
while the walk activity is bounded by Brownian activity and coupling failure. -/
theorem selector_stopping_and_walk_active_le
    {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
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
    (initial : J) (v : V) (z : Euc d) (a : ℝ) (K : ℕ)
    (U : Set (Euc d)) {δ : ℝ} (hδ : 0 < δ)
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none)
    {b c : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) K ω).1 = false} ≤ c) :
    (∀ i x, select i x = none → x ∉ thickening δ U) ∧
    (∀ i x, select i x = none → x ∉ U) ∧
    (∀ i, Measurable (brownianSelectorForWalk select i)) ∧
    (∀ i x, brownianSelectorForWalk select i x = none → x ∉ thickening δ U) ∧
    N.trajectoryLaw A hA v
      {ω | (FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select ω K).1 = false} ≤
      c + b := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := selector_stopping_conditions U hδ select hs hactive
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  exact (N.trajectoryLaw_walkActive_le_brownianActive_add_failure hd pos hinj B hB W hW hWb
    μ hμ select hs m E hE hdE hBA hA haccess initial v z a K).trans (add_le_add htail hfailure)

end LatticeProb
