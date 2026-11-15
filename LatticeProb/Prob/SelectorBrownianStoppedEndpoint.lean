import LatticeProb.Prob.SelectorStoppingConditions
import LatticeProb.Prob.JointBrownianStoppedEndpoint

/-! # Stopped Brownian endpoints and selector coverage -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- If the selector covers a closed thickening, the endpoint of a stopped
Brownian skeleton lies outside the corresponding open thickening, under the
Brownian marginal of the original joint excursion law. -/
theorem jointLaw_brownian_stopped_endpoint_outside_thickening
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
    (initial : J) (v : V) (z : Euc d) (U : Set (Euc d)) {δ : ℝ} (hδ : 0 < δ)
    (hactive : ∀ i x, x ∈ cthickening δ U → select i x ≠ none)
    (n : ℕ) (P : TimePartition n) :
    ∀ᵐ γ ∂(N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).snd,
      (γ n).1 = true →
        P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) 1 ∉
          thickening δ U := by
  exact jointLaw_brownian_stopped_endpoint_outside N hd pos hinj B hB W hW hWb μ hμ
    select hs m E hE hdE hBA hA haccess initial v z isOpen_thickening.measurableSet
    (selector_stopping_conditions U hδ select hs hactive).1 n P

end LatticeProb
