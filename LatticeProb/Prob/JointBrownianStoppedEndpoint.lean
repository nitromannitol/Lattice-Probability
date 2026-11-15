import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedEndpoint
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Stopped Brownian endpoints under a joint excursion law -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- The stopped Brownian endpoint under the original joint excursion law lies
outside any measurable set on which the walk selector is active. -/
theorem jointLaw_brownian_stopped_endpoint_outside
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
    (initial : J) (v : V) (z : Euc d) {C : Set (Euc d)} (hC : MeasurableSet C)
    (hnone : ∀ i x, select i x = none → x ∉ C) (n : ℕ) (P : TimePartition n) :
    ∀ᵐ γ ∂(N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
        initial v z).snd,
      (γ n).1 = true →
        P.concatenate (ExcursionTrajectory.prefixChain n d (fun k => (γ k).2)) 1 ∉ C := by
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  rw [hm.2]
  exact standardBrownianLaw_skeleton_ae_stopped_endPoint_outside hd hμ W hW hWb z initial
    (brownianSelectorForWalk select) (fun i => hs (i - 1)) hC
    (fun i x hx => hnone (i - 1) x hx) n P

end LatticeProb
