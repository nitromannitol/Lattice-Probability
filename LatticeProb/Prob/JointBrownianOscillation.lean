import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteProbability

/-! # Brownian oscillation under a joint excursion law -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- A pasted Brownian oscillation event has the same probability under the
joint excursion law's second marginal and under the original Brownian law. -/
theorem jointLaw_brownian_pasted_oscillation
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
    (initial : J) (v : V) (z : Euc d) (n : ℕ) (P : TimePartition n)
    {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q) (η : ℝ) :
    (N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
      initial v z).snd {γ | pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η} =
    μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad U Q η} := by
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  have hΓ : Measurable (fun ω k => brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion W hW z initial
      (fun i => hs (i - 1)) k
  have hbad : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η} :=
    (measurableSet_unitCurveExitOscillationBad hU hQ η).preimage
      (measurable_pastedBrownianCurve P)
  rw [hm.2, Measure.map_apply hΓ hbad]
  rfl

end LatticeProb
