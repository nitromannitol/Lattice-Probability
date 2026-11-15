import LatticeProb.Walk.CoupledStoppedOuterBudget
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedEndpoint

/-! # Stopping and endpoint bounds for the joint excursion law -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- Under a selector that stops only outside `Q`, the joint failure of walk
stopping or Brownian outer exit is controlled by the Brownian active tail and
the first excursion-pair failure. -/
theorem actual_joint_stopping_outer_failure_le
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
    (Q : Set (Euc d)) (hQ : MeasurableSet Q)
    (hnone : ∀ k x, brownianSelectorForWalk select k x = none → x ∉ Q) (a : ℝ) :
    N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {x | (x.1 n).1 = false ∨ pastedBrownianCurve P x.2 1 ∈ Q} ≤
    μ {ω | (brownianSkeletonExcursion W z initial (brownianSelectorForWalk select) n ω).1 = false} +
    N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      {x | ∃ i ≤ n, (x.1 i, x.2 i) ∉ goodExcursionPair pos (E i) a} := by
  let ρ := N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  have hb : Measurable (fun ω k => brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion W hW z initial
      (fun i => hs (i - 1)) k
  have hend : ∀ᵐ γ ∂ρ.snd, (γ n).1 = true → pastedBrownianCurve P γ 1 ∉ Q := by
    rw [hm.2]
    exact standardBrownianLaw_skeleton_ae_stopped_endPoint_outside hd hμ W hW hWb z initial
      (brownianSelectorForWalk select) (fun i => hs (i - 1)) hQ hnone n P
  have hjoint : ∀ᵐ x ∂ρ, (x.2 n).1 = true → pastedBrownianCurve P x.2 1 ∉ Q :=
    ae_of_ae_map measurable_snd.aemeasurable hend
  have hbound := coupled_stopping_outer_failure_le pos m E a P Q ρ hjoint
  rw [hm.2, Measure.map_apply hb (measurableSet_sequenceActive n)] at hbound
  exact hbound

end LatticeProb
end
