import LatticeProb.Prob.JointBrownianOscillation
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianActiveTransfer

/-! # Exceptional mass for coupled excursions -/

set_option autoImplicit false

open MeasureTheory Set BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- The first-failure, Brownian activity and Brownian oscillation events under
one joint excursion law have total mass bounded by their three source bounds. -/
theorem joint_excursion_exceptional_mass_le
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
    (a : ℝ) {U Q : Set (Euc d)} (hU : IsOpen U) (hQ : IsOpen Q) (η : ℝ)
    {b c o : ℝ≥0∞}
    (hfailure : N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE
      initial v z {p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ≤ b)
    (htail : μ {ω | (brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) n ω).1 = false} ≤ c)
    (hosc : μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) k ω) ∈ unitCurveExitOscillationBad U Q η} ≤ o) :
    N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
      (({p | ∃ i ≤ n, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} ∪
        Prod.snd ⁻¹' sequenceActive n) ∪
        Prod.snd ⁻¹' {γ | pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η}) ≤
      b + c + o := by
  let ρ := N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
    hd hμ hWb hBA hA haccess initial v z
  have hΓ : Measurable (fun ω k => brownianSkeletonExcursion W z initial
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion W hW z initial
      (fun i => hs (i - 1)) k
  have ht : ρ.snd (sequenceActive n) ≤ c := by
    rw [hm.2, Measure.map_apply hΓ (measurableSet_sequenceActive n)]
    exact htail
  have ho : ρ.snd {γ | pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η} ≤ o := by
    rw [jointLaw_brownian_pasted_oscillation N hd pos hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z n P hU hQ η]
    exact hosc
  have hO : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈ unitCurveExitOscillationBad U Q η} :=
    (measurableSet_unitCurveExitOscillationBad hU hQ η).preimage
      (measurable_pastedBrownianCurve P)
  apply le_trans (measure_union_le _ _)
  apply le_trans (add_le_add_left (measure_union_le _ _) _)
  rw [← Measure.snd_apply (measurableSet_sequenceActive n), ← Measure.snd_apply hO]
  exact add_le_add (add_le_add hfailure ht) ho

end LatticeProb
