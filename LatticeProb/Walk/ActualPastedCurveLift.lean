import LatticeProb.Walk.ActualWalkBrownianJointLift
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteProbability

/-! # Coupling an original walk with a finite pasted curve -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set BouRabeeGwynne
open scoped unitInterval

namespace LatticeProb

/-- The original walk can be coupled with the pasted Brownian excursion curve
while preserving the full joint law of the walk excursions and pasted curve. -/
theorem exists_actualWalk_pastedBrownian_joint_lift
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
    (initial : J) (v : V) (z : Euc d) {n : ℕ} (P : TimePartition n) :
    ∃ ρ : Measure ((ℕ → V) × C(unitInterval, Euc d)),
      IsProbabilityMeasure ρ ∧ ρ.fst = N.trajectoryLaw A hA v ∧
      ρ.map (fun p => (FiniteConductanceNetwork.actualWalkExcursionSequence
        pos B initial select p.1, p.2)) =
        (N.walkBrownianJointLaw pos hinj B hB W hW μ select hs m E hE hdE initial v z).map
          (fun p => (p.1, pastedBrownianCurve P p.2)) ∧
      ρ.snd = (μ.map (fun ω k => brownianSkeletonExcursion W z initial
        (brownianSelectorForWalk select) k ω)).map (pastedBrownianCurve P) := by
  obtain ⟨ξ, hξprob, hξfst, hξjoint⟩ :=
    exists_actualWalkBrownian_joint_lift N hd pos hinj B hB W hW hWb μ hμ
      select hs m E hE hdE hBA hA haccess initial v z
  let := hξprob
  let f := FiniteConductanceNetwork.actualWalkExcursionSequence pos B initial select
  have hf : Measurable f :=
    FiniteConductanceNetwork.measurable_actualWalkExcursionSequence pos B initial select
  have hg := measurable_pastedBrownianCurve (d := d) P
  let ρ := ξ.map (fun p => (p.1, pastedBrownianCurve P p.2))
  have hmap : Measurable (fun p : (ℕ → V) × (ℕ → Bool × C(unitInterval, Euc d)) =>
      (p.1, pastedBrownianCurve P p.2)) := measurable_fst.prodMk (hg.comp measurable_snd)
  have hobsCurve : Measurable (fun p : (ℕ → V) × C(unitInterval, Euc d) =>
      (f p.1, p.2)) := (hf.comp measurable_fst).prodMk measurable_snd
  have hobsSeq : Measurable (fun p : (ℕ → V) × (ℕ → Bool × C(unitInterval, Euc d)) =>
      (f p.1, p.2)) := (hf.comp measurable_fst).prodMk measurable_snd
  have hmapJoint : Measurable (fun p : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) => (p.1, pastedBrownianCurve P p.2)) :=
    measurable_fst.prodMk (hg.comp measurable_snd)
  refine ⟨ρ, (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2 hξprob, ?_, ?_, ?_⟩
  · simpa [ρ] using (Measure.fst_map_prodMk measurable_fst (hg.comp measurable_snd)).trans hξfst
  · change (ξ.map (fun p => (p.1, pastedBrownianCurve P p.2))).map
      (fun p => (f p.1, p.2)) = _
    rw [Measure.map_map hobsCurve hmap]
    rw [← hξjoint]
    change _ = (ξ.map (fun p => (f p.1, p.2))).map _
    rw [Measure.map_map hmapJoint hobsSeq]
    rfl
  · change (ξ.map (fun p => (p.1, pastedBrownianCurve P p.2))).map Prod.snd = _
    rw [Measure.map_map measurable_snd hmap]
    have hsnd := congrArg Measure.snd hξjoint
    change (ξ.map (fun p => (f p.1, p.2))).map Prod.snd = _ at hsnd
    rw [Measure.map_map measurable_snd hobsSeq] at hsnd
    change ξ.map (fun p => p.2) = _ at hsnd
    change ξ.map ((pastedBrownianCurve P) ∘
      (Prod.snd : (ℕ → V) × (ℕ → Bool × C(unitInterval, Euc d)) → _)) = _
    rw [← Measure.map_map hg measurable_snd, hsnd,
      (N.walkBrownianJointLaw_marginals pos hinj B hB W hW μ select hs m E hE hdE
        hd hμ hWb hBA hA haccess initial v z).2]

end LatticeProb
end
