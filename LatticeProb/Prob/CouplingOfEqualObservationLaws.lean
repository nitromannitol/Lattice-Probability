import LatticeProb.Prob.JointObservationLift

/-! # Coupling of two laws with the same law of a measurable observation

If two probability measures `P` and `W` on a standard Borel space have the same image under a
measurable map `obs` into a space with measurable diagonal, there is a probability measure on the
product with marginals `P` and `W` that is carried by the set where the two coordinates have the
same observation `obs`.  This is the gluing of `P` and `W` along their common law of `obs`. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace LatticeProb

/-- Coupling along a common observation law: if `P.map obs = W.map obs`, there is a probability
measure `Q` on `α × α` with marginals `P`, `W` and `obs q.1 = obs q.2` for `Q`-a.e. `q`. -/
theorem exists_coupling_of_map_eq {α S : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    [Nonempty α] [MeasurableSpace S] [MeasurableEq S] {obs : α → S} (hobs : Measurable obs)
    (P W : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure W]
    (h : P.map obs = W.map obs) :
    ∃ Q : Measure (α × α), IsProbabilityMeasure Q ∧ Q.fst = P ∧ Q.snd = W ∧
      ∀ᵐ q ∂Q, obs q.1 = obs q.2 := by
  let k : α → S × α := fun b => (obs b, b)
  have hk : Measurable k := hobs.prodMk measurable_id
  let ρ : Measure (S × α) := W.map k
  have hρprob : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hk.aemeasurable).2 inferInstance
  have hρfst : ρ.fst = P.map obs := by
    rw [h]
    change (W.map k).map Prod.fst = W.map obs
    rw [Measure.map_map measurable_fst hk]
    rfl
  obtain ⟨ξ, hξprob, hξfst, hξmap⟩ := exists_joint_observation_lift P ρ obs hobs hρfst
  have hg : Measurable (fun p : α × α => (obs p.1, p.2)) :=
    (hobs.comp measurable_fst).prodMk measurable_snd
  refine ⟨ξ, hξprob, hξfst, ?_, ?_⟩
  · change ξ.map Prod.snd = W
    have h1 : ξ.map Prod.snd = (ξ.map (fun p : α × α => (obs p.1, p.2))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hg]
      rfl
    rw [h1, hξmap]
    change (W.map k).map Prod.snd = W
    rw [Measure.map_map measurable_snd hk]
    exact Measure.map_id
  · have hset : MeasurableSet {q : S × α | q.1 = obs q.2} :=
      measurableSet_eq_fun measurable_fst (hobs.comp measurable_snd)
    have hρae : ∀ᵐ q ∂ρ, q.1 = obs q.2 :=
      (ae_map_iff hk.aemeasurable hset).2 (ae_of_all _ fun _ => rfl)
    rw [← hξmap] at hρae
    exact ae_of_ae_map hg.aemeasurable hρae

end LatticeProb
