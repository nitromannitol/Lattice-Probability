import LatticeProb.Walk.RestrictedWalkExitEdges

/-! # Ambient edge support for restricted walks -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory MatedCRTHarmonic.Markov

namespace LatticeProb

/-- The ambient law of a finite restricted walk follows positive conductance
edges strictly before its first exit from the active region. -/
theorem finiteConductanceRestriction_map_ae_pos_before_exit
    {V : Type*} [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (c : V → V → ℝ) (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R : Set V) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R) (B : Set V) (hAB : ∀ v : R, v ∈ A ↔ (v : V) ∈ B)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).totalConductance v)
    (v : R) :
    ∀ᵐ ω ∂((finiteConductanceRestriction c hsymm hnonneg hloop R).trajectoryLaw A hA v).map
        (fun p n => (p n : V)),
      ∀ j : ℕ, (j : ℕ∞) < hitTime Bᶜ ω → 0 < c (ω j) (ω (j + 1)) := by
  classical
  have hmap : Measurable (fun p : ℕ → R => fun n => (p n : V)) :=
    Measurable.of_eval fun n => (measurable_of_countable (fun x : R => (x : V))).comp
      (measurable_pi_apply n)
  have hc : Measurable (fun x : V × V => c x.1 x.2) := measurable_of_countable _
  have ht : Measurable (hitTime Bᶜ : (ℕ → V) → ℕ∞) :=
    measurable_hitTime (Set.to_countable _).measurableSet
  have hset : MeasurableSet {ω : ℕ → V | ∀ j : ℕ,
      (j : ℕ∞) < hitTime Bᶜ ω → 0 < c (ω j) (ω (j + 1))} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    have htime : MeasurableSet {ω : ℕ → V | (j : ℕ∞) < hitTime Bᶜ ω} :=
      ht (MeasurableSet.of_discrete : MeasurableSet {t : ℕ∞ | (j : ℕ∞) < t})
    have hpair : Measurable (fun ω : ℕ → V => (ω j, ω (j + 1))) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply (j + 1))
    have hedge : MeasurableSet {ω : ℕ → V | 0 < c (ω j) (ω (j + 1))} :=
      measurableSet_lt measurable_const (by
        simpa only [Function.comp_def] using hc.comp hpair)
    convert htime.compl.union hedge using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
  apply (ae_map_iff hmap.aemeasurable hset).2
  exact finiteConductanceRestriction_ae_pos_before_exit c hsymm hnonneg hloop R A B hAB hA v

end LatticeProb
end
