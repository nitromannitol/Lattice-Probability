/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkBrownianActiveTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianFailure

/-! Transfer the checked Brownian active-tail bound to the original walk
through the actual full-sequence coupling and its good-state flag equality. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

variable {d : ℕ}

def sequenceActive {S : Type*} (K : ℕ) : Set (ℕ → Bool × S) :=
  {ω | (ω K).1 = false}

lemma measurableSet_sequenceActive {S : Type*} [MeasurableSpace S] (K : ℕ) :
    MeasurableSet (sequenceActive (S := S) K) :=
  ((measurable_pi_apply K).fst) (measurableSet_singleton false)

lemma coupling_walkActive_le_brownianActive_add_firstFailure {V : Type*}
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (a : ℝ) (K : ℕ)
    (ρ : Measure ((ℕ → Bool × ClockedWalkExcursion d) × (ℕ → Bool × C(unitInterval, Euc d)))) :
    ρ.fst (sequenceActive K) ≤ ρ.snd (sequenceActive K) +
      ρ {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} := by
  rw [Measure.fst_apply (measurableSet_sequenceActive K),
    Measure.snd_apply (measurableSet_sequenceActive K)]
  apply (measure_mono ?_).trans (measure_union_le _ _)
  intro p hp
  by_cases hg : (p.1 K, p.2 K) ∈ goodExcursionPair pos (E K) a
  · left
    exact (goodExcursionPair_flags pos (E K) a hg).symm.trans hp
  · right
    exact ⟨K, le_rfl, hg⟩

namespace FiniteConductanceNetwork

variable {V J : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

/-- Actual original-walk truncation costs at most the actual Brownian tail
plus the first-failure probability of the explicit full-excursion coupling. -/
theorem trajectoryLaw_walkActive_le_brownianActive_add_failure
    (N : FiniteConductanceNetwork V) (hd : 1 ≤ d)
    (pos : V → Euc d) (hinj : Function.Injective pos)
    (B : J → Set V) (hB : ∀ j v, v ∈ B j → 0 < N.totalConductance v)
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (hUb : ∀ j, Bornology.IsBounded (U j))
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (select : ℕ → Euc d → Option J) (hs : ∀ n, Measurable (select n))
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set (Euc d))
    (hE : ∀ n i, MeasurableSet (E n i))
    (hdE : ∀ n, Pairwise (fun i j => Disjoint (E n i) (E n j)))
    {A : Set V} (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (v : V) (z : Euc d) (a : ℝ) (K : ℕ) :
    N.trajectoryLaw A hA v
      {ω | (actualWalkExcursionSequence pos B initial select ω K).1 = false} ≤
      μ {ω | (brownianSkeletonExcursion U z initial (brownianSelectorForWalk select) K ω).1 = false} +
        N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z
          {p | ∃ i ≤ K, (p.1 i, p.2 i) ∉ goodExcursionPair pos (E i) a} := by
  have hm := N.walkBrownianJointLaw_marginals pos hinj B hB U hU μ select hs m E hE hdE
    hd hμ hUb hBA hA haccess initial v z
  have hw : Measurable (actualWalkExcursionSequence pos B initial select) :=
    measurable_actualWalkExcursionSequence pos B initial select
  have hb : Measurable (fun ω k => brownianSkeletonExcursion U z initial
      (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion U hU z initial
      (fun n => hs (n - 1)) k
  have hbound := coupling_walkActive_le_brownianActive_add_firstFailure pos m E a K
    (N.walkBrownianJointLaw pos hinj B hB U hU μ select hs m E hE hdE initial v z)
  rw [hm.1, hm.2, Measure.map_apply hw (measurableSet_sequenceActive K),
    Measure.map_apply hb (measurableSet_sequenceActive K)] at hbound
  exact hbound

end FiniteConductanceNetwork
end BouRabeeGwynne
