import LatticeProb.Topology.CountableCompactImageMatching

/-! # Adjacency preservation for countable compact families -/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- Adjacency preservation under all active image matches is a measurable event. -/
theorem measurableSet_forall_compact_image_adj
    {Ω I J : Type*} [MeasurableSpace Ω] [Countable I] [Countable J]
    (F : Ω → C(ℂ, ℂ)) (K : I → Ω → NonemptyCompacts ℂ)
    (L : J → Ω → NonemptyCompacts ℂ) (A : I → Set Ω) (B : J → Set Ω)
    (E : I → I → Set Ω) (D : J → J → Set Ω)
    (hF : Measurable F) (hK : ∀ i, Measurable (K i))
    (hL : ∀ j, Measurable (L j)) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ j, MeasurableSet (B j))
    (hE : ∀ i i', MeasurableSet (E i i')) (hD : ∀ j j', MeasurableSet (D j j')) :
    MeasurableSet {ω | ∀ i i' j j',
      ω ∈ A i → ω ∈ A i' → ω ∈ B j → ω ∈ B j' →
      (K i ω).map (F ω) (F ω).continuous = L j ω →
      (K i' ω).map (F ω) (F ω).continuous = L j' ω →
      ω ∈ E i i' → ω ∈ D j j'} := by
  apply measurableSet_setOfPred.2
  refine Measurable.forall fun i => Measurable.forall fun i' =>
    Measurable.forall fun j => Measurable.forall fun j' => ?_
  exact (measurableSet_setOfPred.1 (hA i)).imp <|
    (measurableSet_setOfPred.1 (hA i')).imp <|
    (measurableSet_setOfPred.1 (hB j)).imp <|
    (measurableSet_setOfPred.1 (hB j')).imp <|
    (measurableSet_setOfPred.1
      (measurableSet_compact_image_eq F (K i) (L j) hF (hK i) (hL j))).imp <|
    (measurableSet_setOfPred.1
      (measurableSet_compact_image_eq F (K i') (L j') hF (hK i') (hL j'))).imp <|
    (measurableSet_setOfPred.1 (hE i i')).imp (measurableSet_setOfPred.1 (hD j j'))

end LatticeProb
