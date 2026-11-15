import Mathlib.Analysis.Complex.Basic
import LatticeProb.Topology.CompactImageMatching
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # Countable matching of compact images -/

set_option autoImplicit false

open Set Topology TopologicalSpace

namespace LatticeProb

noncomputable local instance : MeasurableSpace (NonemptyCompacts ℂ) := borel _
local instance : BorelSpace (NonemptyCompacts ℂ) := ⟨rfl⟩

/-- Exact image matching is measurable for measurable maps and compact cells. -/
theorem measurableSet_compact_image_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → C(ℂ, ℂ)) (K L : Ω → NonemptyCompacts ℂ)
    (hF : Measurable F) (hK : Measurable K) (hL : Measurable L) :
    MeasurableSet {ω | (K ω).map (F ω) (F ω).continuous = L ω} := by
  let S : Set (C(ℂ, ℂ) × NonemptyCompacts ℂ × NonemptyCompacts ℂ) :=
    {p | p.2.1.map p.1 p.1.continuous = p.2.2}
  have hS : IsClosed S := by
    exact isClosed_nonemptyCompacts_image_eq Prod.fst (fun p : C(ℂ, ℂ) × NonemptyCompacts ℂ × NonemptyCompacts ℂ => p.2.1)
      (fun p => p.2.2) continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  exact hS.measurableSet.preimage (hF.prodMk (hK.prodMk hL))

/-- The active cells of a countable family can be matched measurably to another family. -/
theorem measurableSet_forall_exists_compact_image_eq
    {Ω I J : Type*} [MeasurableSpace Ω] [Countable I] [Countable J]
    (F : Ω → C(ℂ, ℂ)) (K : I → Ω → NonemptyCompacts ℂ)
    (L : J → Ω → NonemptyCompacts ℂ) (A : I → Set Ω) (B : J → Set Ω)
    (hF : Measurable F) (hK : ∀ i, Measurable (K i))
    (hL : ∀ j, Measurable (L j)) (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ j, MeasurableSet (B j)) :
    MeasurableSet {ω | ∀ i, ω ∈ A i → ∃ j, ω ∈ B j ∧
      (K i ω).map (F ω) (F ω).continuous = L j ω} := by
  apply measurableSet_setOfPred.2
  exact Measurable.forall fun i => (measurableSet_setOfPred.1 (hA i)).imp <|
    Measurable.exists fun j => (measurableSet_setOfPred.1 (hB j)).and <|
      measurableSet_setOfPred.1 (measurableSet_compact_image_eq F (K i) (L j) hF (hK i) (hL j))

end LatticeProb
