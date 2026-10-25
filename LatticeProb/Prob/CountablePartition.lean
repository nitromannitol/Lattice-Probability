module

/-
Transfer of event masses through a common countable partition. Each realization
may use its own sample space and atoms. Equal measurable atom masses, disjointness,
and the two exact event decompositions suffice for equality of the event masses.
-/
public import Mathlib.MeasureTheory.Measure.NullMeasurable

@[expose] public section


set_option autoImplicit false

namespace LatticeProb.Prob.CountablePartition

open MeasureTheory

variable {Ω Ω' J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Countable J]

/-- **Countable partition transfer.** Two events partitioned by disjoint measurable
atoms indexed by the same countable set have equal mass when corresponding atoms do.
No independence, termination or output-distribution hypothesis is needed. -/
theorem measure_eq_of_partition (P : Measure Ω) (P' : Measure Ω')
    (E : Set Ω) (E' : Set Ω') (A : J → Set Ω) (A' : J → Set Ω')
    (hE : E = ⋃ j, A j) (hE' : E' = ⋃ j, A' j)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hdis' : Pairwise (fun i j => Disjoint (A' i) (A' j)))
    (hm : ∀ j, MeasurableSet (A j)) (hm' : ∀ j, MeasurableSet (A' j))
    (hweights : ∀ j, P (A j) = P' (A' j)) : P E = P' E' := by
  rw [hE, hE', measure_iUnion hdis hm, measure_iUnion hdis' hm']
  exact tsum_congr hweights

end LatticeProb.Prob.CountablePartition
