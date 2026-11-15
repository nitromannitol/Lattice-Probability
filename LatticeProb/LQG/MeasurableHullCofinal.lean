import LatticeProb.LQG.DyadicHullNeighborhoods
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1

/-! # Measurable selection of cofinal dyadic hulls -/

set_option autoImplicit false

open Set Metric MeasureTheory
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF

namespace LatticeProb.LQG

/-- Inclusion of one random hull in the interior of another is observable from
an arbitrary bounded closed random set. -/
theorem measurableSet_dyadicHull_subset_interior {Ω : Type} (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (m n : ℕ) : MeasurableSet[setSigma A]
      {ω | dyadicHull m (A ω) ⊆ interior (dyadicHull n (A ω))} := by
  classical
  let : MeasurableSpace Ω := setSigma A
  have heq : {ω | dyadicHull m (A ω) ⊆ interior (dyadicHull n (A ω))} =
      ⋃ S ∈ conf36HullShapes m, ⋃ T ∈ conf36HullShapes n,
        if S ⊆ interior T then
          {ω | dyadicHull m (A ω) = S} ∩ {ω | dyadicHull n (A ω) = T}
        else ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_ite_empty_right]
    constructor
    · intro h
      exact ⟨_, conf36_hull_mem_shapes (Or.inl (hbounded ω)) m,
        _, conf36_hull_mem_shapes (Or.inl (hbounded ω)) n, h, rfl, rfl⟩
    · rintro ⟨S, hS, T, hT, h, hm, hn⟩
      simpa only [hm, hn] using h
  rw [heq]
  apply MeasurableSet.biUnion (conf36HullShapes_countable m)
  intro S hS
  apply MeasurableSet.biUnion (conf36HullShapes_countable n)
  intro T hT
  split_ifs
  · exact (measurableSet_hull_eq hclosed m S).inter (measurableSet_hull_eq hclosed n T)
  · exact (MeasurableSet.empty : MeasurableSet[setSigma A] (∅ : Set Ω))

/-- A compact random set admits a measurable choice of a finer dyadic hull
contained in the interior of a specified hull. -/
theorem exists_measurable_dyadicHull_subset_interior {Ω : Type} (A : Ω → Set ℂ)
    (hA : ∀ ω, IsCompact (A ω)) (n : ℕ) :
    ∃ f : Ω → ℕ, Measurable[setSigma A] f ∧
      ∀ ω, dyadicHull (f ω) (A ω) ⊆ interior (dyadicHull n (A ω)) := by
  classical
  let : MeasurableSpace Ω := setSigma A
  have hex : ∀ ω, ∃ m : ℕ,
      dyadicHull m (A ω) ⊆ interior (dyadicHull n (A ω)) := by
    intro ω
    obtain ⟨ε, hε, hsub⟩ := exists_thickening_subset_interior_dyadicHull (hA ω) n
    obtain ⟨m, hm⟩ := exists_dyadicHull_subset_thickening (A ω) hε
    exact ⟨m, hm.trans hsub⟩
  refine ⟨fun ω => Nat.find (hex ω), ?_, fun ω => Nat.find_spec (hex ω)⟩
  exact measurable_find hex fun m =>
    measurableSet_dyadicHull_subset_interior A (fun ω => (hA ω).isClosed)
      (fun ω => (hA ω).isBounded) m n

end LatticeProb.LQG
