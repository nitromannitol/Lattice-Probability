import LatticeProb.LQG.MeasurableHullCofinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.L46MeasE9

/-! # Measurable collars for random dyadic hulls -/

set_option autoImplicit false

open Set Metric MeasureTheory
open LQGMetric.Blueprint LQGMetric.LocalEvent LQGMetric.CONF LQGMetric.GM

namespace LatticeProb.LQG

/-- A dyadic hull of a bounded set is compact. -/
theorem isCompact_dyadicHull_of_bounded {A : Set ℂ} (hA : Bornology.IsBounded A)
    (n : ℕ) : IsCompact (dyadicHull n A) := by
  obtain ⟨s, hs⟩ := exists_hullFin_of_bounded hA n
  rw [hs]
  exact s.isCompact_biUnion fun k _ => gmE_isCompact_dyadicSq n k

/-- The event that one random hull has a prescribed collar inside another
is measurable from the random set. -/
theorem measurableSet_thickening_dyadicHull_subset_interior {Ω : Type}
    (A : Ω → Set ℂ) (hclosed : ∀ ω, IsClosed (A ω))
    (hbounded : ∀ ω, Bornology.IsBounded (A ω)) (m n : ℕ) (r : ℝ) :
    MeasurableSet[setSigma A]
      {ω | thickening r (dyadicHull m (A ω)) ⊆ interior (dyadicHull n (A ω))} := by
  classical
  let : MeasurableSpace Ω := setSigma A
  have heq : {ω | thickening r (dyadicHull m (A ω)) ⊆ interior (dyadicHull n (A ω))} =
      ⋃ S ∈ conf36HullShapes m, ⋃ T ∈ conf36HullShapes n,
        if thickening r S ⊆ interior T then
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

/-- A positive reciprocal-integer collar can be chosen measurably from a
compact random set and lies inside its specified dyadic hull interior. -/
theorem exists_measurable_thickening_subset_interior_dyadicHull {Ω : Type}
    (A : Ω → Set ℂ) (hA : ∀ ω, IsCompact (A ω)) (n : ℕ) :
    ∃ f : Ω → ℕ, Measurable[setSigma A] f ∧ ∀ ω,
      thickening (1 / ((f ω : ℝ) + 1)) (A ω) ⊆ interior (dyadicHull n (A ω)) := by
  classical
  let : MeasurableSpace Ω := setSigma A
  have hex : ∀ ω, ∃ k : ℕ, ∃ m : ℕ,
      thickening (1 / ((k : ℝ) + 1)) (dyadicHull m (A ω)) ⊆
        interior (dyadicHull n (A ω)) := by
    intro ω
    obtain ⟨f, hf, hsub⟩ := exists_measurable_dyadicHull_subset_interior A hA n
    obtain ⟨ε, hε, hεsub⟩ :=
      (isCompact_dyadicHull_of_bounded (hA ω).isBounded (f ω)).exists_thickening_subset_open
        isOpen_interior (hsub ω)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    exact ⟨k, f ω, (thickening_mono hk.le _).trans hεsub⟩
  refine ⟨fun ω => Nat.find (hex ω), ?_, ?_⟩
  · apply measurable_find hex
    intro k
    simpa only [ofPred_exists] using (MeasurableSet.iUnion fun m =>
      measurableSet_thickening_dyadicHull_subset_interior A
        (fun ω => (hA ω).isClosed) (fun ω => (hA ω).isBounded) m n
        (1 / ((k : ℝ) + 1)))
  · intro ω
    obtain ⟨m, hm⟩ := Nat.find_spec (hex ω)
    exact (thickening_subset_of_subset _
      ((subset_interior_dyadicHull m (A ω)).trans interior_subset)).trans hm

end LatticeProb.LQG
