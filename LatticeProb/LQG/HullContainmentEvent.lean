import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1

/-! # Containment events for random dyadic hulls -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Containment of a fixed set in the interior of a bounded random dyadic hull
is measurable in the hull field sigma algebra. -/
theorem measurableSet_subset_interior_dyadicHull {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ) (T : Set ℂ) :
    MeasurableSet[hullSigma0 h A n]
      {ω | T ⊆ interior (dyadicHull n (A ω))} := by
  classical
  have heq : {ω | T ⊆ interior (dyadicHull n (A ω))} =
      ⋃ S ∈ {S ∈ conf36HullShapes n | T ⊆ interior S},
        {ω | dyadicHull n (A ω) = S} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · intro hT
      exact ⟨_, ⟨conf36_hull_mem_shapes (Or.inl (hA ω)) n, hT⟩, rfl⟩
    · rintro ⟨S, ⟨_, hT⟩, heq⟩
      simpa only [heq] using hT
  rw [heq]
  apply MeasurableSet.biUnion ((conf36HullShapes_countable n).mono (by intro S hS; exact hS.1))
  intro S hS
  have hgen : MeasurableSet[hullSigma0 h A n]
      ({ω | dyadicHull n (A ω) = S} ∩ (univ : Set Ω)) :=
    (le_sup_right : _ ≤ hullSigma0 h A n) _
      (measurableSet_generateFrom ⟨S, univ, @MeasurableSet.univ Ω _, rfl⟩)
  simpa only [inter_univ] using hgen

/-- The indicator of containment of a fixed set in the interior hull is a
real-valued measurable observation. -/
theorem measurable_indicator_subset_interior_dyadicHull {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ) (T : Set ℂ) :
    Measurable[hullSigma0 h A n] (fun ω =>
      ({ω | T ⊆ interior (dyadicHull n (A ω))} : Set Ω).indicator (fun _ => (1 : ℝ)) ω) := by
  exact measurable_const.indicator (measurableSet_subset_interior_dyadicHull h A hA n T)

end LatticeProb.LQG
