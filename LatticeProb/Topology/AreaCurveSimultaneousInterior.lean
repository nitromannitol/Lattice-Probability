import LatticeProb.Topology.AreaCurveInteriorVisits

/-! # Simultaneous interior visits of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Almost every time visits the interior of the image of every segment
strictly containing that time. The exceptional set is common to all segments. -/
theorem ae_mem_interior_all_image_Icc_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a)) :
    ∀ᵐ u ∂volume, ∀ a b : ℝ, a < u → u < b →
      η u ∈ interior (η '' Icc a b) := by
  have hrat : ∀ᵐ u ∂volume, ∀ p q : ℚ, (p : ℝ) < (q : ℝ) →
      u ∈ Icc (p : ℝ) (q : ℝ) → η u ∈ interior (η '' Icc (p : ℝ) (q : ℝ)) := by
    apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    by_cases hpq : (p : ℝ) < (q : ℝ)
    · filter_upwards [ae_mem_interior_image_Icc_of_proper_area_curve η μ hη hp hs hmap harea hpq]
        with u hu _ hui
      exact hu hui
    · exact Filter.Eventually.of_forall fun _ h _ => (hpq h).elim
  filter_upwards [hrat] with u hu a b hau hub
  obtain ⟨p, hap, hpu⟩ := exists_rat_btwn hau
  obtain ⟨q, huq, hqb⟩ := exists_rat_btwn hub
  have hsub : Icc (p : ℝ) (q : ℝ) ⊆ Icc a b :=
    Icc_subset_Icc hap.le hqb.le
  exact interior_mono (image_mono hsub) (hu p q (hpu.trans huq) ⟨hpu.le, huq.le⟩)

end LatticeProb
