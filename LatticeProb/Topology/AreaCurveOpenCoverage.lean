import LatticeProb.Topology.AreaCurveIntervalContainment
import Mathlib.Topology.Order.Basic

/-! # Open sets covered by area-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- If an open set is covered by an area-parametrized curve segment, all visits
occur strictly between the endpoints. -/
theorem preimage_open_subset_Ioo_of_area_curve_coverage
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : ℝ → X) (μ : Measure X)
    (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {U : Set X} (hU : IsOpen U) {a b : ℝ} (hab : a < b)
    (hcover : U ⊆ η '' Icc a b) : η ⁻¹' U ⊆ Ioo a b := by
  intro u hu
  have hopen : IsOpen (η ⁻¹' U) := hU.preimage hη
  obtain ⟨p, q, hpq, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hu)
  let p' := (p + u) / 2
  let q' := (u + q) / 2
  have hp'u : p' < u := by dsimp [p']; linarith [hpq.1]
  have huq' : u < q' := by dsimp [q']; linarith [hpq.2]
  have hp'q' : p' < q' := hp'u.trans huq'
  have himage : η '' Icc p' q' ⊆ η '' Icc a b := by
    rintro z ⟨t, ht, rfl⟩
    apply hcover
    apply hsub
    constructor
    · dsimp [p'] at ht
      linarith [hpq.1, ht.1]
    · dsimp [q'] at ht
      linarith [hpq.2, ht.2]
  have htime := Icc_subset_of_area_curve_image_subset η μ hη hμ hp'q' hab himage
  have hp' := htime ⟨le_rfl, hp'q'.le⟩
  have hq' := htime ⟨hp'q'.le, le_rfl⟩
  exact ⟨lt_of_le_of_lt hp'.1 hp'u, lt_of_lt_of_le huq' hq'.2⟩

end LatticeProb
