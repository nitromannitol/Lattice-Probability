import LatticeProb.Topology.RationalComponentIntervals
import LatticeProb.Topology.AreaComponentWitnessTransfer
import LatticeProb.Topology.ProperAreaCurveFrontier
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Component intervals for countable families of curve segments -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- Fixed rational-time witness statements for a countable family of segments
imply a common event on which almost every visit to each segment is inside an
interval tracing the closure of the visited interior component. -/
theorem ae_countable_segment_component_visits
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (f : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ)
    (s t : ι → ℝ) (hst : ∀ i, s i < t i)
    (hcurve : ∀ᵐ ω ∂P, IsProperMap (f ω) ∧ Surjective (f ω) ∧
      Measure.map (f ω) volume = μ ω ∧
      ∀ a b, a < b → μ ω (f ω '' Icc a b) = ENNReal.ofReal (b - a))
    (h : ∀ i : ι, ∀ q : ℚ, ∀ᵐ ω ∂P,
      s i < (q : ℝ) → (q : ℝ) < t i →
      f ω q ∈ interior (f ω '' Icc (s i) (t i)) →
      ∃ a b : ℝ, s i ≤ a ∧ a ≤ b ∧ b ≤ t i ∧
        closure (connectedComponentIn (interior (f ω '' Icc (s i) (t i))) (f ω q)) =
          f ω '' Icc a b) :
    ∀ᵐ ω ∂P, ∀ i : ι, ∀ᵐ u ∂volume, u ∈ Icc (s i) (t i) →
      ∃ a b : ℝ, s i ≤ a ∧ a < u ∧ u < b ∧ b ≤ t i ∧
        closure (connectedComponentIn (interior (f ω '' Icc (s i) (t i))) (f ω u)) =
          f ω '' Icc a b := by
  filter_upwards [hcurve, ae_all_iff.2 (fun i => ae_all_iff.2 (h i))] with ω hc hw
  obtain ⟨hp, hs, hmap, harea⟩ := hc
  intro i
  have hinter := component_intervals_of_rational_times (f ω) (hst i) (hw i)
  have hfront := measure_frontier_image_Icc_eq_zero_of_proper (f ω) (μ ω)
    (f ω).continuous hp hs harea (hst i)
  have hae := interior_ae_eq_of_null_frontier hfront
  rw [← hmap] at hae
  have hae' := ae_of_ae_map (f ω).continuous.measurable.aemeasurable hae
  filter_upwards [hae'] with u hu huI
  have hui : f ω u ∈ interior (f ω '' Icc (s i) (t i)) := hu.mpr ⟨u, huI, rfl⟩
  obtain ⟨a, b, ha, hab, hb, himage⟩ := hinter (f ω u) hui
  let U := connectedComponentIn (interior (f ω '' Icc (s i) (t i))) (f ω u)
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have huU : f ω u ∈ U := mem_connectedComponentIn hui
  have hab' : a < b := interval_lt_of_image_eq_closure_open (f ω) U a b hU
    ⟨f ω u, huU⟩ himage.symm
  have huv : u ∈ Ioo a b := preimage_open_subset_Ioo_of_area_curve_coverage
    (f ω) (μ ω) (f ω).continuous harea hU hab' (by rw [← himage]; exact subset_closure) huU
  exact ⟨a, b, ha, huv.1, huv.2, hb, himage⟩

end LatticeProb
