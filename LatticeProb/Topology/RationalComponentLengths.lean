import LatticeProb.Topology.RationalComponentIntervals
import LatticeProb.Topology.AreaCurveAllComponentLengths
import LatticeProb.Topology.AreaComponentWitnessTransfer

/-! # Component lengths from rational-time witnesses -/

set_option autoImplicit false

open Set MeasureTheory Function LatticeProb.Topology

namespace LatticeProb

/-- Rational-time interval witnesses determine intervals for all components of
one segment; their positive lengths sum to the segment length. -/
theorem exists_all_component_interval_lengths_of_rational_times
    (η : C(ℝ, ℂ)) (μ : Measure ℂ)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {s t : ℝ} (hst : s < t)
    (h : ∀ q : ℚ, s < (q : ℝ) → (q : ℝ) < t →
      η q ∈ interior (η '' Icc s t) →
      ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (η '' Icc s t)) (η q)) =
          η '' Icc a b) :
    ∃ (x : {U // U ∈ connectedComponentsIn (interior (η '' Icc s t))} → ℂ)
      (a b : {U // U ∈ connectedComponentsIn (interior (η '' Icc s t))} → ℝ),
      (∀ i, connectedComponentIn (interior (η '' Icc s t)) (x i) = i.1) ∧
      (∀ i, s ≤ a i ∧ a i < b i ∧ b i ≤ t) ∧
      (∀ i, η '' Icc (a i) (b i) = closure i.1) ∧
      (∑' i, ENNReal.ofReal (b i - a i)) = ENNReal.ofReal (t - s) := by
  have hw := component_intervals_of_rational_times η hst h
  obtain ⟨x, a, b, hx, hi, hsum⟩ :=
    exists_all_component_interval_lengths η μ hp hs hmap harea hst (by
      intro z hz
      obtain ⟨a, b, _, _, _, hab⟩ := hw z hz
      exact ⟨a, b, hab.symm⟩)
  refine ⟨x, a, b, hx, ?_, hi, hsum⟩
  intro i
  apply component_interval_bounds_of_area_curve η μ (x i) s t (a i) (b i) hst harea
  · rw [hx i]
    obtain ⟨z, hz, hzcomp⟩ := i.2
    exact ⟨z, hzcomp ▸ mem_connectedComponentIn hz⟩
  · simpa only [hx i] using hi i

/-- For countably many segments, fixed rational-time witness events give a
single event on which all component interval lengths sum to their segment length. -/
theorem ae_all_component_interval_lengths_of_rational_times
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (μ : Ω → Measure ℂ)
    (s t : ι → ℝ) (hst : ∀ i, s i < t i)
    (hcurve : ∀ᵐ ω ∂P, IsProperMap (η ω) ∧ Surjective (η ω) ∧
      Measure.map (η ω) volume = μ ω ∧
      ∀ a b, a < b → μ ω (η ω '' Icc a b) = ENNReal.ofReal (b - a))
    (h : ∀ i : ι, ∀ q : ℚ, ∀ᵐ ω ∂P,
      s i < (q : ℝ) → (q : ℝ) < t i →
      η ω q ∈ interior (η ω '' Icc (s i) (t i)) →
      ∃ a b : ℝ, s i ≤ a ∧ a ≤ b ∧ b ≤ t i ∧
        closure (connectedComponentIn (interior (η ω '' Icc (s i) (t i))) (η ω q)) =
          η ω '' Icc a b) :
    ∀ᵐ ω ∂P, ∀ i : ι,
      ∃ (x : {U // U ∈ connectedComponentsIn (interior (η ω '' Icc (s i) (t i)))} → ℂ)
        (a b : {U // U ∈ connectedComponentsIn (interior (η ω '' Icc (s i) (t i)))} → ℝ),
        (∀ j, connectedComponentIn (interior (η ω '' Icc (s i) (t i))) (x j) = j.1) ∧
        (∀ j, s i ≤ a j ∧ a j < b j ∧ b j ≤ t i) ∧
        (∀ j, η ω '' Icc (a j) (b j) = closure j.1) ∧
        (∑' j, ENNReal.ofReal (b j - a j)) = ENNReal.ofReal (t i - s i) := by
  filter_upwards [hcurve, ae_all_iff.2 (fun i => ae_all_iff.2 (h i))] with ω hc hw
  obtain ⟨hp, hs, hmap, harea⟩ := hc
  intro i
  exact exists_all_component_interval_lengths_of_rational_times
    (η ω) (μ ω) hp hs hmap harea (hst i) (hw i)

end LatticeProb
