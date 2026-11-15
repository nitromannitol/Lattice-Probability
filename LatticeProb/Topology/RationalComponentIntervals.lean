import LatticeProb.Topology.AreaCurveOpenCoverage

/-! # Component interval witnesses at rational times -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- For one nondegenerate segment, interval witnesses at rational interior times
suffice for every component of the interior of the segment image. -/
theorem component_intervals_of_rational_times
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    (f : C(ℝ, X)) {s t : ℝ} (hst : s < t)
    (h : ∀ q : ℚ, s < (q : ℝ) → (q : ℝ) < t →
      f q ∈ interior (f '' Icc s t) →
      ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (f '' Icc s t)) (f q)) =
          f '' Icc a b) :
    ∀ z ∈ interior (f '' Icc s t), ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
      closure (connectedComponentIn (interior (f '' Icc s t)) z) =
        f '' Icc a b := by
  intro z hz
  obtain ⟨v, hv, hvz⟩ := interior_subset hz
  let U := connectedComponentIn (interior (f '' Icc s t)) z
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have hvU : v ∈ f ⁻¹' U := by
    change f v ∈ U
    rw [hvz]
    exact mem_connectedComponentIn hz
  have hopen : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hvcl : v ∈ closure (Ioo s t) := by
    rw [closure_Ioo hst.ne]
    exact hv
  obtain ⟨w, hwU, hwst⟩ := mem_closure_iff.mp hvcl _ hopen hvU
  have hinter : IsOpen ((f ⁻¹' U) ∩ Ioo s t) := hopen.inter isOpen_Ioo
  obtain ⟨q, hqU, hqst⟩ := Rat.denseRange_cast.exists_mem_open hinter ⟨w, hwU, hwst⟩
  have hqint : f q ∈ interior (f '' Icc s t) := connectedComponentIn_subset _ _ hqU
  obtain ⟨a, b, ha, hab, hb, hq⟩ := h q hqst.1 hqst.2 hqint
  have heq : connectedComponentIn (interior (f '' Icc s t)) z =
      connectedComponentIn (interior (f '' Icc s t)) (f q) := connectedComponentIn_eq hqU
  exact ⟨a, b, ha, hab, hb, heq ▸ hq⟩

/-- Countably many fixed-time almost-sure witness statements imply a single
almost-sure statement for all interior components of a fixed segment. -/
theorem ae_component_intervals_of_rational_times
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [LocallyConnectedSpace X]
    (P : Measure Ω) (f : Ω → C(ℝ, X)) {s t : ℝ} (hst : s < t)
    (h : ∀ q : ℚ, ∀ᵐ ω ∂P, s < (q : ℝ) → (q : ℝ) < t →
      f ω q ∈ interior (f ω '' Icc s t) →
      ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (f ω '' Icc s t)) (f ω q)) =
          f ω '' Icc a b) :
    ∀ᵐ ω ∂P, ∀ z ∈ interior (f ω '' Icc s t),
      ∃ a b : ℝ, s ≤ a ∧ a ≤ b ∧ b ≤ t ∧
        closure (connectedComponentIn (interior (f ω '' Icc s t)) z) =
          f ω '' Icc a b := by
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact component_intervals_of_rational_times (f ω) hst hω

end LatticeProb
