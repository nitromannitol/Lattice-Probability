import LatticeProb.Topology.ProperAreaCurveFrontier
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Regular closed images of area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory Function

namespace LatticeProb

/-- A compact curve segment with null frontier for the curve's pushforward of
Lebesgue measure is the closure of its interior. -/
theorem closure_interior_image_Icc_of_map_volume_of_null_frontier
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hmap : Measure.map η volume = μ) {a b : ℝ} (hab : a < b)
    (hfront : μ (frontier (η '' Icc a b)) = 0) :
    closure (interior (η '' Icc a b)) = η '' Icc a b := by
  let K := η '' Icc a b
  have hK : IsClosed K := (isCompact_Icc.image hη).isClosed
  have hae : ∀ᵐ t ∂volume, η t ∈ K → η t ∈ interior K := by
    have h := interior_ae_eq_of_null_frontier hfront
    rw [← hmap] at h
    have h' := ae_of_ae_map hη.measurable.aemeasurable h
    filter_upwards [h'] with t ht htK
    exact ht.mpr htK
  have hdense : Dense {t : ℝ | η t ∈ K → η t ∈ interior K} :=
    Measure.dense_of_ae hae
  have hsub : Ioo a b ⊆ η ⁻¹' closure (interior K) := by
    apply (hdense.open_subset_closure_inter isOpen_Ioo).trans
    apply closure_minimal _ (isClosed_closure.preimage hη)
    rintro t ⟨ht, htgood⟩
    exact subset_closure (htgood ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
  have hcc : Icc a b ⊆ η ⁻¹' closure (interior K) := by
    calc
      Icc a b = closure (Ioo a b) := (closure_Ioo hab.ne).symm
      _ ⊆ η ⁻¹' closure (interior K) :=
        closure_minimal hsub (isClosed_closure.preimage hη)
  apply Subset.antisymm (closure_minimal interior_subset hK)
  rintro x ⟨t, ht, rfl⟩
  exact hcc ht

/-- Every nondegenerate segment image of a proper surjective area-parametrized
curve is the closure of its interior. -/
theorem closure_interior_image_Icc_of_proper_area_curve
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (η : ℝ → X) (μ : Measure X) (hη : Continuous η)
    (hp : IsProperMap η) (hs : Surjective η) (hmap : Measure.map η volume = μ)
    (harea : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {a b : ℝ} (hab : a < b) :
    closure (interior (η '' Icc a b)) = η '' Icc a b :=
  closure_interior_image_Icc_of_map_volume_of_null_frontier η μ hη hmap hab
    (measure_frontier_image_Icc_eq_zero_of_proper η μ hη hp hs harea hab)

end LatticeProb
