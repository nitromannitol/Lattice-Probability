import LatticeProb.Analysis.WedgeArcIntegral

/-! # Closure and endpoints of a circular arc -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- The closure of a nonempty circular arc is the image of the closed interval. -/
theorem closure_circleMap_image_Ioo {a b : ℝ} (hab : a < b) :
    closure (circleMap 0 1 '' Ioo a b) = circleMap 0 1 '' Icc a b := by
  apply Subset.antisymm
  · apply closure_minimal (image_mono Ioo_subset_Icc_self)
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  · rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image (by fun_prop)

/-- A symmetric arc shorter than a full turn has exactly its two endpoint
images in the difference between its closure and the arc itself. -/
theorem closure_circleMap_symmetric_arc_diff {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) :
    closure (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2)) \ 
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2)) =
        {circleMap 0 1 (-θ / 2), circleMap 0 1 (θ / 2)} := by
  rw [closure_circleMap_image_Ioo (by linarith : -θ / 2 < θ / 2)]
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    have hn' : x ∉ Ioo (-θ / 2) (θ / 2) := fun h => hn ⟨x, h, rfl⟩
    have : x = -θ / 2 ∨ x = θ / 2 := by
      simp only [mem_Ioo, not_and_or, not_lt] at hn'
      rcases hn' with h | h <;> [left; right] <;> linarith [hx.1, hx.2]
    rcases this with h | h <;> simp [h]
  · intro hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    all_goals
      constructor
      · first | exact ⟨-θ / 2, ⟨le_rfl, by linarith⟩, rfl⟩
              | exact ⟨θ / 2, ⟨by linarith, le_rfl⟩, rfl⟩
      · rintro ⟨x, hx, heq⟩
        have hxarg : (circleMap 0 1 x).arg = x :=
          arg_circleMap_mem_wedge (by linarith) ⟨hx.1, hx.2.le⟩
        have hbound : (-θ / 2 : ℝ) ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
          constructor <;> linarith
        have hbound' : (θ / 2 : ℝ) ∈ Ioc (-(2 * Real.pi) / 2) ((2 * Real.pi) / 2) := by
          constructor <;> linarith
        have he := congrArg Complex.arg heq
        rw [hxarg] at he
        first | rw [arg_circleMap_mem_wedge le_rfl hbound] at he; linarith [hx.1]
              | rw [arg_circleMap_mem_wedge le_rfl hbound'] at he; linarith [hx.2]

end LatticeProb
