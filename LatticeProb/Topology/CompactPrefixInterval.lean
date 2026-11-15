import LatticeProb.Topology.CompactStoppedPrefix
import LatticeProb.Prob.ContinuousStoppedPath

/-! # Compact prefixes and stopped path traces -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The normalized compact prefix is the image of the original time interval. -/
theorem coe_compactPathPrefix_eq_image_Icc {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0) :
    (compactPathPrefix w T : Set E) = w '' Icc 0 T := by
  rw [coe_compactPathPrefix]
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨(u : ℝ) * (T : ℝ), mul_nonneg u.property.1 T.property⟩, ?_, ?_⟩
    · constructor
      · exact zero_le
      · apply NNReal.coe_le_coe.mp
        exact mul_le_of_le_one_left T.property u.property.2
    · rfl
  · rintro ⟨s, hs, rfl⟩
    have hscale : (fun t : ℝ => t * (T : ℝ)) '' Icc (0 : ℝ) 1 =
        Icc 0 (T : ℝ) := by
      simpa only [zero_mul, one_mul] using
        (image_mul_right_Icc (a := (0 : ℝ)) (b := 1) (c := (T : ℝ))
          (by norm_num) T.property)
    have hs' : (s : ℝ) ∈ (fun t : ℝ => t * (T : ℝ)) '' Icc 0 1 := by
      rw [hscale]
      exact ⟨s.property, NNReal.coe_le_coe.mpr hs.2⟩
    obtain ⟨u, hu, hu_eq⟩ := hs'
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [normalizedPathPrefix_apply]
    congr 1
    exact Subtype.ext hu_eq

/-- A stopped path has the original trace up to its finite stopping time. -/
theorem coe_compactPathPrefix_stoppedPath {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0∞) (hT : T ≠ ∞) :
    (compactPathPrefix (stoppedPath T w) T.toNNReal : Set E) =
      w '' Icc 0 T.toNNReal := by
  rw [coe_compactPathPrefix_eq_image_Icc]
  apply Set.image_congr
  intro s hs
  rw [stoppedPath_apply, min_eq_left]
  · simp
  · rw [← ENNReal.coe_toNNReal hT]
    exact ENNReal.coe_le_coe.mpr hs.2

end LatticeProb
