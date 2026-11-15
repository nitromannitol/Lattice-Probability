import LatticeProb.Analysis.WedgeArcIntegral

/-! # Relative openness of a circular arc -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A symmetric arc shorter than a full turn is relatively open in the unit circle. -/
theorem isOpen_unitCircle_symmetric_arc {θ : ℝ} (hθ' : θ < 2 * Real.pi) :
    IsOpen ((Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2))) := by
  let U : Set ℂ := Complex.slitPlane ∩ Complex.arg ⁻¹' Ioo (-θ / 2) (θ / 2)
  have hU : IsOpen U :=
    Complex.continuousOn_arg.isOpen_inter_preimage Complex.isOpen_slitPlane isOpen_Ioo
  have heq : (Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹'
      (circleMap 0 1 '' Ioo (-θ / 2) (θ / 2)) =
      (Subtype.val : {z : ℂ // ‖z‖ = 1} → ℂ) ⁻¹' U := by
    ext z
    constructor
    · rintro ⟨x, hx, hxz⟩
      have hxarg : (circleMap 0 1 x).arg = x :=
        arg_circleMap_mem_wedge (by linarith) ⟨hx.1, hx.2.le⟩
      have hzarg : z.val.arg = x := by rw [← hxz, hxarg]
      have hz0 : z.val ≠ 0 := by
        intro h
        have := z.property
        simp [h] at this
      refine ⟨Complex.mem_slitPlane_iff_arg.mpr ⟨?_, hz0⟩, ?_⟩
      · rw [hzarg]; linarith [hx.2]
      · simpa only [mem_preimage, hzarg] using hx
    · rintro ⟨_, hzarg⟩
      refine ⟨z.val.arg, hzarg, ?_⟩
      simpa only [circleMap_zero, Complex.ofReal_one, one_mul, z.property] using
        (Complex.norm_mul_exp_arg_mul_I z.val)
  rw [heq]
  exact hU.preimage continuous_subtype_val

end LatticeProb
