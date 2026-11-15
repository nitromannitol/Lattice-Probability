import Mathlib

/-! # Scaling of power-ratio limits -/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace LatticeProb

/-- Rescaling a positive radial variable by `c` multiplies the limiting
power-ratio constant by `c ^ p`. -/
theorem tendsto_power_ratio_const_mul {f : ℝ → ℝ} {p L c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun s => f s / s ^ p) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r => f (c * r) / r ^ p) (𝓝[>] 0) (𝓝 (L * c ^ p)) := by
  have hscale : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hid.const_mul c
    · exact eventually_nhdsWithin_of_forall fun r hr => mul_pos hc hr
  have h := (hlim.comp hscale).mul_const (c ^ p)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : r ^ p ≠ 0 := (Real.rpow_pos_of_pos hr p).ne'
  have hcp : c ^ p ≠ 0 := (Real.rpow_pos_of_pos hc p).ne'
  change f (c * r) / (c * r) ^ p * c ^ p = f (c * r) / r ^ p
  rw [Real.mul_rpow hc.le hr.le]
  field_simp

end LatticeProb
