import LatticeProb.Prob.CorrelatedBMWedgeArc

/-! # The angle of a closed symmetric wedge -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- A nonzero point in the closure of a symmetric wedge has argument in the
closed angular sector. -/
theorem abs_arg_le_of_mem_closure_symmetricWedge {θ : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) {z : ℂ}
    (hz : z ∈ closure {w : ℂ | (w.re, w.im) ∈
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))})
    (hne : z ≠ 0) : |z.arg| ≤ θ / 2 := by
  let W : Set ℂ := {w | (w.re, w.im) ∈
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hweak : |Real.cos (θ / 2) * z.im| ≤ Real.sin (θ / 2) * z.re := by
    apply closure_minimal (s := W) (t := {w : ℂ |
      |Real.cos (θ / 2) * w.im| ≤ Real.sin (θ / 2) * w.re}) ?_ ?_ hz
    · intro w hw
      change |Real.cos (θ / 2) * w.im| < Real.sin (θ / 2) * w.re at hw
      exact le_of_lt hw
    · exact isClosed_le (by fun_prop) (by fun_prop)
  have hrez : 0 ≤ z.re := (mul_nonneg_iff_of_pos_left hs).1
    (le_trans (abs_nonneg _) hweak)
  have hre : 0 < z.re := by
    by_contra hn
    have hre0 : z.re = 0 := le_antisymm (le_of_not_gt hn) hrez
    have him0 : z.im = 0 := by
      have habs : |Real.cos (θ / 2) * z.im| = 0 := by
        apply le_antisymm _ (abs_nonneg _)
        simpa [hre0] using hweak
      have hmul := abs_eq_zero.mp habs
      exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hc)
    apply hne
    apply Complex.ext <;> simp [hre0, him0]
  have : NeBot (𝓝[W] z) := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hcont : ContinuousAt (fun w : ℂ => |w.arg|) z :=
    (Complex.continuousAt_arg (Or.inl hre)).abs
  apply le_of_tendsto (x := 𝓝[W] z) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have ha := ((CorrelatedBM.mem_openSymmetricWedge_iff_arg hθ0 hθπ w).1 hw).2
  exact (abs_lt.mpr ⟨by linarith [ha.1], ha.2⟩).le

end LatticeProb
