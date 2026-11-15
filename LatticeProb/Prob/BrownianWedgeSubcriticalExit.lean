import LatticeProb.Prob.BrownianWedgePositivePowerExit
import LatticeProb.Prob.BrownianOpenExitIntegrable
import LatticeProb.Analysis.WedgeSubcriticalPower
import LatticeProb.Analysis.WedgeClosureAngle

/-! # Brownian exit from a wedge with subcritical power -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A subcritical power-profile bound on exit at large radius from a
symmetric wedge. The initial point may lie on the boundary of the wedge. -/
theorem brownian_wedge_subcritical_exit_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {θ p r : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) (hp : 0 < p) (hpθ : p * θ < Real.pi) (hr : 0 < r) :
    let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
    let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
    x ∈ closure W →
    Real.cos (p * (θ / 2)) * r ^ p *
      P.real {ω | r ≤ ‖J (B (openExitTime B (U ∩ W) ω).toNNReal ω)‖} ≤
      (J x ^ (p : ℂ)).re := by
  dsimp only
  intro hx
  have := hB.isProbabilityMeasure
  let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
  let Wc : Set ℂ := {z | (z.re, z.im) ∈
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
  let W : Set (Euc 2) := J ⁻¹' Wc
  let V : Set (Euc 2) := U ∩ W
  let C : Euc 2 → ℂ := fun y => ((max 0 (J y).re : ℝ) : ℂ) + ((J y).im : ℂ) * Complex.I
  let f : Euc 2 → ℝ := fun y => (C y ^ (p : ℂ)).re
  let Z : Ω → Euc 2 := fun ω => B (openExitTime B V ω).toNNReal ω
  let H : Ω → ℝ := fun ω => (J (Z ω) ^ (p : ℂ)).re
  have hJ : Continuous J := Complex.orthonormalBasisOneI.repr.symm.continuous
  have hW : IsOpen W := by
    apply (CorrelatedBM.isOpen_openSymmetricWedge _ _).preimage
    exact (Complex.continuous_re.comp hJ).prodMk (Complex.continuous_im.comp hJ)
  have hVo : IsOpen V := hU.inter hW
  have hVb : Bornology.IsBounded V := hUb.subset inter_subset_left
  have hxW : x ∈ closure W := hx
  have hZ : ∀ᵐ ω ∂P, J (Z ω) ∈ closure Wc := by
    filter_upwards [hB.start, hB.cont, ae_openExitTime_ne_top (by norm_num) hB hVb]
      with ω hstart hcont hfin
    have hz : Z ω ∈ closure W := by
      by_cases hxin : x ∈ V
      · exact closure_mono inter_subset_right (frontier_subset_closure
          (openExitTime_mem_frontier hVo hcont (by rwa [hstart]) hfin))
      · have ht : openExitTime B V ω = 0 :=
          openExitTime_eq_zero_of_not_mem (by rwa [hstart])
        simpa [Z, ht, hstart] using hxW
    exact map_mem_closure hJ hz (fun _ hy => hy)
  have hnonneg : 0 ≤ᵐ[P] H := by
    filter_upwards [hZ] with ω hω
    by_cases hz : J (Z ω) = 0
    · change 0 ≤ (J (Z ω) ^ (p : ℂ)).re
      rw [hz, re_zero_cpow_of_pos hp]
    · have ha := abs_arg_le_of_mem_closure_symmetricWedge hθ0 hθπ hω hz
      have hb := wedge_re_cpow_lower_bound_subcritical hθ0 hp hpθ
        (show (0 : ℝ) ≤ 0 by rfl) hz (norm_nonneg _) ha
      simpa [H, Real.zero_rpow (ne_of_gt hp)] using hb
  have hreal : ∀ z ∈ closure Wc, 0 ≤ z.re := by
    apply closure_minimal (s := Wc)
    · intro z hz
      have hs : 0 < Real.sin (θ / 2) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      change |Real.cos (θ / 2) * z.im| < Real.sin (θ / 2) * z.re at hz
      exact (mul_pos_iff_of_pos_left hs).1 (lt_of_le_of_lt (abs_nonneg _) hz) |>.le
    · exact isClosed_le continuous_const Complex.continuous_re
  have hC : Continuous C := by dsimp [C]; fun_prop
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (continuousAt_re_cpow_of_nonneg_re hp (show 0 ≤ (C y).re by simp [C])).comp
      hC.continuousAt
  have hEq : ∀ᵐ ω ∂P, f (Z ω) = H ω := by
    filter_upwards [hZ] with ω hω
    have hc : C (Z ω) = J (Z ω) := by
      apply Complex.ext <;> simp [C, max_eq_right (hreal _ hω)]
    simp only [f, H, hc]
  have hint : Integrable H P :=
    (integrable_continuous_openExit (by norm_num) hB hVo hVb hf).congr hEq
  have hmark := mul_meas_ge_le_integral_of_nonneg hnonneg hint
    (Real.cos (p * (θ / 2)) * r ^ p)
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | r ≤ ‖J (Z ω)‖} →
      ω ∈ {ω | Real.cos (p * (θ / 2)) * r ^ p ≤ H ω} := by
    filter_upwards [hZ] with ω hω hrω
    have hn : J (Z ω) ≠ 0 := by
      intro he
      have : ‖J (Z ω)‖ = 0 := by rw [he, norm_zero]
      linarith
    exact wedge_re_cpow_lower_bound_subcritical hθ0 hp hpθ hr.le hn hrω
      (abs_arg_le_of_mem_closure_symmetricWedge hθ0 hθπ hω hn)
  have hm : P.real {ω | r ≤ ‖J (Z ω)‖} ≤
      P.real {ω | Real.cos (p * (θ / 2)) * r ^ p ≤ H ω} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hc : 0 ≤ Real.cos (p * (θ / 2)) * r ^ p := by
    have hc' : 0 < Real.cos (p * (θ / 2)) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
    exact mul_nonneg hc'.le (Real.rpow_nonneg hr.le _)
  have hid := integral_openExit_symmetricWedge_re_cpow_of_pos hB hU hUb hθ0 hθπ hp
  change Real.cos (p * (θ / 2)) * r ^ p *
    P.real {ω | r ≤ ‖J (Z ω)‖} ≤ _
  calc
    _ ≤ Real.cos (p * (θ / 2)) * r ^ p *
        P.real {ω | Real.cos (p * (θ / 2)) * r ^ p ≤ H ω} :=
          mul_le_mul_of_nonneg_left hm hc
    _ ≤ ∫ ω, H ω ∂P := hmark
    _ = (J x ^ (p : ℂ)).re := hid

end LatticeProb
