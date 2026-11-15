import LatticeProb.Prob.BrownianBoundedWedgePowerExit
import LatticeProb.Prob.BrownianOpenExitIntegrable
import LatticeProb.Analysis.WedgePowerMiddleSector

/-! # Brownian exit through the middle of a wedge -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- A power-profile bound on exit at large radius through the middle half of a
symmetric wedge. The initial point may lie on the boundary of the wedge. -/
theorem brownian_wedge_middle_exit_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {U : Set (Euc 2)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {θ r : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) (hr : 0 < r) :
    let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
    let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
    x ∈ closure W →
    (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) *
      P.real {ω | r ≤ ‖J (B (openExitTime B (U ∩ W) ω).toNNReal ω)‖ ∧
        |(J (B (openExitTime B (U ∩ W) ω).toNNReal ω)).arg| ≤ θ / 4} ≤
      (J x ^ ((Real.pi / θ : ℝ) : ℂ)).re := by
  dsimp only
  intro hx
  have := hB.isProbabilityMeasure
  let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
  let Wc : Set ℂ := {z | (z.re, z.im) ∈
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
  let W : Set (Euc 2) := J ⁻¹' Wc
  let V : Set (Euc 2) := U ∩ W
  let C : Euc 2 → ℂ := fun y => ((max 0 (J y).re : ℝ) : ℂ) + ((J y).im : ℂ) * Complex.I
  let f : Euc 2 → ℝ := fun y => (C y ^ ((Real.pi / θ : ℝ) : ℂ)).re
  let Z : Ω → Euc 2 := fun ω => B (openExitTime B V ω).toNNReal ω
  let H : Ω → ℝ := fun ω => (J (Z ω) ^ ((Real.pi / θ : ℝ) : ℂ)).re
  have hp : 0 < Real.pi / θ := div_pos Real.pi_pos hθ0
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
  have hprofile := wedge_re_cpow_continuousOn_nonneg_closure hθ0 hθπ
  have hnonneg : 0 ≤ᵐ[P] H := hZ.mono (fun ω hω => hprofile.2 _ hω)
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
    ((Real.sqrt 2 / 2) * r ^ (Real.pi / θ))
  have hsub : {ω | r ≤ ‖J (Z ω)‖ ∧ |(J (Z ω)).arg| ≤ θ / 4} ⊆
      {ω | (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) ≤ H ω} := by
    intro ω hω
    have hn : J (Z ω) ≠ 0 := by
      intro he
      have : ‖J (Z ω)‖ = 0 := by rw [he, norm_zero]
      linarith [hω.1]
    exact wedge_re_cpow_lower_bound_middle_sector hθ0 hr.le hn hω.1 hω.2
  have hm := measureReal_mono hsub (μ := P)
  have hc : 0 ≤ (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) := by positivity
  have hid := integral_openExit_symmetricWedge_re_cpow hB hU hUb hθ0 hθπ
  change (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) *
    P.real {ω | r ≤ ‖J (Z ω)‖ ∧ |(J (Z ω)).arg| ≤ θ / 4} ≤ _
  calc
    _ ≤ (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) *
        P.real {ω | (Real.sqrt 2 / 2) * r ^ (Real.pi / θ) ≤ H ω} :=
          mul_le_mul_of_nonneg_left hm hc
    _ ≤ ∫ ω, H ω ∂P := hmark
    _ = (J x ^ ((Real.pi / θ : ℝ) : ℂ)).re := hid

end LatticeProb
