/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGaussianError at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CMom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_Xbig_gaussian_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x : ℝ, 0 < x →
      P {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
          (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} ≤
        ENNReal.ofReal (C * Real.exp (-(c * x ^ 2))) := by
  let W' : WNSpace → Ω → ℝ := fun f => W (motionL2 1 T20C.cBig f)
  have hW' : IsWhiteNoise P W' := isWhiteNoise_isometry hW _
  have hφ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y,
      phiMN W P 0 n (y + T20C.cBig) ω = phiMN W' P 0 n y ω := by
    refine ae_all_iff.mpr fun n => ?_
    have h1 := isPhiVersion_phiMN hW (Nat.zero_le n)
    have h2 := isPhiVersion_phiMN hW' (Nat.zero_le n)
    refine T20C.ae_forall_eq_of_cont
      (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const))
      h2.cont fun y => ?_
    have e := phi_motion W (a := (2 : ℝ)⁻¹ ^ n) (by positivity)
      ((2 : ℝ)⁻¹ ^ 0) 1 y T20C.cBig
    simp only [Circle.coe_one, one_mul] at e
    exact (h1.ae_eq (y + T20C.cBig)).trans
      (by rw [e]; exact (h2.ae_eq y).symm)
  have hψ : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y,
      psiMN Q W P 0 n (y + T20C.cBig) ω = psiMN Q W' P 0 n y ω := by
    refine ae_all_iff.mpr fun n => ?_
    have h1 := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    have h2 := isPsiVersion_psiMN (Q := Q) hW' (Nat.zero_le n)
    refine T20C.ae_forall_eq_of_cont
      (fun ω => (h1.cont ω).comp (continuous_id.add continuous_const))
      h2.cont fun y => ?_
    have e : psi Q W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (y + T20C.cBig) =
        psi Q W' ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) y := by
      have e1 := psiKernelL2_motion Q (a := (2 : ℝ)⁻¹ ^ n) (by positivity)
        ((2 : ℝ)⁻¹ ^ 0) 1 y T20C.cBig
      simp only [Circle.coe_one, one_mul] at e1
      funext ω
      simp only [psi, e1, W']
    exact (h1.ae_eq (y + T20C.cBig)).trans
      (by rw [e]; exact (h2.ae_eq y).symm)
  obtain ⟨C, c, hC, hc, htail⟩ := dddf_prop5_XAB hW' Q 5 5
  refine ⟨C, c, hC, hc, fun x hx => ?_⟩
  have hevent : {ω | ENNReal.ofReal x ≤
      XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
        (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5} =ᵐ[P]
      {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W' P 0 n y ω)
          (fun n y => psiMN Q W' P 0 n y ω) 5 5} := by
    filter_upwards [hφ, hψ] with ω h1 h2
    simp only [h1, h2]
  exact (measure_congr hevent).trans_le (htail x hx)

end SupercriticalLQGUniqueness.B2.DG20Conc
