/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicScaleCoupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBandAdd
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L37V1

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

def dg20ScaledNoise {Ω : Type} (r : ℝ) (hr : 0 < r)
    (W : WNSpace → Ω → ℝ) : WNSpace → Ω → ℝ :=
  fun f ω => W (LQGMetric.DG.wnScale hr 0 f) ω

theorem dg20_isWhiteNoise_scaled
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (r : ℝ) (hr : 0 < r) : IsWhiteNoise P (dg20ScaledNoise r hr W) := by
  exact LQGMetric.DG.isWhiteNoise_comp hW (LQGMetric.DG.wnScale hr 0)

theorem dg20_phi_scaled_pathwise
    {Ω : Type} (W : WNSpace → Ω → ℝ)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (b : ℝ) (x : ℂ) (ω : Ω) :
    phi (dg20ScaledNoise r hr W) a b x ω =
      phi W (r * a) (r * b) ((r : ℂ) * x) ω := by
  simp only [phi, dg20ScaledNoise, LQGMetric.DG.wnScale_phiKernelL2 hr 0 ha b x,
    LQGMetric.DG.affineC, add_zero]

 

theorem dg20_phiVer_scaled_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    {r a b : ℝ} (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, ∀ x : ℂ,
      phiVer (dg20ScaledNoise r hr W) P a b x ω =
        phiVer W P (r * a) (r * b) ((r : ℂ) * x) ω := by
  have hW' := dg20_isWhiteNoise_scaled P W hW r hr
  have h₁ := isPhiVersion_phiVer hW' ha hab
  have h₂ := isPhiVersion_phiVer hW (mul_pos hr ha)
    (mul_le_mul_of_nonneg_left hab hr.le)
  refine ae_eq_of_continuous_modification h₁.cont
    (fun ω => (h₂.cont ω).comp (continuous_const.mul continuous_id)) fun x => ?_
  filter_upwards [h₁.ae_eq x, h₂.ae_eq ((r : ℂ) * x)] with ω e₁ e₂
  rw [e₁, e₂, dg20_phi_scaled_pathwise W hr ha b x ω]

end SupercriticalLQGUniqueness.B2.DG20Pt
