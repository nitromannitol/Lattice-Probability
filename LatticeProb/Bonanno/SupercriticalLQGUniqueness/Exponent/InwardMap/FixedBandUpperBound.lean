/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.FixedBandUpperBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.EtaLimit




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem polyAnnularCost_le_fourBand_fixed (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox)
    {B T L R : ℝ → ℂ}
    (hB : DDDF.AdmPath (DDDF.sB (0, 0)).toSet
      (DDDF.sB (0, 0)).side₁ (DDDF.sB (0, 0)).side₂ B)
    (hT : DDDF.AdmPath (DDDF.sT (0, 0)).toSet
      (DDDF.sT (0, 0)).side₁ (DDDF.sT (0, 0)).side₂ T)
    (hL : DDDF.AdmPath (DDDF.sL (0, 0)).toSet
      (DDDF.sL (0, 0)).side₁ (DDDF.sL (0, 0)).side₂ L)
    (hR : DDDF.AdmPath (DDDF.sR (0, 0)).toSet
      (DDDF.sR (0, 0)).side₁ (DDDF.sR (0, 0)).side₂ R) :
    Exponent.PolygonalCost.polyAnnularCost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*gradientSup f))) *
        (lfppLen ξ f B + lfppLen ξ f T +
          lfppLen ξ f L + lfppLen ξ f R) := by
  let C : ℝ := (5/4:ℝ)*Real.exp
    (32*Real.sqrt 2*ξ*((a:ℝ)*gradientSup f))
  have hC : 0 < C := by dsimp [C]; positivity
  apply le_mul_of_forall_eta _ _ C hC
  intro η hη
  exact polyAnnularCost_le_fourBand a ha0 ha ξ (gradientSup f) hξ
    (gradientSup_nonneg f hfc) f hf hfd (gradientSup_bound f hfc)
    hB hT hL hR hη


end SupercriticalLQGUniqueness.Exponent.InwardMap
