/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonalUpperBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.InfimumFour




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

private theorem rectLen_eq_admInf (ξ : ℝ) (f : ℂ → ℝ)
    (R : DDDF.MarkedRect) :
    DDDF.rectLen ξ f R =
      ⨅ P : {P : ℝ → ℂ // DDDF.AdmPath R.toSet R.side₁ R.side₂ P},
        lfppLen ξ f P.1 := by
  rw [DDDF.rectLen, DDDF.crossLenIn_eq_biInf]
  exact (iInf_subtype (f := fun P :
    {P : ℝ → ℂ // DDDF.AdmPath R.toSet R.side₁ R.side₂ P} =>
      lfppLen ξ f P.1)).symm

theorem polyAnnularCost_le_four_rectLen (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : ℂ → ℝ) (hf : Continuous f)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hfc : ContinuousOn (fun z => fderiv ℝ f z) gradientBox) :
    Exponent.PolygonalCost.polyAnnularCost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*gradientSup f))) *
        (DDDF.rectLen ξ f (DDDF.sB (0,0)) +
          DDDF.rectLen ξ f (DDDF.sT (0,0)) +
          DDDF.rectLen ξ f (DDDF.sL (0,0)) +
          DDDF.rectLen ξ f (DDDF.sR (0,0))) := by
  let C := ENNReal.ofReal ((5/4:ℝ)*Real.exp
    (32*Real.sqrt 2*ξ*((a:ℝ)*gradientSup f)))
  have hC0 : C ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
  rw [rectLen_eq_admInf, rectLen_eq_admInf,
    rectLen_eq_admInf, rectLen_eq_admInf]
  exact le_mul_four_iInf (Exponent.PolygonalCost.polyAnnularCost ξ f) C hC0 hCt
    (fun B : {P : ℝ → ℂ // DDDF.AdmPath (DDDF.sB (0,0)).toSet
        (DDDF.sB (0,0)).side₁ (DDDF.sB (0,0)).side₂ P} => lfppLen ξ f B.1)
    (fun T : {P : ℝ → ℂ // DDDF.AdmPath (DDDF.sT (0,0)).toSet
        (DDDF.sT (0,0)).side₁ (DDDF.sT (0,0)).side₂ P} => lfppLen ξ f T.1)
    (fun L : {P : ℝ → ℂ // DDDF.AdmPath (DDDF.sL (0,0)).toSet
        (DDDF.sL (0,0)).side₁ (DDDF.sL (0,0)).side₂ P} => lfppLen ξ f L.1)
    (fun R : {P : ℝ → ℂ // DDDF.AdmPath (DDDF.sR (0,0)).toSet
        (DDDF.sR (0,0)).side₁ (DDDF.sR (0,0)).side₂ P} => lfppLen ξ f R.1)
    (fun B T L R => polyAnnularCost_le_fourBand_fixed a ha0 ha ξ hξ f hf
      hfd hfc B.2 T.2 L.2 R.2)


end SupercriticalLQGUniqueness.Exponent.InwardMap
