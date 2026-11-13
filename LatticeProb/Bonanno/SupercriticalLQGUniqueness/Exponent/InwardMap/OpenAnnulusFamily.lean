/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.OpenAnnulusFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.FourBandImage




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric LQGMetric.LFPP

theorem fourBand_open_polygon_le (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ) (hf : Continuous f)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    {B T L R : ℝ → ℂ}
    (hB : DDDF.AdmPath (DDDF.sB (0, 0)).toSet
      (DDDF.sB (0, 0)).side₁ (DDDF.sB (0, 0)).side₂ B)
    (hT : DDDF.AdmPath (DDDF.sT (0, 0)).toSet
      (DDDF.sT (0, 0)).side₁ (DDDF.sT (0, 0)).side₂ T)
    (hL : DDDF.AdmPath (DDDF.sL (0, 0)).toSet
      (DDDF.sL (0, 0)).side₁ (DDDF.sL (0, 0)).side₂ L)
    (hR : DDDF.AdmPath (DDDF.sR (0, 0)).toSet
      (DDDF.sR (0, 0)).side₁ (DDDF.sR (0, 0)).side₂ R)
    {η : ℝ} (hη : 0 < η) :
    ∃ P : Exponent.PolygonalCost.RatPolygonFamily, P.Admitted ∧
      P.cost ξ f ≤ ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
        (lfppLen ξ f B + lfppLen ξ f T +
          lfppLen ξ f L + lfppLen ξ f R + ENNReal.ofReal η) := by
  obtain ⟨F, _, hcost⟩ :=
    Exponent.PolygonalCost.exists_rational_four_band_le hf hB hT hL hR hη
  refine ⟨mappedFourBandFamily a F,
    mappedFourBandFamily_admitted a ha0 ha ξ f F, ?_⟩
  calc
    (mappedFourBandFamily a F).cost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) * F.cost :=
      mappedFourBandFamily_cost_le a ha0.le ha ξ G hξ hG0 f hfd hG F
    _ ≤ _ := by simpa only [mul_comm] using
      (mul_le_mul_left hcost (ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G)))))

theorem polyAnnularCost_le_fourBand (a : ℚ) (ha0 : 0 < a)
    (ha : (a:ℝ) ≤ 1/256) (ξ G : ℝ) (hξ : 0 ≤ ξ) (hG0 : 0 ≤ G)
    (f : ℂ → ℝ) (hf : Continuous f)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    {B T L R : ℝ → ℂ}
    (hB : DDDF.AdmPath (DDDF.sB (0, 0)).toSet
      (DDDF.sB (0, 0)).side₁ (DDDF.sB (0, 0)).side₂ B)
    (hT : DDDF.AdmPath (DDDF.sT (0, 0)).toSet
      (DDDF.sT (0, 0)).side₁ (DDDF.sT (0, 0)).side₂ T)
    (hL : DDDF.AdmPath (DDDF.sL (0, 0)).toSet
      (DDDF.sL (0, 0)).side₁ (DDDF.sL (0, 0)).side₂ L)
    (hR : DDDF.AdmPath (DDDF.sR (0, 0)).toSet
      (DDDF.sR (0, 0)).side₁ (DDDF.sR (0, 0)).side₂ R)
    {η : ℝ} (hη : 0 < η) :
    Exponent.PolygonalCost.polyAnnularCost ξ f ≤
      ENNReal.ofReal ((5/4:ℝ)*Real.exp
        (32*Real.sqrt 2*ξ*((a:ℝ)*G))) *
        (lfppLen ξ f B + lfppLen ξ f T +
          lfppLen ξ f L + lfppLen ξ f R + ENNReal.ofReal η) := by
  obtain ⟨P, hP, hcost⟩ := fourBand_open_polygon_le a ha0 ha ξ G hξ hG0
    f hf hfd hG hB hT hL hR hη
  exact (iInf_le_of_le P (iInf_le _ hP)).trans hcost


end SupercriticalLQGUniqueness.Exponent.InwardMap
