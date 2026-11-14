/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateNormalized at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36UpperScale
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20TranslB
import LatticeProb.Bonanno.NV1Evidence
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Iface.Statements

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem dg20_heat_translate_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (a : ℂ) (ε : ℝ) (hε : 0 < ε) :
    let g : Ω → DistC := fun ω =>
      addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)
    IsNormalizedWholePlaneGFF g P ∧
      ∀ᵐ ω ∂P, ∀ z,
        heatMollify ε (g ω) z =
          heatMollify ε (h ω) (z + a) - circleAvg (h ω) 1 a := by
  dsimp
  have hg : IsNormalizedWholePlaneGFF
      (fun ω => addConst (affineComp 1 a (h ω)) (-circleAvg (h ω) 1 a)) P :=
    isNormalizedWholePlaneGFF_iff_old.mpr
      (L36.isNormalizedWPGFF_rescale
        (isNormalizedWholePlaneGFF_iff_old.mp hh) one_pos a)
  refine ⟨hg, ?_⟩
  have hT := hh.1.affineComp one_pos a
  filter_upwards [ae_heatMollify_translate hh.1 hε.ne' a,
    hT.ae_tendstoLocallyUniformly_heatMollify ε hε.ne'] with ω htr hconv
  intro z
  rw [heatMollify_addConst_of_tendsto hε.ne'
    ((tendstoLocallyUniformlyOn_univ.2 hconv.1).tendsto_at (Set.mem_univ z)),
    htr z]
  ring

end SupercriticalLQGUniqueness.B2.DG20Pt
