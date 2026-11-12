/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.JordanJ1bFinal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanJ1bTop
import LatticeProb.Bonanno.LQGMetric.Topo.SectorMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# J1b and the Jordan-curve / conformal-map facts for filled balls, unconditionally

`gmSector` (P2-GMSEC, `LQGMetric/Topo/Sector*.lean`) discharges the sector lemma, the only
hypothesis of the `_of_sector` results in `JordanJ1bTop.lean` (Miller–Sheffield arXiv:1506.03806
Prop 2.1, `mapmaking_final.tex` l. 570–601; GPS arXiv:2010.07889 Lemma 2.4).
-/

open Set Metric Topology Filter

namespace LQGMetric.GM

/-- **J1b** (local connectivity of filled-ball boundaries), unconditional. -/
theorem gm_j1b : GMJ1b := gm_j1b_of_sector gmSector

/-- **GM.S-Jordan** (GPS Lemma 2.4 for filled balls): the boundary of a filled metric ball of a
length metric with bounded balls is a Jordan curve. -/
theorem gm_filledBall_frontier_isJordanCurve' {D : ContMetric} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hL : D.IsLength) (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) :
    JordanMap.IsJordanCurve (frontier (Blueprint.filledBall D z s)) :=
  gm_filledBall_frontier_isJordanCurve_of_sector gmSector hs hL hbd

/-- **J2** for filled balls: a conformal map from the punctured disc onto the complement of the
filled ball, extending continuously and injectively to the unit circle. -/
theorem gm_filledBall_conformal' {D : ContMetric} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hL : D.IsLength) (hbd : Bornology.IsBounded (Blueprint.ballM D z s)) :
    ∃ Ψ : ℂ → ℂ, ContinuousOn Ψ (closedBall 0 1 \ {0}) ∧ InjOn Ψ (closedBall 0 1 \ {0}) ∧
      DifferentiableOn ℂ Ψ (ball 0 1 \ {0}) ∧
      Ψ '' (ball 0 1 \ {0}) = (Blueprint.filledBall D z s)ᶜ ∧
      Ψ '' sphere 0 1 = frontier (Blueprint.filledBall D z s) ∧
      Tendsto Ψ (𝓝[≠] 0) (Bornology.cobounded ℂ) :=
  gm_filledBall_conformal_of_sector gmSector hs hL hbd

end LQGMetric.GM
