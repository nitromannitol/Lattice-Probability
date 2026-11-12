/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Sup1

/-!
# DDDF Theorem 1 (2) for `D = (−1,2)²` (task P2-DDDF6f)

DDDF = arXiv:1904.08021, `tightness.tex` l. 160–161, 1497–1510. `DDDFThm1_2Sq` is
`Blueprint.DDDFThm1_2` for the one domain `D = (−1,2)²` that DFGPS uses (T:877–881, through
`DFGPS.zb_step'`, which reads only the tightness at that `D`). `dddfThm1_2Sq_of` proves it from
DDDF Theorem 1 (1), DDDF Proposition 29 on the square and DDDF (5.54) (proved from the DG
inputs in `S6DGLow`): continuity is `S6Thm.cont_sqLen`, tightness `S6Thm.s6_thm12_tight_sq` with
the sup bound `S6Sup.s6_hsup`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF

open Blueprint HeatSq WhiteNoise

/-- **DDDF Theorem 1 (2)** (DD:160–161) for `D = (−1,2)²` (`Blueprint.DDDFThm1_2` with
`D := sqOpens (-1) 3`). -/
def DDDFThm1_2Sq : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (W' : WNSpace → Ω' → ℝ),
      IsWhiteNoise P' W' →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ), IsZBGFFProcessExt (sqOpens (-1) 3) Xh P →
    ∀ Y : ℝ → ℂ → Ω → ℝ,
      (∀ δ ∈ Ioo (0 : ℝ) 1,
        IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) →
      let X : ℝ → Ω → C(closedUnitSquare × closedUnitSquare, ℝ) := fun δ ω =>
        sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ)) (fun x => Y δ x ω)
      (∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω, Continuous fun p : closedUnitSquare × closedUnitSquare =>
        (lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ))⁻¹ *
          lenMetricOn (xiGamma γ) (fun x => Y δ x ω) closedUnitSquare p.1 p.2) ∧
      IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map (X δ)}

/-- **DDDF Theorem 1 (2) on `(−1,2)²`** from DDDF Theorem 1 (1), Proposition 29 on the square
and (5.54). -/
theorem dddfThm1_2Sq_of (h11 : DDDFThm1_1) (h29 : DDDFProp29Sq)
    (h554 : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W → S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P) :
    DDDFThm1_2Sq := by
  intro γ hγ hγ2 Ω' _ P' W' hW' Ω _ P _ Xh hX Y hY
  refine ⟨fun δ hδ ω => S6Thm.cont_sqLen ((hY δ hδ).1 ω) _, ?_⟩
  exact S6Thm.s6_thm12_tight_sq h11 h29 hγ hγ2 P' W' hW' (h554 γ hγ hγ2 P' W' hW') P Xh hX Y hY
    (S6Sup.s6_hsup P Xh hX Y hY)

end DDDF
end LQGMetric
