/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneASource at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 
def laneA_upperConstant (G C c : ℝ) : ℝ :=
  G * C + Real.exp ((c / 4) *
    ((Real.log (max (3 * G) (G^2)))^2 / Real.log (Real.log 3)))

 



theorem laneA_source_tails_of_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ p Cneg cNeg Cpos cPos : ℝ}
    {Ucross Uaround E F : Set ℂ} {R G : ℝ}
    (hR : 1 ≤ R) (hG : 1 ≤ G)
    (hgeom : LaneAInputs.RectAnnulusCover Ucross Uaround E F (G * R))
    (hCpos : 0 < Cpos) (hcpos : 0 < cPos)
    (hlow : ∀ (m : ℕ) (T : ℝ), 3 < T →
      P {ω | lenObs ξ (phiMN W P 0 m) (rectAB 1 3) ω <
        T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)))
    (hupp : ∀ (m : ℕ) (T : ℝ), 3 < T →
      P {ω | T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) <
        lenObs ξ (phiMN W P 0 m) (rectAB 3 1) ω} ≤
        ENNReal.ofReal (Cpos * Real.exp
          (-cPos * (Real.log T)^2 / Real.log (Real.log T))))
    (m : ℕ) (T : ℝ) (hT : 3 < T) :
    P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω) Ucross E F <
      ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
      ENNReal.ofReal ((G * Cneg) * R *
        Real.exp (-cNeg * (Real.log T)^2)) ∧
    P {ω | ENNReal.ofReal ((T * R) *
      (LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p))) <
      (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist Uaround E F} ≤
      ENNReal.ofReal (laneA_upperConstant G Cpos cPos * R *
        Real.exp (-(cPos / 4) * (Real.log T)^2 /
          Real.log (Real.log T))) := by
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hraw := laneA_annulus_tails_of_cover hW hgeom hlow hupp m T hT
  constructor
  · calc
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω) Ucross E F <
        ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
        ENNReal.ofReal (G * R) * ENNReal.ofReal
          (Cneg * Real.exp (-cNeg * (Real.log T)^2)) := hraw.1
      _ = ENNReal.ofReal ((G * R) *
        (Cneg * Real.exp (-cNeg * (Real.log T)^2))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal ((G * Cneg) * R *
        Real.exp (-cNeg * (Real.log T)^2)) := by congr 1; ring
  · let A : Ω → ℝ≥0∞ := fun ω =>
      (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist Uaround E F
    let L : ℝ := LambdaN ξ W P m (ENNReal.ofReal p) *
      ellN ξ W P m (ENNReal.ofReal p)
    have hrawUpper : ∀ s : ℝ, 3 < s →
        P {ω | ENNReal.ofReal ((G * R) * (s * L)) < A ω} ≤
          ENNReal.ofReal (G * R) * ENNReal.ofReal
            (Cpos * Real.exp (-cPos * (Real.log s)^2 /
              Real.log (Real.log s))) := by
      intro s hs
      simpa only [A, L, mul_assoc] using
        (laneA_annulus_tails_of_cover hW hgeom hlow hupp m s hs).2
    have h := laneA_rescale_upper_tail P A L R G Cpos cPos hR hG hCpos hcpos
      hrawUpper T hT
    simpa only [A, L, laneA_upperConstant] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
