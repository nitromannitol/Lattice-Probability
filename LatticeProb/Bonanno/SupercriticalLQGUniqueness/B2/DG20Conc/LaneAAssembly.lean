/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneAAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAInputs

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ} {ξ p Cneg cNeg Cpos cPos : ℝ}

 



theorem laneA_annulus_tails_of_cover (hW : IsWhiteNoise P W)
    {Ucross Uaround E F : Set ℂ} {N : ℝ}
    (hgeom : LaneAInputs.RectAnnulusCover Ucross Uaround E F N)
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
      ENNReal.ofReal N *
        ENNReal.ofReal (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
    P {ω | ENNReal.ofReal (N * (T * LambdaN ξ W P m (ENNReal.ofReal p) *
      ellN ξ W P m (ENNReal.ofReal p))) <
      (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist Uaround E F} ≤
      ENNReal.ofReal N *
        ENNReal.ofReal (Cpos * Real.exp
          (-cPos * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨Js, Jl, us, ul, cs, cl, hJs, hJl, hcover⟩ := hgeom
  have hcountS : (Js.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hJs
  have hcountL : (Jl.card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hJl
  constructor
  · have hsubset : {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω) Ucross E F <
        ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ⊆
        {ω | ∃ j ∈ Js,
          T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 0 (us j) (cs j) 1 3 <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} := by
      intro ω hω
      have hf := (isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω
      change crossLenIn ξ (fun z => phiMN W P 0 m z ω) Ucross E F < _ at hω
      exact (hcover ξ (fun z => phiMN W P 0 m z ω) hf
        (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)) 0).1 hω
    calc
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω) Ucross E F <
          ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
        P {ω | ∃ j ∈ Js,
          T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 0 (us j) (cs j) 1 3 <
            T⁻¹ * ellN ξ W P m (ENNReal.ofReal p)} := measure_mono hsubset
      _ ≤ (Js.card : ℝ≥0∞) * ENNReal.ofReal
        (Cneg * Real.exp (-cNeg * (Real.log T)^2)) :=
          laneA_short_family_tail hW hlow m Js us cs T hT
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal
        (Cneg * Real.exp (-cNeg * (Real.log T)^2)) :=
          mul_le_mul_of_nonneg_right hcountS (zero_le : (0 : ℝ≥0∞) ≤ _)
  · have hsubset : {ω | ENNReal.ofReal (N * (T * LambdaN ξ W P m
          (ENNReal.ofReal p) * ellN ξ W P m (ENNReal.ofReal p))) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist Uaround E F} ⊆
        {ω | ∃ j ∈ Jl,
          T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 0 (ul j) (cl j) 3 1} := by
      intro ω hω
      have hf := (isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω
      change ENNReal.ofReal (N * (T * LambdaN ξ W P m
        (ENNReal.ofReal p) * ellN ξ W P m (ENNReal.ofReal p))) <
        (lfppContMetric ξ (fun z => phiMN W P 0 m z ω) hf).aroundDist Uaround E F at hω
      exact (hcover ξ (fun z => phiMN W P 0 m z ω) hf 0
        (T * LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p))).2 hω
    calc
      P {ω | ENNReal.ofReal (N * (T * LambdaN ξ W P m
            (ENNReal.ofReal p) * ellN ξ W P m (ENNReal.ofReal p))) <
            (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
              ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist Uaround E F} ≤
        P {ω | ∃ j ∈ Jl,
          T * LambdaN ξ W P m (ENNReal.ofReal p) *
            ellN ξ W P m (ENNReal.ofReal p) <
            T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω) 0 (ul j) (cl j) 3 1} :=
          measure_mono hsubset
      _ ≤ (Jl.card : ℝ≥0∞) * ENNReal.ofReal
        (Cpos * Real.exp (-cPos * (Real.log T)^2 /
          Real.log (Real.log T))) :=
          laneA_long_family_tail hW hupp m Jl ul cl T hT
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal
        (Cpos * Real.exp (-cPos * (Real.log T)^2 /
          Real.log (Real.log T))) :=
          mul_le_mul_of_nonneg_right hcountL (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc
