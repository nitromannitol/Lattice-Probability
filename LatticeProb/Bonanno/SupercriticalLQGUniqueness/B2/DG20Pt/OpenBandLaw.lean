/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.OpenBandLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.BandLaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.OpenCrossingLaw

 




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem measure_band_crossing_open_dilate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (U : Opens ℂ) (A B : Set ℂ)
    {k n : ℕ} (hkn : k ≤ n)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    let r : ℝ := (2 : ℝ)⁻¹ ^ k
    let F : ℂ → ℂ := fun z => (r : ℂ) * z
    P {ω | crossLenIn ξ (fun z => phiMN W P k n z ω)
          (F '' U) (F '' A) (F '' B) ∈ S} =
      P {ω | ENNReal.ofReal r *
          crossLenIn ξ (fun z => phiMN W P 0 (n - k) z ω) U A B ∈ S} := by
  dsimp
  let r : ℝ := (2 : ℝ)⁻¹ ^ k
  have hr : 0 < r := by dsimp [r]; positivity
  let F : ℂ → ℂ := fun z => (r : ℂ) * z
  have hφ := isPhiVersion_phiMN hW hkn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - k))
  let Y₁ : ℂ → Ω → ℝ := fun z ω => phiMN W P k n (F z) ω
  have hlaw : P.map (fun ω z => Y₁ z ω) =
      P.map (fun ω z => phiMN W P 0 (n - k) z ω) := by
    simpa only [Y₁, F, r] using map_phiMN_dilate_eq P W hW hkn
  let T : Set ℝ≥0∞ := {v | ENNReal.ofReal r * v ∈ S}
  have hT : MeasurableSet T := (measurable_const.mul measurable_id) hS
  have hleft : {ω | crossLenIn ξ (fun z => phiMN W P k n z ω)
        (F '' U) (F '' A) (F '' B) ∈ S} =
      {ω | crossLenIn ξ (fun z => Y₁ z ω) U A B ∈ T} := by
    ext ω
    simp only [Set.mem_ofPred_eq, T, Y₁, F]
    rw [crossLenIn_image_mul ξ (fun z => phiMN W P k n z ω) U A B hr]
  rw [hleft]
  exact measure_crossLenIn_open_eq P P ξ U A B
    (fun ω => (hφ.cont ω).comp (continuous_const.mul continuous_id))
    (fun z => hφ.meas _) hφ0.cont hφ0.meas hlaw hT

end SupercriticalLQGUniqueness.B2.DG20Pt
