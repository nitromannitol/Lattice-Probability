/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneB_coarse_oscillation_on_annuli
    {ι Ω : Type*} [MeasurableSpace Ω] (K : ℕ) (Y : ℂ → Ω → ℝ) (ω : Ω)
    (hY : ContDiff ℝ 1 (fun x => Y x ω))
    (A : ι → Set ℂ) (v : ι → ℂ) (M : ℝ)
    (hA : ∀ i, A i ⊆ T20D.bigBox)
    (hv : ∀ i, v i ∈ T20D.bigBox)
    (hrad : ∀ i, ∀ z ∈ A i, ‖z - v i‖ ≤ M * (2 : ℝ)⁻¹ ^ K) :
    ∀ i, ∀ z ∈ A i,
      |Y z ω - Y (v i) ω| ≤ M * T20C.Obig K Y ω := by
  intro i z hz
  have hO := T20C.Obig_nonneg K Y ω
  have h := T20D.osc_bigBox_le K hY (hA i hz) (hv i)
  have hpow : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (by positivity)]
  calc
    |Y z ω - Y (v i) ω| ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω * ‖z - v i‖ := h
    _ ≤ (2 : ℝ) ^ K * T20C.Obig K Y ω * (M * (2 : ℝ)⁻¹ ^ K) :=
      mul_le_mul_of_nonneg_left (hrad i z hz) (by positivity)
    _ = M * T20C.Obig K Y ω := by
      calc
        _ = M * T20C.Obig K Y ω * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
        _ = _ := by rw [hpow, mul_one]

end SupercriticalLQGUniqueness.B2.DG20Conc
