import LatticeProb.Prob.CorrelatedBMJointWindowTransfer

/-! # Whitening correlated Brownian barriers -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The first coordinate and the whitened second coordinate are independent
standard Brownian motions when the correlation is strictly between -1 and 1. -/
theorem whitened_coneComb_brownian_independent {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (hρlo : -1 < lrCov γ 0 1)
    (hρhi : lrCov γ 0 1 < 1) :
    let ρ := lrCov γ 0 1
    let σ := Real.sqrt (1 - ρ ^ 2)
    IsBrownianReal (fun v : ℝ≥0 => coneComb 1 0 v 0) μ ∧
    IsBrownianReal (fun v : ℝ≥0 => coneComb (-ρ / σ) (1 / σ) v 0) μ ∧
    IndepFun (fun ω (v : ℝ≥0) => coneComb 1 0 v 0 ω)
      (fun ω (v : ℝ≥0) => coneComb (-ρ / σ) (1 / σ) v 0 ω) μ := by
  dsimp only
  let ρ := lrCov γ 0 1
  let σ := Real.sqrt (1 - ρ ^ 2)
  have hσsq : σ * σ = 1 - ρ ^ 2 := by
    apply Real.mul_self_sqrt
    nlinarith [mul_pos (show 0 < ρ + 1 by linarith) (show 0 < 1 - ρ by linarith)]
  have hσ : 0 < σ := by
    apply Real.sqrt_pos.2
    nlinarith [mul_pos (show 0 < ρ + 1 by linarith) (show 0 < 1 - ρ by linarith)]
  have hnorm : -ρ / σ * (-ρ / σ) + 1 / σ * (1 / σ) +
      (-ρ / σ * (1 / σ) + 1 / σ * (-ρ / σ)) * ρ = 1 := by
    rw [show -ρ / σ * (-ρ / σ) + 1 / σ * (1 / σ) +
      (-ρ / σ * (1 / σ) + 1 / σ * (-ρ / σ)) * ρ =
        (1 - ρ ^ 2) / (σ * σ) by ring, ← hσsq]
    exact div_self (mul_pos hσ hσ).ne'
  constructor
  · simpa using (isBrownianReal_coneComb hμ (α := 1) (β := 0) (e := 1)
      (by norm_num) (by ring) 0)
  constructor
  · simpa only [zero_add, one_mul] using
      (isBrownianReal_coneComb hμ (α := -ρ / σ) (β := 1 / σ) (e := 1)
        (by norm_num) hnorm 0)
  · simpa only [zero_add, one_mul] using indepFun_coneComb_future hμ 1 0 σ

/-- The joint barrier is survival in a wedge after whitening and translating the path. -/
theorem mem_jointZeroBarrier_iff_whitened {γ : ℝ} (ω : Path2) (q h : ℝ)
    (hσ : 0 < Real.sqrt (1 - (lrCov γ 0 1) ^ 2)) :
    let ρ := lrCov γ 0 1
    let σ := Real.sqrt (1 - ρ ^ 2)
    ω ∈ jointZeroBarrier q h ↔
      ∀ t ∈ Icc 0 h,
        let x := q + coneIncr 0 t 0 ω
        let y := (1 - ρ) * q / σ + coneComb (-ρ / σ) (1 / σ) t 0 ω
        0 ≤ x ∧ 0 ≤ ρ * x + σ * y := by
  dsimp only
  have hσne : Real.sqrt (1 - (lrCov γ 0 1) ^ 2) ≠ 0 := ne_of_gt hσ
  have hidentity (t : ℝ) :
      lrCov γ 0 1 * (q + coneIncr 0 t 0 ω) +
          Real.sqrt (1 - (lrCov γ 0 1) ^ 2) *
          ((1 - lrCov γ 0 1) * q / Real.sqrt (1 - (lrCov γ 0 1) ^ 2) +
            coneComb (-lrCov γ 0 1 / Real.sqrt (1 - (lrCov γ 0 1) ^ 2))
              (1 / Real.sqrt (1 - (lrCov γ 0 1) ^ 2)) t 0 ω) =
        q + coneIncr 1 t 0 ω := by
    simp only [coneComb]
    field_simp
    ring
  simp only [jointZeroBarrier, mem_inter_iff, mem_ofPred_eq, hidentity]
  constructor
  · rintro ⟨h0, h1⟩ t ht
    exact ⟨by linarith [h0 t ht], by linarith [h1 t ht]⟩
  · intro hw
    constructor <;> intro t ht
    · have := (hw t ht).1; linarith
    · have := (hw t ht).2; linarith

end LatticeProb.CorrelatedBM
