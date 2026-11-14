import LatticeProb.Prob.CorrelatedBMDirectPairSurvival

/-! # Optimizing the direct-excursion pair dimension bound -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MesoModel

namespace LatticeProb.CorrelatedBM

private theorem exists_mesh_exponent (p : ℝ) (d β : ℝ≥0)
    (hd : 1 - p / 2 ≤ (d : ℝ)) (hβ : d < β) :
    ∃ α : ℝ≥0, (α : ℝ) < 1 / 2 ∧ 2 < (β : ℝ) + (α : ℝ) * (p + 2) := by
  have hdb : (d : ℝ) < (β : ℝ) := hβ
  by_cases hp : p + 2 ≤ 0
  · refine ⟨0, by norm_num, ?_⟩
    simp only [NNReal.coe_zero, zero_mul, add_zero]
    linarith
  · have hp' : 0 < p + 2 := lt_of_not_ge hp
    have hupper : max 0 ((2 - (β : ℝ)) / (p + 2)) < 1 / 2 := by
      apply max_lt (by norm_num)
      apply (div_lt_iff₀ hp').2
      linarith
    obtain ⟨a, ha, ha'⟩ := exists_between hupper
    have ha0 : 0 ≤ a := (le_max_left _ _).trans ha.le
    refine ⟨⟨a, ha0⟩, ha', ?_⟩
    have hlo : (2 - (β : ℝ)) / (p + 2) < a :=
      (le_max_right _ _).trans_lt ha
    have := (div_lt_iff₀ hp').1 hlo
    change 2 < (β : ℝ) + a * (p + 2)
    linarith

/-- Uniform joint survival estimates for every subcritical mesh exponent yield
an endpoint dimension bound. The survival constant may depend on the exponent. -/
theorem ae_dimH_direct_excursion_pairs_le_of_all_mesh_exponents
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (d : ℝ≥0) (C p : ℝ) (hC : 0 < C) (hd : 1 - p / 2 ≤ (d : ℝ))
    (hJ : ∀ (α : ℝ≥0), (α : ℝ) < 1 / 2 →
      ∀ h : ℝ, 0 < h → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (n : ℕ) (ν : Measure Path2), IsCorrelatedBM2 γ ν →
          ν (jointZeroBarrier (C * (factorialGridMesh n) ^ (α : ℝ)) h) ≤
            ENNReal.ofReal (B * (C * (factorialGridMesh n) ^ (α : ℝ)) ^ p)) :
    ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ d := by
  let β : ℕ → ℝ≥0 := fun n => d + ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hdim (n : ℕ) : ∀ᵐ ω ∂μ, dimH {q : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) q.1 a ∧ DirectRel (lrCoord 1 · ω) q.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a q.1 ∧ DirectRel (lrCoord 1 · ω) b q.1)) ∧
      (q.2 = a ∨ q.2 = b)} ≤ β n := by
    have hb : d < β n := by
      dsimp [β]
      exact lt_add_of_pos_right _ (by exact_mod_cast (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity))
    obtain ⟨α, hα, hs⟩ := exists_mesh_exponent p d (β n) hd hb
    have hb0 : 0 < β n := lt_of_le_of_lt (show 0 ≤ d from bot_le) hb
    exact ae_dimH_direct_excursion_pairs_le_of_joint_survival hμ α (β n) hα hb0 C p hC hs (hJ α hα)
  filter_upwards [ae_all_iff.2 hdim] with ω hω
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((d : ℝ) + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (ENNReal.ofReal (d : ℝ))) := by
    apply ENNReal.tendsto_ofReal
    simpa only [add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (d : ℝ)
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (d : ℝ) = (d : ℝ≥0∞))]
  apply ge_of_tendsto' hlim
  intro n
  have heq : (β n : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) + 1 / ((n : ℝ) + 1)) := by
    change (β n : ℝ≥0∞) = ENNReal.ofReal ((β n : ℝ))
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [← heq]
  exact hω n

end LatticeProb.CorrelatedBM
