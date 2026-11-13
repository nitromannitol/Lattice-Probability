import LatticeProb.Analysis.LogKernel

/-!
# The logarithmic kernel on a set, split at a small radius

For a measure `μ` on `ℂ`, a point `z` and a Borel set `S`, split `S` at the ball `B_s(z)`, `s ≤ 1`.
Off the ball the kernel `log (1/|z - w|) + 1` is at most `log (1/s) + 1`; on the ball the dyadic
volume bound `μ(B_{s 2^{-k}}(z)) ≤ (s 2^{-k})^β` controls the integral
(`LatticeProb.LogKernel.setLIntegral_ball_log_le`). Hence (`setLIntegral_log_le_of_dyadic`)
`∫_S (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/s) + 1) μ(S) + (log (1/s) + 1 + log 2) s^β (1 - 2^{-β})⁻¹`.

This is the deterministic step of the estimate of the logarithmic energy of a set by its mass
(Berestycki-Gwynne, arXiv:2003.10320, proof of Lemma A.3, (A.12)): when the volume bound holds down
to a radius `s` whose power `s^β` is small compared with `μ(S)`, the second term is absorbed into the
first (`iSup_setLIntegral_log_le_mul_of_dyadic`), uniformly over the centres `z` in a set `T`.
-/

namespace LatticeProb.LogKernel

open MeasureTheory Set Metric
open scoped ENNReal

/-- Off the ball `B_s(z)` the logarithmic kernel is at most its value at distance `s`:
`log (1/|z - w|) + 1 ≤ log (1/s) + 1` when `s ≤ |z - w|`. -/
theorem ofReal_log_le_of_le_norm {s : ℝ} (hs0 : 0 < s) {z w : ℂ} (hw : s ≤ ‖z - w‖) :
    ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ≤ ENNReal.ofReal (Real.log (1 / s) + 1) := by
  apply ENNReal.ofReal_le_ofReal
  have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le hs0 hw
  have : Real.log (1 / ‖z - w‖) ≤ Real.log (1 / s) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hs0 hw)
  linarith

/-- `log (1/s) + 1 ≥ 0` for `0 < s ≤ 1`. -/
theorem log_one_div_add_one_nonneg {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ Real.log (1 / s) + 1 := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / s by rw [le_div_iff₀ hs0]; linarith)
  linarith

/-- **The logarithmic kernel on a set, split at radius `s`.** If `μ(B_{s 2^{-k}}(z)) ≤ (s 2^{-k})^β`
for every `k ∈ ℕ`, `0 < s ≤ 1`, `β > 0`, then for every Borel set `S`,
`∫_S (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/s) + 1) μ(S) + (log (1/s) + 1 + log 2) s^β (1 - 2^{-β})⁻¹`. -/
theorem setLIntegral_log_le_of_dyadic {μ : Measure ℂ} {z : ℂ} {S : Set ℂ} {s β : ℝ}
    (hS : MeasurableSet S) (hs0 : 0 < s) (hs1 : s ≤ 1) (hβ : 0 < β)
    (hvol : ∀ k : ℕ, μ (ball z (s * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((s * (1 / 2) ^ k) ^ β)) :
    ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal (Real.log (1 / s) + 1) * μ S +
        ENNReal.ofReal ((Real.log (1 / s) + 1 + Real.log 2) * s ^ β * (1 - (1 / 2) ^ β)⁻¹) := by
  have hsplit : S ⊆ (S \ ball z s) ∪ ball z s := by
    intro w hw
    by_cases hb : w ∈ ball z s
    · exact Or.inr hb
    · exact Or.inl ⟨hw, hb⟩
  have hoff : ∫⁻ w in S \ ball z s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ ≤
      ENNReal.ofReal (Real.log (1 / s) + 1) * μ S := by
    calc ∫⁻ w in S \ ball z s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
        ≤ ∫⁻ _ in S \ ball z s, ENNReal.ofReal (Real.log (1 / s) + 1) ∂μ := by
          refine setLIntegral_mono' (hS.diff measurableSet_ball) fun w hw => ?_
          apply ofReal_log_le_of_le_norm hs0
          have hnot := hw.2
          rw [mem_ball, dist_comm, dist_eq_norm, not_lt] at hnot
          exact hnot
      _ = ENNReal.ofReal (Real.log (1 / s) + 1) * μ (S \ ball z s) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (Real.log (1 / s) + 1) * μ S := by
          gcongr
          exact sdiff_subset
  calc ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ
      ≤ ∫⁻ w in (S \ ball z s) ∪ ball z s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ :=
        lintegral_mono_set hsplit
    _ ≤ ∫⁻ w in S \ ball z s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ +
          ∫⁻ w in ball z s, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ _ := add_le_add hoff (setLIntegral_ball_log_le hs0 hs1 hβ hvol)

/-- Uniform version of `setLIntegral_log_le_of_dyadic` over the centres `z ∈ T`. -/
theorem iSup_setLIntegral_log_le_of_dyadic {μ : Measure ℂ} {T S : Set ℂ} {s β : ℝ}
    (hS : MeasurableSet S) (hs0 : 0 < s) (hs1 : s ≤ 1) (hβ : 0 < β)
    (hvol : ∀ z ∈ T, ∀ k : ℕ,
      μ (ball z (s * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((s * (1 / 2) ^ k) ^ β)) :
    (⨆ z ∈ T, ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ≤
      ENNReal.ofReal (Real.log (1 / s) + 1) * μ S +
        ENNReal.ofReal ((Real.log (1 / s) + 1 + Real.log 2) * s ^ β * (1 - (1 / 2) ^ β)⁻¹) :=
  iSup₂_le fun z hz => setLIntegral_log_le_of_dyadic hS hs0 hs1 hβ (hvol z hz)

/-- **Logarithmic energy of a set bounded by its mass.** Under the dyadic volume bound at radius `s`
around every centre `z ∈ T`, if the dyadic tail `(log (1/s) + 1 + log 2) s^β (1 - 2^{-β})⁻¹` is at
most `μ(S)`, then `sup_{z ∈ T} ∫_S (log (1/|z - w|) + 1) dμ(w) ≤ (log (1/s) + 2) μ(S)`
(Berestycki-Gwynne, arXiv:2003.10320, Lemma A.3 with the additive error absorbed as in the proof of
Lemma 6.7, (6.17)). -/
theorem iSup_setLIntegral_log_le_mul_of_dyadic {μ : Measure ℂ} {T S : Set ℂ} {s β : ℝ}
    (hS : MeasurableSet S) (hs0 : 0 < s) (hs1 : s ≤ 1) (hβ : 0 < β)
    (hvol : ∀ z ∈ T, ∀ k : ℕ,
      μ (ball z (s * (1 / 2) ^ k)) ≤ ENNReal.ofReal ((s * (1 / 2) ^ k) ^ β))
    (htail : ENNReal.ofReal ((Real.log (1 / s) + 1 + Real.log 2) * s ^ β * (1 - (1 / 2) ^ β)⁻¹) ≤
      μ S) :
    (⨆ z ∈ T, ∫⁻ w in S, ENNReal.ofReal (Real.log (1 / ‖z - w‖) + 1) ∂μ) ≤
      ENNReal.ofReal (Real.log (1 / s) + 2) * μ S := by
  refine (iSup_setLIntegral_log_le_of_dyadic hS hs0 hs1 hβ hvol).trans ?_
  have hl := log_one_div_add_one_nonneg hs0 hs1
  calc ENNReal.ofReal (Real.log (1 / s) + 1) * μ S +
        ENNReal.ofReal ((Real.log (1 / s) + 1 + Real.log 2) * s ^ β * (1 - (1 / 2) ^ β)⁻¹)
      ≤ ENNReal.ofReal (Real.log (1 / s) + 1) * μ S + μ S := add_le_add le_rfl htail
    _ = ENNReal.ofReal (Real.log (1 / s) + 2) * μ S := by
      rw [show Real.log (1 / s) + 2 = (Real.log (1 / s) + 1) + 1 by ring,
        ENNReal.ofReal_add hl zero_le_one, ENNReal.ofReal_one, add_mul, one_mul]

end LatticeProb.LogKernel
