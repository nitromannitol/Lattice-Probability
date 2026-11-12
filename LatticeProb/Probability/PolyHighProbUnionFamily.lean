import Mathlib
import LatticeProb.Gauss.GFF

/-!
# Polynomially high probability for a scale-dependent finite family of events

If for each scale `r ∈ (0, 1)` a finite index set `T r` of at most `K r^{-c}` events `E r i` is given, each failing with
probability at most `C r^α` and `c < α`, then the intersection of the events over `i ∈ T r` holds with polynomially high
probability as `r → 0`: the union bound gives `P[∃ i ∈ T r, ω ∉ E r i] ≤ K C r^{α - c}`. The events need not be
measurable; the probabilities of complements are outer measures.

## Main statement

* `polyHighProb_forall_mem_finset`
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Gauss

/-- **Union bound over a finite family that grows polynomially as the scale shrinks.** If, for every `r ∈ (0, 1)`, the
index set `T r` has at most `K r^{-c}` elements and each event `E r i`, `i ∈ T r`, fails with probability at most
`C r^α`, where `c < α`, then `⋂_{i ∈ T r} E r i` holds with polynomially high probability (exponent `α - c`). -/
theorem polyHighProb_forall_mem_finset {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*}
    (T : ℝ → Finset ι) (E : ℝ → ι → Set Ω) {K c C α : ℝ} (_hK : 0 ≤ K) (hC : 0 ≤ C) (hcα : c < α)
    (hT : ∀ r : ℝ, 0 < r → r < 1 → ((T r).card : ℝ) ≤ K * r ^ (-c))
    (hE : ∀ r : ℝ, 0 < r → r < 1 → ∀ i ∈ T r, P (E r i)ᶜ ≤ ENNReal.ofReal (C * r ^ α)) :
    PolyHighProb P (fun r => {ω | ∀ i ∈ T r, ω ∈ E r i}) := by
  refine ⟨α - c, by linarith, K * C, 1, one_pos, fun r hr hr1 => ?_⟩
  have hsub : ({ω | ∀ i ∈ T r, ω ∈ E r i} : Set Ω)ᶜ = ⋃ i ∈ T r, (E r i)ᶜ := by
    ext ω
    simp
  rw [hsub]
  calc P (⋃ i ∈ T r, (E r i)ᶜ) ≤ ∑ i ∈ T r, P (E r i)ᶜ := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ T r, ENNReal.ofReal (C * r ^ α) := Finset.sum_le_sum fun i hi => hE r hr hr1 i hi
    _ = ((T r).card : ℝ≥0∞) * ENNReal.ofReal (C * r ^ α) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal (((T r).card : ℝ) * (C * r ^ α)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (K * C * r ^ (α - c)) := by
        apply ENNReal.ofReal_le_ofReal
        have h : K * C * r ^ (α - c) = (K * r ^ (-c)) * (C * r ^ α) := by
          rw [Real.rpow_sub hr, Real.rpow_neg hr.le]
          ring
        rw [h]
        exact mul_le_mul_of_nonneg_right (hT r hr hr1) (mul_nonneg hC (Real.rpow_nonneg hr.le _))

end LatticeProb.Gauss
