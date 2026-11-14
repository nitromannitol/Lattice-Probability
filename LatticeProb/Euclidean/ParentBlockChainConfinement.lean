import LatticeProb.Euclidean.ParentBlock

/-!
# Confinement of a chain of parent-block excursions

A path whose sampled positions remain in a parent block and whose oscillation between samples is
bounded stays in a fixed larger ball, even if it leaves and re-enters the parent block.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

private theorem exists_mem_interval_of_le {τ : ℕ → ℝ≥0} (hzero : τ 0 = 0) (K : ℕ) {t : ℝ≥0} (ht : t ≤ τ K) (hK : 0 < K) :
    ∃ n < K, τ n ≤ t ∧ t ≤ τ (n + 1) := by
  induction K with
  | zero => omega
  | succ K ih =>
    by_cases h : t ≤ τ K
    · by_cases hK' : 0 < K
      · obtain ⟨n, hn, hnt, htn⟩ := ih h hK'
        exact ⟨n, by omega, hnt, htn⟩
      · have hK0 : K = 0 := by omega
        subst K
        exact ⟨0, by omega, by simp [hzero], ht⟩
    · exact ⟨K, by omega, le_of_not_ge h, ht⟩

/-- Sampled parent-block positions and a bound on each inter-sample oscillation confine the whole
path to a ball with radius the sum of the two bounds. The final interval may cross the outer
boundary. -/
theorem norm_sub_le_of_parentBlock_chain {f : ℝ≥0 → ℂ} {τ : ℕ → ℝ≥0}
    {z c : ℂ} {S s : ℝ} (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hz : z ∈ closedSquare c S) (hstart : f 0 = z)
    (hzero : τ 0 = 0) (K : ℕ)
    (hpoints : ∀ n < K, f (τ n) ∈ parentBlock c S)
    (hosc : ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)), ‖f t - f (τ n)‖ ≤ 4 * s)
    {t : ℝ≥0} (ht : t ≤ τ K) : ‖f t - z‖ ≤ 4 * S + 4 * s := by
  by_cases hK : 0 < K
  · obtain ⟨n, hn, hnt, htn⟩ := exists_mem_interval_of_le hzero K ht hK
    have h1 := hosc n hn t ⟨hnt, htn⟩
    have h2 := norm_sub_le_four_mul_of_mem_of_mem_parentBlock hS hz (hpoints n hn)
    calc
      ‖f t - z‖ ≤ ‖f t - f (τ n)‖ + ‖f (τ n) - z‖ := by
        simpa only [dist_eq_norm] using dist_triangle (f t) (f (τ n)) z
      _ ≤ 4 * S + 4 * s := by linarith
  · have hK0 : K = 0 := by omega
    subst K
    have ht0 : t = 0 := by simpa [hzero] using ht
    subst t
    simp only [hstart, sub_self, norm_zero]
    positivity

end LatticeProb.ParentBlock
