/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFiniteChain at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenConnectedFinite

 


set_option autoImplicit false
noncomputable section

open Set Topology Metric
open LQGMetric LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_finite_chain_of_path
    {U : Set ℂ} {z w : ℂ} {q : ℝ → ℂ}
    (hq : IsDGPath U z w q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ p : ℕ → ℂ,
      p 0 = z ∧ p (N + 1) = w ∧
      (∀ k, k ≤ N + 1 → p k ∈ q '' Icc (0 : ℝ) 1) ∧
      ∀ k, k ≤ N → dist (p k) (p (k + 1)) < δ := by
  have huc : UniformContinuousOn q (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hq.continuousOn
  obtain ⟨η, hη, hηq⟩ := Metric.uniformContinuousOn_iff.1 huc δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  let t : ℕ → ℝ := fun k => min ((k : ℝ) / (N + 1)) 1
  let p : ℕ → ℂ := fun k => q (t k)
  have htmem : ∀ k, t k ∈ Icc (0 : ℝ) 1 := by
    intro k
    exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hteq : ∀ k, k ≤ N + 1 → t k = (k : ℝ) / (N + 1) := by
    intro k hk
    exact min_eq_left ((div_le_one (by positivity)).2 (by exact_mod_cast hk))
  refine ⟨N, p, ?_, ?_, ?_, ?_⟩
  · simpa only [p, t, Nat.cast_zero, zero_div, min_eq_left (zero_le_one : (0 : ℝ) ≤ 1)]
      using hq.source
  · have ht : t (N + 1) = 1 := by
      rw [hteq _ le_rfl]
      have hne : (N : ℝ) + 1 ≠ 0 := by positivity
      simp [hne]
    simpa only [p, ht] using hq.target
  · intro k hk
    exact ⟨t k, htmem k, rfl⟩
  · intro k hk
    apply hηq (t k) (htmem k) (t (k + 1)) (htmem (k + 1))
    rw [Real.dist_eq, hteq k (by omega), hteq (k + 1) (by omega)]
    push_cast
    rw [show (k : ℝ) / (N + 1) - (k + 1) / (N + 1) = -(1 / (N + 1)) by ring,
      abs_neg, abs_of_pos (by positivity)]
    exact hN

end SupercriticalLQGUniqueness.B2.DG20Pt
