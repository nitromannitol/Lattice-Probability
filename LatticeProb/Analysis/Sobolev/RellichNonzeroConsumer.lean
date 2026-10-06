import LatticeProb.Analysis.Sobolev.RellichConvolvedCompact

/-! # A nonzero lawful consumer at arbitrary positive or negative orders -/

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- The finite net is actually consumed by a positive normalized bump, for all real orders. -/
theorem rellich_positive_bump_consumer (s₀ s : ℝ) (hlt : s₀ < s) :
    ∃ φ : Space 1 → ℝ,
      IsTestFn (Metric.ball 0 3) φ ∧ 0 < φ 0 ∧
      0 < sobolevNormSq 1 s φ ∧ sobolevNormSq 1 s φ ≤ 1 ∧
      ∃ (N : ℕ) (ψ : Fin N → Space 1 → ℝ),
        0 < N ∧ (∀ i, IsTestFn (Metric.ball 0 3) (ψ i)) ∧
        ∃ i, sobolevNormSq 1 s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal (1 ^ 2) := by
  let b : ContDiffBump (0 : Space 1) := default
  have hb := isTestFn_contDiffBump b
  have hK : IsCompact (tsupport (b : Space 1 → ℝ)) := b.hasCompactSupport
  obtain ⟨A, hA, hbound⟩ := exists_uniform_sobolev_kernel_bound
    (fun _ : Unit => (b : Space 1 → ℝ)) hK (fun _ => b.contDiff)
    (fun _ => subset_rfl)
    (fun n => Continuous.comp
      ((b.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedFDeriv
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) continuous_snd) s

  let c := 1 / (A + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let φ : Space 1 → ℝ := fun x => c * b x
  have htest : IsTestFn (Metric.ball 0 3) φ := by
    refine ⟨b.contDiff.const_smul c, b.hasCompactSupport.mul_left, ?_⟩
    apply (tsupport_mul_subset_right (f := fun _ : Space 1 => c) (g := b)).trans
    apply hb.2.2.trans
    change Metric.closedBall (0 : Space 1) 2 ⊆ Metric.ball 0 3
    exact Metric.closedBall_subset_ball (by norm_num)
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_self] using b.rIn_pos.le)
  have hpos : 0 < φ 0 := by simpa [φ, hb0] using hc
  have hbpos : 0 < sobolevNormSq 1 s (b : Space 1 → ℝ) := by
    have hp := sobolevNormSq_mul_pos_bump (d := 1) s (0 : Space 1)
    by_contra hn
    have hz : sobolevNormSq 1 s (b : Space 1 → ℝ) = 0 :=
      le_antisymm (not_lt.mp hn) bot_le
    change 0 < sobolevNormSq 1 s (b : Space 1 → ℝ) * _ at hp
    rw [hz, zero_mul] at hp
    exact (lt_irrefl (0 : ℝ≥0∞)) hp
  have hnormpos : 0 < sobolevNormSq 1 s φ := by
    rw [show φ = fun x => c * b x from rfl, sobolevNormSq_const_mul]
    exact ENNReal.mul_pos_iff.2 ⟨ENNReal.ofReal_pos.2 (by positivity), hbpos⟩
  have hca : c ^ 2 * A ≤ 1 := by
    dsimp [c]
    rw [div_pow, one_pow, div_mul_eq_mul_div₀, one_mul]
    apply (div_le_iff₀ (by positivity : 0 < (A + 1) ^ 2)).2
    nlinarith [sq_nonneg A]
  have hunit : sobolevNormSq 1 s φ ≤ 1 := by
    rw [show φ = fun x => c * b x from rfl, sobolevNormSq_const_mul]
    calc ENNReal.ofReal (c ^ 2) * sobolevNormSq 1 s (b : Space 1 → ℝ)
        ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal A := mul_le_mul_right (hbound ()) _
      _ = ENNReal.ofReal (c ^ 2 * A) := (ENNReal.ofReal_mul (sq_nonneg c)).symm
      _ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hca
  have hD : IsDomain (Metric.ball (0 : Space 1) 3) :=
    ⟨Metric.isOpen_ball, Metric.isBounded_ball, ⟨0, by simp⟩⟩
  obtain ⟨N, ψ, hψ, hnet⟩ :=
    rellichKondrachovNegSobolev_holds 1 (Metric.ball 0 3) hD s₀ s hlt 1 (by norm_num)
  obtain ⟨i, hi⟩ := hnet φ htest hunit
  exact ⟨φ, htest, hpos, hnormpos, hunit, N, ψ,
    Nat.zero_lt_of_lt i.isLt, hψ, i, hi⟩

end LatticeProb.Sobolev
