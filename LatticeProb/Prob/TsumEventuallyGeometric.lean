import Mathlib

/-!
# A series that is eventually dominated by a geometric series is finite

For `L : ℕ → [0, ∞]` with every `L k` finite and `L k ≤ C e^{-η k}` for all large `k`
(`η > 0`), the series `∑' k, L k` is finite.
-/

open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- A series of finite terms that is eventually bounded by `C e^{-η k}`, `η > 0`, is finite. -/
theorem tsum_ne_top_of_eventually_le_exp {L : ℕ → ℝ≥0∞} (hfin : ∀ k, L k ≠ ⊤) {C η : ℝ}
    (hη : 0 < η)
    (hev : ∀ᶠ k in Filter.atTop, L k ≤ ENNReal.ofReal (C * Real.exp (-(η * k)))) :
    ∑' k, L k ≠ ⊤ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0∞, r = ENNReal.ofReal (Real.exp (-η)) := ⟨_, rfl⟩
  have hr1 : r < 1 := by
    rw [hr]
    refine ENNReal.ofReal_lt_one.2 ?_
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hgeo : ∑' k : ℕ, ENNReal.ofReal |C| * r ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne')
  have hpt : ∀ k : ℕ, L k ≤ (if k < N then L k else 0) + ENNReal.ofReal |C| * r ^ k := by
    intro k
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte]
      exact le_self_add
    · simp only [hk, ↓reduceIte, zero_add]
      refine (hN k (not_lt.1 hk)).trans ?_
      have hx : Real.exp (-(η * k)) = Real.exp (-η) ^ k := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc ENNReal.ofReal (C * Real.exp (-(η * k)))
          ≤ ENNReal.ofReal (|C| * Real.exp (-(η * k))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
        _ = ENNReal.ofReal |C| * r ^ k := by
            rw [ENNReal.ofReal_mul (abs_nonneg C), hx, hr, ENNReal.ofReal_pow (Real.exp_pos _).le]
  have hfinite : ∑' k : ℕ, (if k < N then L k else 0) ≠ ⊤ := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · refine ENNReal.sum_ne_top.2 fun k _ => ?_
      split_ifs
      · exact hfin k
      · simp
    · intro k hk
      have : ¬ k < N := fun h => hk (Finset.mem_range.2 h)
      simp [this]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hpt)
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.2 ⟨hfinite, hgeo⟩

end LatticeProb
