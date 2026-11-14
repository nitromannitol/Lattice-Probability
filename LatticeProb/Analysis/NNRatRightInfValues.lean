import LatticeProb.Analysis.NNRatRightInf

/-!
# Values of the right limit through the nonnegative rationals

For a rational skeleton `a : ℚ≥0 → ℝ≥0`, `nnratRightInf a t = inf {a q : q ∈ ℚ≥0, q > t}`.  We record when this
right limit returns the values of the data it was built from.

* `nnratRightInf_nnrat`: for a monotone skeleton with a locally uniform modulus of continuity (the
  hypothesis of `continuous_nnratRightInf`), the right limit agrees with the skeleton at every
  nonnegative rational;
* `nnratRightInf_eq_of_continuous`: for a continuous nondecreasing function `g : ℝ≥0 → ℝ≥0`, the right
  limit of its rational restriction is `g`.
-/

open scoped NNReal

noncomputable section

namespace LatticeProb

/-- **The right limit of a good skeleton returns the skeleton at the nonnegative rationals.** -/
theorem nnratRightInf_nnrat (a : ℚ≥0 → ℝ≥0) (hmono : Monotone a)
    (hmod : ∀ N k : ℕ, ∃ j : ℕ, ∀ p q : ℚ≥0, (p : ℝ) ≤ N → (q : ℝ) ≤ N →
      |(p : ℝ) - q| < 1 / ((j : ℝ) + 1) → |(a p : ℝ) - (a q : ℝ)| ≤ 1 / ((k : ℝ) + 1))
    (r : ℚ≥0) : nnratRightInf a (r : ℝ≥0) = a r := by
  refine le_antisymm ?_ (le_nnratRightInf hmono le_rfl)
  by_contra hlt
  have hlt := not_le.1 hlt
  have hd : (0 : ℝ) < (nnratRightInf a (r : ℝ≥0) : ℝ) - a r := sub_pos.2 (NNReal.coe_lt_coe.2 hlt)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
  obtain ⟨N, hN⟩ := exists_nat_gt ((r : ℝ) + 1)
  obtain ⟨j, hj⟩ := hmod N k
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hη1 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hj0]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  obtain ⟨η, hηc, hη0⟩ : ∃ η : ℝ≥0, (η : ℝ) = 1 / ((j : ℝ) + 1) ∧ 0 < η :=
    ⟨(1 / ((j : ℝ) + 1)).toNNReal, Real.coe_toNNReal _ (by positivity),
      Real.toNNReal_pos.2 (by positivity)⟩
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_between_nnreal (show (r : ℝ≥0) < r + η by simpa using hη0)
  have hq1' : (r : ℝ) < q := by exact_mod_cast hq1
  have hq2' : (q : ℝ) < r + 1 / ((j : ℝ) + 1) := by
    have h3 : (q : ℝ) < r + (η : ℝ) := by exact_mod_cast hq2
    rwa [hηc] at h3
  have hle : (nnratRightInf a (r : ℝ≥0) : ℝ) ≤ a q := NNReal.coe_le_coe.2 (nnratRightInf_le hq1)
  have hpq : |(r : ℝ) - q| < 1 / ((j : ℝ) + 1) := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have h := hj r q (by linarith) (by linarith) hpq
  rw [abs_sub_comm] at h
  have h2 : (a q : ℝ) - a r ≤ |(a q : ℝ) - a r| := le_abs_self _
  linarith

/-- **The right limit through the rationals of a continuous nondecreasing function is the function.** -/
theorem nnratRightInf_eq_of_continuous {g : ℝ≥0 → ℝ≥0} (hg : Continuous g) (hmono : Monotone g)
    (t : ℝ≥0) : nnratRightInf (fun q : ℚ≥0 => g q) t = g t := by
  have hne := nonempty_nnratRightInf_index t
  refine le_antisymm ?_ (le_ciInf fun q => hmono q.2.le)
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hg t ε hε
  have hδ0 : (0 : ℝ≥0) < δ.toNNReal := Real.toNNReal_pos.2 hδ
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_between_nnreal (show t < t + δ.toNNReal by simpa using hδ0)
  have hq1' : (t : ℝ) < q := by exact_mod_cast hq1
  have hq2' : ((q : ℝ≥0) : ℝ) < t + δ := by
    have h3 := NNReal.coe_lt_coe.2 hq2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at h3
  have hd : dist (q : ℝ≥0) t < δ := by
    rw [NNReal.dist_eq, abs_of_pos (by linarith)]
    linarith
  have h := hδ' (q : ℝ≥0) hd
  rw [NNReal.dist_eq] at h
  have h1 : ((nnratRightInf (fun q : ℚ≥0 => g q) t : ℝ≥0) : ℝ) ≤ g q :=
    NNReal.coe_le_coe.2 (nnratRightInf_le hq1)
  have h2 := (abs_lt.1 h).2
  linarith

end LatticeProb

end
