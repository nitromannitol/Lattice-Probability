import LatticeProb.Walk.GreenNorms

/-!
# The two norms of the truncated Green function

The orders of magnitude of the `ℓ²` norm and of the maximum of the truncated Green function
`g_n(x) = ∑_{j<n} P^j(0, x)` of the simple random walk on `ℤ^d`, as the parking formalization
quotes them from Bou-Rabee and Panagiotis, Section 3.1: `‖g_n‖₂ ≍ n^{3/4}, n^{1/2}, n^{1/4},
√(log n), 1` in dimensions one, two, three, four and five upward, and `max_x g_n(x) ≍ n^{1/2},
log n, 1` in dimensions one, two and three upward, for `n ≥ 2`.

The statement is recorded here as a proposition so that a formalization citing it can carry it as
an explicit hypothesis; it is proved in `LatticeProb.External.GreenNormsProved`.
-/

noncomputable section

namespace LatticeProb.External

/-- **The two norms of the truncated Green function**: in every dimension `d ≥ 1` and for
`n ≥ 2`, `‖g_n‖₂ ≍ greenL2Rate d n` and `max_x g_n(x) ≍ greenMaxRate d n`, each
relation with its own pair of constants. -/
def GreenNorms : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * greenL2Rate d n ≤ Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ∧
          Real.sqrt (∑' x : Site d, srwGreen d n x ^ 2) ≤ C * greenL2Rate d n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * greenMaxRate d n ≤ (⨆ x : Site d, srwGreen d n x) ∧
          (⨆ x : Site d, srwGreen d n x) ≤ C * greenMaxRate d n)

end LatticeProb.External
