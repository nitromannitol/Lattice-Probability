import LatticeProb.Prob.ContinuousPathStepTimes

/-!
# Separated chains are dominated by the successive displacement times

Let `σ_0 = 0 ≤ σ_1 ≤ ⋯` be the successive displacement times of size `r` of a path `f`
(`LatticeProb.stepTime f r`).  If `τ_0 ≤ τ_1 ≤ ⋯` is any nondecreasing chain of times along which `f`
moves by at least `2 r` between consecutive times, then `σ_n ≤ τ_n`.  Consequently the number of
steps of such a chain performed before a given time is at most the number of displacement times of
size `r` before that time.

The proof is the observation that between the chain times `τ_n` and `τ_{n+1}`, which are `2 r` apart in
the path, the path must leave the open `r`-ball around its value at the last displacement time not
exceeding `τ_n`.
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimeChain

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ≥0 → E} {r : ℝ}

/-- **A chain with increments of size at least `2 r` is dominated by the displacement times of
size `r`.**  For a nondecreasing chain `τ` with `2 r ≤ ‖f (τ (n+1)) - f (τ n)‖` for `n < N`, the
`n`-th displacement time of size `r` is at most `τ n`, for every `n ≤ N`. -/
theorem stepTime_le_of_separated_chain {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {N : ℕ}
    (hsep : ∀ n < N, 2 * r ≤ ‖f (τ (n + 1)) - f (τ n)‖) :
    ∀ n ≤ N, stepTime f r n ≤ (τ n : ℝ≥0∞) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 : stepTime f r n ≤ (τ n : ℝ≥0∞) := ih (Nat.le_of_succ_le hn)
    by_contra hlt
    rw [not_le] at hlt
    have hfin : stepTime f r n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
    rw [stepTime_succ_of_ne_top hfin] at hlt
    have haτ : (stepTime f r n).toNNReal ≤ τ n := by
      have := ENNReal.toNNReal_mono ENNReal.coe_ne_top h1
      simpa using this
    have hτle : τ n ≤ τ (n + 1) := hτ (Nat.le_succ n)
    have hn1 : ‖f (τ n) - f (stepTime f r n).toNNReal‖ < r :=
      norm_lt_of_lt_nextStep haτ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτle) hlt)
    have hn2 : ‖f (τ (n + 1)) - f (stepTime f r n).toNNReal‖ < r :=
      norm_lt_of_lt_nextStep (haτ.trans hτle) hlt
    have hsepn := hsep n (Nat.lt_of_succ_le hn)
    have hsub : f (τ (n + 1)) - f (τ n) =
        (f (τ (n + 1)) - f (stepTime f r n).toNNReal) - (f (τ n) - f (stepTime f r n).toNNReal) := by
      abel
    have hlt2 : ‖f (τ (n + 1)) - f (τ n)‖ < r + r := by
      rw [hsub]
      exact (norm_sub_le _ _).trans_lt (add_lt_add hn2 hn1)
    linarith

/-- The number of steps of a `2 r`-separated chain finished by time `T` is at most the number of
displacement times of size `r` finished by time `T`: if the chain makes `N` steps with `τ N ≤ T`, then
the `N`-th displacement time of size `r` is at most `T`. -/
theorem stepTime_le_of_separated_chain_of_le {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {N : ℕ}
    (hsep : ∀ n < N, 2 * r ≤ ‖f (τ (n + 1)) - f (τ n)‖) {T : ℝ≥0} (hT : τ N ≤ T) :
    stepTime f r N ≤ (T : ℝ≥0∞) :=
  (stepTime_le_of_separated_chain hτ hsep N le_rfl).trans (by exact_mod_cast hT)

end StepTimeChain

end LatticeProb
