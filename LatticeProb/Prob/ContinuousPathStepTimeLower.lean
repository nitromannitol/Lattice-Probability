import LatticeProb.Prob.ContinuousPathStepTimes

/-!
# Lower bounds for successive displacement times from a block decomposition

Let `f : ℝ≥0 → E` and let `σ_k = stepTime f r k` be its successive displacement times of size `r`
(`σ₀ = 0`, and `σ_{k+1}` is the first time after `σ_k` at which `f` has moved by `r` from
`f σ_k`). If `τ₀ = 0, τ₁, τ₂, …` are times in `[0, ∞]` such that `f` moves by less than `r` inside
each block `[τ_k, τ_{k+1}]`, then `τ_k ≤ σ_k` for every `k`: the `k`-th displacement of size `r`
cannot be completed before the `k`-th block ends.

A typical use: `τ_k` are the successive exit times of a discrete walk from the balls of radius `ρ`
centred at its position at time `τ_{k-1}`, `f` is the linear interpolation of the walk, and `r`
exceeds twice `ρ` plus the jump sizes.

## Main statements
* `le_nextStep_of_forall`: `b ≤ nextStep f r a` when every time of the step set from `a` is at
  least `b`.
* `le_stepTime_of_block_norm_sub_lt`: the block criterion with `‖f t - f s‖ < r` for
  `τ_k ≤ s ≤ t ≤ τ_{k+1}`.
* `le_stepTime_of_block_norm_sub_le`: the same when `f` stays within `ρ` of a point `q_k` on the
  block `[τ_k, τ_{k+1}]` and `2 ρ < r`.
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ≥0 → E} {r : ℝ}

/-- If every time `t ≥ a` at which `f` has moved by `r` from `f a` is at least `b`, then the next
displacement time from `a` is at least `b`. -/
lemma le_nextStep_of_forall {a : ℝ≥0} {b : ℝ≥0∞}
    (h : ∀ t ∈ stepSet f r a, b ≤ (t : ℝ≥0∞)) : b ≤ nextStep f r a := by
  unfold nextStep
  split_ifs with hne
  · rw [ENNReal.coe_sInf hne]
    exact le_iInf₂ h
  · exact le_top

/-- **Block criterion for displacement times.** Let `τ : ℕ → [0, ∞]` with `τ 0 = 0`. If
`‖f t - f s‖ < r` whenever `τ k ≤ s ≤ t ≤ τ (k + 1)`, then `τ k ≤ σ_k(f, r)` for every `k`. -/
theorem le_stepTime_of_block_norm_sub_lt {τ : ℕ → ℝ≥0∞} (h0 : τ 0 = 0)
    (hblock : ∀ (k : ℕ) (s t : ℝ≥0), τ k ≤ s → s ≤ t → (t : ℝ≥0∞) ≤ τ (k + 1) →
      ‖f t - f s‖ < r) :
    ∀ k, τ k ≤ stepTime f r k := by
  intro k
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    by_cases htop : stepTime f r k = ⊤
    · rw [stepTime_succ_of_eq_top htop]
      exact le_top
    · rw [stepTime_succ_of_ne_top htop]
      have hak : (((stepTime f r k).toNNReal : ℝ≥0) : ℝ≥0∞) = stepTime f r k :=
        ENNReal.coe_toNNReal htop
      apply le_nextStep_of_forall
      intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have hτa : τ k ≤ (((stepTime f r k).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [hak]
        exact ih
      have hlt' := hblock k _ t hτa ht.1 hlt.le
      exact absurd ht.2 (not_le.mpr hlt')

/-- **Block criterion, ball form.** Let `τ : ℕ → [0, ∞]` with `τ 0 = 0`, points `q k`, and
`2 ρ < r`. If `‖f t - q k‖ ≤ ρ` whenever `τ k ≤ t ≤ τ (k + 1)`, then `τ k ≤ σ_k(f, r)` for
every `k`. -/
theorem le_stepTime_of_block_norm_sub_le {τ : ℕ → ℝ≥0∞} (h0 : τ 0 = 0) (q : ℕ → E) {ρ : ℝ}
    (hρ : 2 * ρ < r)
    (hblock : ∀ (k : ℕ) (t : ℝ≥0), τ k ≤ t → (t : ℝ≥0∞) ≤ τ (k + 1) → ‖f t - q k‖ ≤ ρ) :
    ∀ k, τ k ≤ stepTime f r k :=
  le_stepTime_of_block_norm_sub_lt h0 fun k s t hs hst ht => by
    have hst' : (s : ℝ≥0∞) ≤ t := by exact_mod_cast hst
    have h1 := hblock k t (hs.trans hst') ht
    have h2 := hblock k s hs (hst'.trans ht)
    calc ‖f t - f s‖ = ‖(f t - q k) - (f s - q k)‖ := by
          congr 1
          abel
      _ ≤ ‖f t - q k‖ + ‖f s - q k‖ := norm_sub_le _ _
      _ ≤ ρ + ρ := add_le_add h1 h2
      _ < r := by linarith

end LatticeProb
