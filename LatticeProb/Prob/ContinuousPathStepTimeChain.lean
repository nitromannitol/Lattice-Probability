import LatticeProb.Prob.ContinuousPathStepTimeCompare

/-!
# Well-separated chains dominate displacement times; the stay form of the comparison

Let `f : ℝ≥0 → E` and let `σ_k = stepTime f r k` be its successive displacement times of size `r`
(`σ₀ = 0`, and `σ_{k+1}` is the first time after `σ_k` at which `f` has moved by `r` from
`f σ_k`).

* `stepTime_le_of_chain`: if `τ₀ ≤ τ₁ ≤ …` are times in `[0, ∞]` such that `f` moves by at least
  `D ≥ 2 r` between two consecutive finite chain times, then `σ_k ≤ τ_k` for every `k`. Each
  displacement interval `[σ_{k-1}, σ_k)` contains at most one chain point more than the previous
  one, because `f` stays within `r` of `f σ_{k-1}` there. No continuity is needed.
* `norm_lt_of_lt_stepTime_of_norm_sub_comp_le`: transfer of a *stay* event between two paths at
  distance `≤ κ` modulo an increasing time change `φ`: if `f` stays in the ball of radius `ρ`
  around the origin up to its `K`-th displacement time of size `s`, then `g` stays in the ball of
  radius `ρ + κ` up to its `K`-th displacement time of size `r`, whenever `2 r + 2 κ ≤ s`. This is
  the converse direction of `exists_lt_stepTime_of_norm_sub_comp_le` (exit before the `K`-th step).
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimeChain

variable {E : Type*} [NormedAddCommGroup E]

/-- **Chain criterion.** Let `τ : ℕ → [0, ∞]` be nondecreasing and suppose `f` moves by at least
`D` between two consecutive finite chain times, with `2 r ≤ D`. Then the `k`-th displacement time
of size `r` of `f` comes no later than `τ k`. -/
theorem stepTime_le_of_chain {f : ℝ≥0 → E} {r D : ℝ} (hD : 2 * r ≤ D) {τ : ℕ → ℝ≥0∞}
    (hmono : ∀ k, τ k ≤ τ (k + 1))
    (hsep : ∀ (k : ℕ) (s t : ℝ≥0), τ k = s → τ (k + 1) = t → D ≤ ‖f t - f s‖) :
    ∀ k, stepTime f r k ≤ τ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    by_contra hlt
    rw [not_le] at hlt
    have hτtop : τ (k + 1) ≠ ⊤ := ne_top_of_lt hlt
    have hτk : τ k ≠ ⊤ := ne_top_of_le_ne_top hτtop (hmono k)
    have hσk : stepTime f r k ≠ ⊤ := ne_top_of_le_ne_top hτk ih
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, τ k = s := ⟨(τ k).toNNReal, (ENNReal.coe_toNNReal hτk).symm⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, τ (k + 1) = t :=
      ⟨(τ (k + 1)).toNNReal, (ENNReal.coe_toNNReal hτtop).symm⟩
    rw [stepTime_succ_of_ne_top hσk, ht] at hlt
    have hak : (((stepTime f r k).toNNReal : ℝ≥0) : ℝ≥0∞) = stepTime f r k :=
      ENNReal.coe_toNNReal hσk
    have has : (stepTime f r k).toNNReal ≤ s := by
      have : (((stepTime f r k).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞) := by
        rw [hak, ← hs]; exact ih
      exact_mod_cast this
    have hst : s ≤ t := by
      have : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by rw [← hs, ← ht]; exact hmono k
      exact_mod_cast this
    have h1 : ‖f t - f (stepTime f r k).toNNReal‖ < r :=
      norm_lt_of_lt_nextStep (has.trans hst) hlt
    have h2 : ‖f s - f (stepTime f r k).toNNReal‖ < r :=
      norm_lt_of_lt_nextStep has (lt_of_le_of_lt (by exact_mod_cast hst) hlt)
    have h3 := hsep k s t hs ht
    have h4 := norm_sub_le_norm_sub_add_norm_sub (f t) (f (stepTime f r k).toNNReal) (f s)
    have h5 : ‖f (stepTime f r k).toNNReal - f s‖ = ‖f s - f (stepTime f r k).toNNReal‖ :=
      norm_sub_rev _ _
    linarith

/-- **Stay form of the comparison.** If `‖f t - g (φ t)‖ ≤ κ` for all `t` (`φ` an increasing
bijection of `ℝ≥0`), `2 r + 2 κ ≤ s`, and `f` stays in the open ball of radius `ρ` about the origin
at all times before its `K`-th displacement time of size `s`, then `g` stays in the open ball of
radius `ρ + κ` about the origin at all times before its `K`-th displacement time of size `r`. -/
theorem norm_lt_of_lt_stepTime_of_norm_sub_comp_le {f g : ℝ≥0 → E} (φ : ℝ≥0 ≃o ℝ≥0)
    {s r κ ρ : ℝ} (hfg : ∀ t, ‖f t - g (φ t)‖ ≤ κ) (hr : 2 * r + 2 * κ ≤ s) {K : ℕ}
    (hf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < stepTime f s K → ‖f t‖ < ρ) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < stepTime g r K → ‖g u‖ < ρ + κ := by
  intro u hu
  have hle : stepTime (g ∘ φ) r K ≤ stepTime f s K :=
    stepTime_le_stepTime_of_norm_sub_le (f := g ∘ φ) (g := f) (s := r) (r := s) (κ := κ)
      (fun t => by rw [Function.comp_apply, norm_sub_rev]; exact hfg t) hr K
  have hut : ((φ.symm u : ℝ≥0) : ℝ≥0∞) < stepTime (g ∘ φ) r K :=
    (coe_lt_stepTime_comp_iff g r φ K (φ.symm u)).2 (by rw [φ.apply_symm_apply]; exact hu)
  have h1 := hf (φ.symm u) (lt_of_lt_of_le hut hle)
  have h2 := hfg (φ.symm u)
  rw [φ.apply_symm_apply] at h2
  have h3 := norm_sub_norm_le (g u) (f (φ.symm u))
  have h4 : ‖g u - f (φ.symm u)‖ = ‖f (φ.symm u) - g u‖ := norm_sub_rev _ _
  linarith

end StepTimeChain

end LatticeProb
