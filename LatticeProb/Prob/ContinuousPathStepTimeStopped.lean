import LatticeProb.Prob.ContinuousPathStepTimeCompare

/-!
# Displacement times of a stopped path

For a path `f : ℝ≥0 → E`, the successive displacement times of size `r` (`stepTime f r`) below a time `T`
depend only on `f` on `[0, T]`: if `f = g` on `[0, T]`, then `min (σ_j f) T = min (σ_j g) T` for every `j`
(`min_stepTime_eq_of_eqOn`).

Consequently, if the path `f` stopped at time `T`, `t ↦ f (min t T)`, reaches distance `a` from its starting
point strictly before its `K`-th displacement time, then `f` itself reaches distance `a` at the time
`u = min s T ≤ T`, which is at most the `K`-th displacement time of `f` (`exists_le_stepTime_of_stopped`).
Together with the comparison of displacement times under a uniform perturbation modulo an increasing time
change (`exists_lt_stepTime_of_norm_sub_comp_le`), this transfers an exit-before-the-`K`-th-step event from a
path `f` to any path `b` such that `b` stopped at time `T` is uniformly close to `f` after a time change
(`exists_le_stepTime_of_norm_sub_comp_stopped_le`).
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimeStopped

variable {E : Type*} [NormedAddCommGroup E]

/-- Locality of the next displacement time: if `f = g` on `[0, T]` and `a ≤ T`, then
`min (nextStep f r a) T ≤ nextStep g r a`. -/
lemma min_nextStep_le_of_eqOn {f g : ℝ≥0 → E} {r : ℝ} {T a : ℝ≥0} (hfg : ∀ t ≤ T, f t = g t)
    (haT : a ≤ T) : min (nextStep f r a) (T : ℝ≥0∞) ≤ nextStep g r a := by
  by_contra hcon
  rw [not_le] at hcon
  have hne : min (nextStep f r a) (T : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  obtain ⟨x, hxeq⟩ : ∃ x : ℝ≥0, (x : ℝ≥0∞) = min (nextStep f r a) (T : ℝ≥0∞) :=
    ⟨_, ENNReal.coe_toNNReal hne⟩
  rw [← hxeq] at hcon
  obtain ⟨t, ht, htx⟩ := exists_mem_of_nextStep_lt hcon
  have htx' : (t : ℝ≥0∞) < min (nextStep f r a) (T : ℝ≥0∞) := by
    rw [← hxeq]
    exact_mod_cast htx
  have htT : t ≤ T := (ENNReal.coe_lt_coe.1 (htx'.trans_le (min_le_right _ _))).le
  have hmem : t ∈ stepSet f r a :=
    ⟨ht.1, by
      show r ≤ ‖f t - f a‖
      rw [hfg t htT, hfg a haT]
      exact ht.2⟩
  exact absurd (nextStep_le_of_mem hmem) (not_le.2 (htx'.trans_le (min_le_left _ _)))

/-- **Locality of displacement times.** If `f = g` on `[0, T]`, then for every `j` the `j`-th displacement
times of `f` and of `g` of size `r`, capped at `T`, coincide. -/
theorem min_stepTime_eq_of_eqOn {f g : ℝ≥0 → E} {r : ℝ} {T : ℝ≥0} (hfg : ∀ t ≤ T, f t = g t)
    (j : ℕ) : min (stepTime f r j) (T : ℝ≥0∞) = min (stepTime g r j) (T : ℝ≥0∞) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    by_cases hT : (T : ℝ≥0∞) ≤ stepTime f r j
    · have hT' : (T : ℝ≥0∞) ≤ stepTime g r j := by
        by_contra hcon
        rw [not_le] at hcon
        rw [min_eq_right hT, min_eq_left hcon.le] at ih
        exact hcon.ne' ih
      rw [min_eq_right (hT.trans (stepTime_le_succ j)), min_eq_right (hT'.trans (stepTime_le_succ j))]
    · rw [not_le] at hT
      have hfeq : stepTime f r j = stepTime g r j := by
        rw [min_eq_left hT.le] at ih
        rcases le_total (stepTime g r j) (T : ℝ≥0∞) with h | h
        · rwa [min_eq_left h] at ih
        · rw [min_eq_right h] at ih
          exact absurd ih hT.ne
      have hne : stepTime f r j ≠ ⊤ := ne_top_of_lt hT
      have hne' : stepTime g r j ≠ ⊤ := hfeq ▸ hne
      rw [stepTime_succ_of_ne_top hne, stepTime_succ_of_ne_top hne', ← hfeq]
      have haT : (stepTime f r j).toNNReal ≤ T := by
        have hc := ENNReal.coe_toNNReal hne
        exact (ENNReal.coe_lt_coe.1 (by rw [hc]; exact hT)).le
      have h1 := min_nextStep_le_of_eqOn (r := r) hfg haT
      have h2 := min_nextStep_le_of_eqOn (r := r) (fun t ht => (hfg t ht).symm) haT
      exact le_antisymm (le_min h1 (min_le_right _ _)) (le_min h2 (min_le_right _ _))

/-- **Witness for the unstopped path.** Let `g` be `f` stopped at time `T`, `g t = f (min t T)`. If `g`
reaches distance `a` from `g 0` strictly before its `K`-th displacement time of size `r`, then `f` reaches
distance `a` from `f 0` at a time `u ≤ T` which is at most its `K`-th displacement time of size `r`. -/
theorem exists_le_stepTime_of_stopped {f g : ℝ≥0 → E} {T : ℝ≥0} (hg : ∀ t, g t = f (min t T))
    {r a : ℝ} {K : ℕ} (h : ∃ s : ℝ≥0, (s : ℝ≥0∞) < stepTime g r K ∧ a ≤ ‖g s - g 0‖) :
    ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ stepTime f r K ∧ u ≤ T ∧ a ≤ ‖f u - f 0‖ := by
  obtain ⟨s, hs, has⟩ := h
  have hloc := min_stepTime_eq_of_eqOn (r := r)
    (fun t (ht : t ≤ T) => (hg t).trans (by rw [min_eq_left ht])) K
  refine ⟨min s T, ?_, min_le_right _ _, ?_⟩
  · have h1 : ((min s T : ℝ≥0) : ℝ≥0∞) ≤ min (stepTime g r K) (T : ℝ≥0∞) :=
      le_min ((ENNReal.coe_le_coe.2 (min_le_left _ _)).trans hs.le)
        (ENNReal.coe_le_coe.2 (min_le_right _ _))
    rw [hloc] at h1
    exact h1.trans (min_le_left _ _)
  · have h0 : min (0 : ℝ≥0) T = 0 := min_eq_left zero_le
    rw [hg s, hg 0, h0] at has
    exact has

/-- **Transfer of an exit-before-the-`K`-th-step event to an unstopped path.** Let `f, b : ℝ≥0 → E`, a time
`T` and an increasing time change `φ` with `‖f t - b (min (φ t) T)‖ ≤ κ` for every `t`, that is, `f` is within
`κ` of `b` stopped at time `T`, modulo `φ`. If `f` reaches distance `a` from `f 0` strictly before its `K`-th
displacement time of size `s`, and `2 s + 2 κ ≤ r`, then `b` reaches distance `a - 2 κ` from `b 0` at a time
`u ≤ T` which is at most its `K`-th displacement time of size `r`. -/
theorem exists_le_stepTime_of_norm_sub_comp_stopped_le {f b : ℝ≥0 → E} {T : ℝ≥0} (φ : ℝ≥0 ≃o ℝ≥0)
    {s r κ a : ℝ} (hfb : ∀ t, ‖f t - b (min (φ t) T)‖ ≤ κ) (hr : 2 * s + 2 * κ ≤ r) {K : ℕ}
    (h : ∃ t : ℝ≥0, (t : ℝ≥0∞) < stepTime f s K ∧ a ≤ ‖f t - f 0‖) :
    ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ stepTime b r K ∧ u ≤ T ∧ a - 2 * κ ≤ ‖b u - b 0‖ :=
  exists_le_stepTime_of_stopped (g := fun t => b (min t T)) (fun _ => rfl)
    (exists_lt_stepTime_of_norm_sub_comp_le (g := fun t => b (min t T)) φ hfb hr h)

end StepTimeStopped

end LatticeProb
