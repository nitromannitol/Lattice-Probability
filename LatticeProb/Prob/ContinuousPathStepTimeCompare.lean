import LatticeProb.Prob.ContinuousPathStepTimes

/-!
# Comparison of successive displacement times

For paths `f g : ℝ≥0 → E` in a normed group, `stepTime f r` are the successive displacement times
of `f` of size `r` (`LatticeProb.stepTime`). This file compares them for two paths that are close,
and for a path and its time reparametrizations.

* `stepTime_le_stepTime_of_norm_sub_le`: if `‖f t - g t‖ ≤ κ` for all `t` and `2 s + 2 κ ≤ r`, then
  `σ_j(f, s) ≤ σ_j(g, r)` for every `j`. No continuity is needed.
* `stepTime_comp_orderIso`: for an increasing homeomorphism `φ` of `ℝ≥0` (an order isomorphism), the
  displacement times of `g ∘ φ` are the images under `φ⁻¹` of those of `g`
  (`coe_lt_stepTime_comp_iff`: `t < σ_j(g ∘ φ)` iff `φ t < σ_j(g)`).
* `exists_lt_stepTime_of_norm_sub_comp_le`: the two combined. If `‖f t - g (φ t)‖ ≤ κ` for all `t`
  and `f` leaves the ball of radius `a` around `f 0` before its `K`-th displacement time of size `s`,
  then `g` leaves the ball of radius `a - 2 κ` around `g 0` before its `K`-th displacement time of
  size `r`, for every `r ≥ 2 s + 2 κ`. This is the form in which a bound on the distance of two
  curves modulo time parametrization transfers an exit-before-the-`K`-th-step event.
-/

open Set
open scoped NNReal ENNReal

namespace LatticeProb

section StepTimeCompare

variable {E : Type*} [NormedAddCommGroup E]

/-- Successive displacement times are monotone under uniform perturbation: if `f` stays within `κ`
of `g` and `2 s + 2 κ ≤ r`, then the `j`-th displacement time of `f` of size `s` comes no later
than the `j`-th displacement time of `g` of size `r`. -/
theorem stepTime_le_stepTime_of_norm_sub_le {f g : ℝ≥0 → E} {s r κ : ℝ}
    (hfg : ∀ t, ‖f t - g t‖ ≤ κ) (hr : 2 * s + 2 * κ ≤ r) :
    ∀ j, stepTime f s j ≤ stepTime g r j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases hg : stepTime g r j = ⊤
    · rw [stepTime_succ_of_eq_top hg]; exact le_top
    have hf : stepTime f s j ≠ ⊤ := ne_top_of_le_ne_top hg ih
    rw [stepTime_succ_of_ne_top hg, stepTime_succ_of_ne_top hf]
    have haa : (stepTime f s j).toNNReal ≤ (stepTime g r j).toNNReal :=
      ENNReal.toNNReal_mono hg ih
    set a := (stepTime g r j).toNNReal
    set a' := (stepTime f s j).toNNReal
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨x, hx1, hx2⟩ := exists_between hlt
    lift x to ℝ≥0 using ne_top_of_lt hx2
    obtain ⟨t, ⟨hat, hrt⟩, htx⟩ := exists_mem_of_nextStep_lt hx1
    have htlt : (t : ℝ≥0∞) < nextStep f s a' := lt_trans (by exact_mod_cast htx) hx2
    have h1 : ‖f t - f a'‖ < s := norm_lt_of_lt_nextStep (le_trans haa hat) htlt
    have h2 : ‖f a - f a'‖ < s :=
      norm_lt_of_lt_nextStep haa (lt_of_le_of_lt (by exact_mod_cast hat) htlt)
    have e1 := norm_sub_le_norm_sub_add_norm_sub (g t) (f t) (g a)
    have e2 := norm_sub_le_norm_sub_add_norm_sub (f t) (f a') (g a)
    have e3 := norm_sub_le_norm_sub_add_norm_sub (f a') (f a) (g a)
    have e4 : ‖g t - f t‖ ≤ κ := by rw [norm_sub_rev]; exact hfg t
    have e5 : ‖f a' - f a‖ < s := by rw [norm_sub_rev]; exact h2
    have e6 := hfg a
    linarith

/-- The displacement set of a reparametrized path is the preimage of the displacement set. -/
lemma stepSet_comp_orderIso (g : ℝ≥0 → E) (r : ℝ) (φ : ℝ≥0 ≃o ℝ≥0) (a : ℝ≥0) :
    stepSet (g ∘ φ) r a = φ ⁻¹' stepSet g r (φ a) := by
  ext t
  simp [stepSet, φ.le_iff_le]

lemma nextStep_comp_orderIso (g : ℝ≥0 → E) (r : ℝ) (φ : ℝ≥0 ≃o ℝ≥0) (a : ℝ≥0) :
    (nextStep (g ∘ φ) r a = ⊤ ∧ nextStep g r (φ a) = ⊤) ∨
      ∃ t : ℝ≥0, nextStep (g ∘ φ) r a = t ∧ nextStep g r (φ a) = (φ t : ℝ≥0) := by
  have hS := stepSet_comp_orderIso g r φ a
  by_cases hne : (stepSet g r (φ a)).Nonempty
  · have hne' : (stepSet (g ∘ φ) r a).Nonempty := by
      obtain ⟨u, hu⟩ := hne
      exact ⟨φ.symm u, by rw [hS]; simpa using hu⟩
    refine Or.inr ⟨sInf (stepSet (g ∘ φ) r a), by simp [nextStep, hne'], ?_⟩
    have himg : φ '' stepSet (g ∘ φ) r a = stepSet g r (φ a) := by
      rw [hS]; exact image_preimage_eq _ φ.surjective
    rw [φ.map_csInf' hne' (OrderBot.bddBelow _), himg]
    simp [nextStep, hne]
  · have hne' : ¬ (stepSet (g ∘ φ) r a).Nonempty := by
      rintro ⟨u, hu⟩
      rw [hS] at hu
      exact hne ⟨φ u, hu⟩
    exact Or.inl ⟨by simp [nextStep, hne'], by simp [nextStep, hne]⟩

/-- The displacement times of `g ∘ φ`, for an order isomorphism `φ` of `ℝ≥0`, are the images under
`φ⁻¹` of the displacement times of `g`: both are `⊤`, or both are finite and correspond under `φ`. -/
theorem stepTime_comp_orderIso (g : ℝ≥0 → E) (r : ℝ) (φ : ℝ≥0 ≃o ℝ≥0) (j : ℕ) :
    (stepTime (g ∘ φ) r j = ⊤ ∧ stepTime g r j = ⊤) ∨
      ∃ t : ℝ≥0, stepTime (g ∘ φ) r j = t ∧ stepTime g r j = (φ t : ℝ≥0) := by
  induction j with
  | zero =>
    have h0 : φ 0 = 0 := le_antisymm (φ.le_symm_apply.1 zero_le) zero_le
    exact Or.inr ⟨0, by simp, by simp [h0]⟩
  | succ j ih =>
    rcases ih with ⟨h1, h2⟩ | ⟨t, h1, h2⟩
    · exact Or.inl ⟨stepTime_succ_of_eq_top h1, stepTime_succ_of_eq_top h2⟩
    · have h1' : stepTime (g ∘ φ) r j ≠ ⊤ := by rw [h1]; exact ENNReal.coe_ne_top
      have h2' : stepTime g r j ≠ ⊤ := by rw [h2]; exact ENNReal.coe_ne_top
      rw [stepTime_succ_of_ne_top h1', stepTime_succ_of_ne_top h2', h1, h2,
        ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
      exact nextStep_comp_orderIso g r φ t

lemma coe_lt_stepTime_comp_iff (g : ℝ≥0 → E) (r : ℝ) (φ : ℝ≥0 ≃o ℝ≥0) (j : ℕ) (t : ℝ≥0) :
    (t : ℝ≥0∞) < stepTime (g ∘ φ) r j ↔ ((φ t : ℝ≥0) : ℝ≥0∞) < stepTime g r j := by
  rcases stepTime_comp_orderIso g r φ j with ⟨h1, h2⟩ | ⟨u, h1, h2⟩
  · rw [h1, h2]; simp
  · rw [h1, h2, ENNReal.coe_lt_coe, ENNReal.coe_lt_coe, φ.lt_iff_lt]

/-- Transfer of an exit-before-the-`K`-th-step event between two paths at distance `≤ κ` modulo
an increasing time change `φ`: if `f` reaches distance `a` from `f 0` strictly before its `K`-th
displacement time of size `s`, then `g` reaches distance `a - 2 κ` from `g 0` strictly before its
`K`-th displacement time of size `r`, whenever `2 s + 2 κ ≤ r`. -/
theorem exists_lt_stepTime_of_norm_sub_comp_le {f g : ℝ≥0 → E} (φ : ℝ≥0 ≃o ℝ≥0) {s r κ a : ℝ}
    (hfg : ∀ t, ‖f t - g (φ t)‖ ≤ κ) (hr : 2 * s + 2 * κ ≤ r) {K : ℕ}
    (h : ∃ t : ℝ≥0, (t : ℝ≥0∞) < stepTime f s K ∧ a ≤ ‖f t - f 0‖) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < stepTime g r K ∧ a - 2 * κ ≤ ‖g t - g 0‖ := by
  obtain ⟨t, ht, hat⟩ := h
  have hle := stepTime_le_stepTime_of_norm_sub_le (g := g ∘ φ) hfg hr K
  have hlt : ((φ t : ℝ≥0) : ℝ≥0∞) < stepTime g r K :=
    (coe_lt_stepTime_comp_iff g r φ K t).1 (lt_of_lt_of_le ht hle)
  have h0 : φ 0 = 0 := le_antisymm (φ.le_symm_apply.1 zero_le) zero_le
  refine ⟨φ t, hlt, ?_⟩
  have e1 := norm_sub_le_norm_sub_add_norm_sub (f t) (g (φ t)) (f 0)
  have e2 := norm_sub_le_norm_sub_add_norm_sub (g (φ t)) (g (φ 0)) (f 0)
  have e3 : ‖g (φ 0) - f 0‖ ≤ κ := by rw [norm_sub_rev]; exact hfg 0
  have e4 := hfg t
  rw [h0] at e2 e3
  linarith

end StepTimeCompare

end LatticeProb
