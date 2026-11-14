/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# The right limit through the nonnegative rationals of a monotone skeleton

For a function `a : ℚ≥0 → ℝ≥0` the right limit through the nonnegative rationals is
`t ↦ inf {a q : q ∈ ℚ≥0, q > t}`.  When `a` is nondecreasing and locally uniformly continuous on `ℚ≥0` (for
every bound `N` and tolerance `1 / (k + 1)` there is a scale `1 / (j + 1)` such that rationals in `[0, N]`
at distance `< 1 / (j + 1)` have values within `1 / (k + 1)`), this right limit is a continuous function of
`t ∈ ℝ≥0`.  The hypothesis is stated by countable quantifiers, so that the set of skeletons satisfying it is
measurable for a family of measurable skeletons.

* `nnratRightInf`: the right limit through the nonnegative rationals;
* `nnratRightInf_le`, `le_nnratRightInf`, `monotone_nnratRightInf`: the elementary sandwich;
* `continuous_nnratRightInf`: continuity under the modulus hypothesis.
-/

set_option autoImplicit false

open scoped NNReal

noncomputable section

namespace LatticeProb

/-- Between two nonnegative reals `s < t` there is a nonnegative rational. -/
theorem exists_nnrat_between_nnreal {s t : ℝ≥0} (h : s < t) :
    ∃ q : ℚ≥0, s < (q : ℝ≥0) ∧ (q : ℝ≥0) < t := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < t from h)
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ s := s.coe_nonneg
    exact_mod_cast this.trans hq1.le
  exact ⟨⟨q, hq0⟩, by exact_mod_cast hq1, by exact_mod_cast hq2⟩

/-- Every nonnegative real is within `η > 0` above a nonnegative rational below it. -/
theorem exists_nnrat_le_lt_add (x : ℝ≥0) {η : ℝ≥0} (hη : 0 < η) :
    ∃ p : ℚ≥0, (p : ℝ≥0) ≤ x ∧ x < (p : ℝ≥0) + η := by
  by_cases hx : x < η
  · exact ⟨0, by simp, by simpa using hx⟩
  · have hx := not_lt.1 hx
    have hx0 : 0 < x := lt_of_lt_of_le hη hx
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_between_nnreal (tsub_lt_self hx0 hη)
    refine ⟨p, hp2.le, ?_⟩
    have : x - η + η = x := tsub_add_cancel_of_le hx
    calc x = x - η + η := this.symm
      _ < (p : ℝ≥0) + η := by gcongr

/-- **The right limit through the nonnegative rationals**: `t ↦ inf {a q : q ∈ ℚ≥0, q > t}`. -/
def nnratRightInf (a : ℚ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  ⨅ q : {q : ℚ≥0 // t < (q : ℝ≥0)}, a q.1

theorem nnratRightInf_le {a : ℚ≥0 → ℝ≥0} {t : ℝ≥0} {q : ℚ≥0} (h : t < (q : ℝ≥0)) :
    nnratRightInf a t ≤ a q :=
  ciInf_le (OrderBot.bddBelow _) (⟨q, h⟩ : {q : ℚ≥0 // t < (q : ℝ≥0)})

theorem nonempty_nnratRightInf_index (t : ℝ≥0) : Nonempty {q : ℚ≥0 // t < (q : ℝ≥0)} := by
  obtain ⟨q, hq, -⟩ := exists_nnrat_between_nnreal (show t < t + 1 by simp)
  exact ⟨⟨q, hq⟩⟩

theorem le_nnratRightInf {a : ℚ≥0 → ℝ≥0} (hmono : Monotone a) {s : ℝ≥0} {p : ℚ≥0}
    (hp : (p : ℝ≥0) ≤ s) : a p ≤ nnratRightInf a s := by
  have := nonempty_nnratRightInf_index s
  exact le_ciInf fun q => hmono (by exact_mod_cast hp.trans q.2.le)

theorem monotone_nnratRightInf (a : ℚ≥0 → ℝ≥0) : Monotone (nnratRightInf a) := by
  intro s t hst
  have := nonempty_nnratRightInf_index t
  exact le_ciInf fun q =>
    ciInf_le (OrderBot.bddBelow _) (⟨q.1, hst.trans_lt q.2⟩ : {q : ℚ≥0 // s < (q : ℝ≥0)})

/-- **Continuity of the right limit of a monotone, locally uniformly continuous rational skeleton.** -/
theorem continuous_nnratRightInf (a : ℚ≥0 → ℝ≥0) (hmono : Monotone a)
    (hmod : ∀ N k : ℕ, ∃ j : ℕ, ∀ p q : ℚ≥0, (p : ℝ) ≤ N → (q : ℝ) ≤ N →
      |(p : ℝ) - q| < 1 / ((j : ℝ) + 1) → |(a p : ℝ) - (a q : ℝ)| ≤ 1 / ((k : ℝ) + 1)) :
    Continuous (nnratRightInf a) := by
  rw [Metric.continuous_iff]
  intro t₀ ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((t₀ : ℝ) + 1)
  obtain ⟨j, hj⟩ := hmod N k
  have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / (3 * ((j : ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 3 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h3 : 3 * δ = 1 / ((j : ℝ) + 1) := by
    rw [hδ]; field_simp
  set η : ℝ≥0 := ⟨δ, hδ0.le⟩ with hη
  have hη0 : 0 < η := by rw [hη]; exact_mod_cast hδ0
  have hηδ : (η : ℝ) = δ := rfl
  -- the key estimate for `s ≤ t`
  have key : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) - s < δ → (t : ℝ) < t₀ + δ →
      |(nnratRightInf a t : ℝ) - nnratRightInf a s| < ε := by
    intro s t hst hts htt
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_le_lt_add s hη0
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_between_nnreal (show t < t + η by simpa using hη0)
    have hbs : (a p : ℝ) ≤ nnratRightInf a s :=
      NNReal.coe_le_coe.2 (le_nnratRightInf hmono hp1)
    have hbt : (nnratRightInf a t : ℝ) ≤ a q := NNReal.coe_le_coe.2 (nnratRightInf_le hq1)
    have hmo : (nnratRightInf a s : ℝ) ≤ nnratRightInf a t :=
      NNReal.coe_le_coe.2 (monotone_nnratRightInf a hst)
    have hp1' : (p : ℝ) ≤ s := by exact_mod_cast hp1
    have hp2' : (s : ℝ) < p + δ := by exact_mod_cast hp2
    have hq1' : (t : ℝ) < q := by exact_mod_cast hq1
    have hq2' : (q : ℝ) < t + δ := by exact_mod_cast hq2
    have hst' : (s : ℝ) ≤ t := hst
    have hpq : |(p : ℝ) - q| < 1 / ((j : ℝ) + 1) := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    have hpN : (p : ℝ) ≤ N := by linarith
    have hqN : (q : ℝ) ≤ N := by linarith
    have := hj p q hpN hqN hpq
    rw [abs_sub_comm] at this
    rw [abs_of_nonneg (by linarith)]
    have h2 : (a q : ℝ) - a p ≤ |(a q : ℝ) - a p| := le_abs_self _
    linarith
  refine ⟨δ, hδ0, fun s hs => ?_⟩
  rw [NNReal.dist_eq] at hs
  rw [NNReal.dist_eq]
  obtain ⟨hs1, hs2⟩ := abs_lt.1 hs
  rcases le_total s t₀ with h | h
  · have h' : (s : ℝ) ≤ t₀ := h
    have := key s t₀ h (by linarith) (by linarith)
    rwa [abs_sub_comm] at this
  · have h' : (t₀ : ℝ) ≤ s := h
    exact key t₀ s h (by linarith) (by linarith)

end LatticeProb

end
