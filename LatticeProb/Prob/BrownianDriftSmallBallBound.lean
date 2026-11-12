/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianDriftSmallBall
import LatticeProb.Prob.GaussianFreezing

/-!
# Small-ball bound for Brownian motion with positive drift

For a Brownian motion `B` and `c, δ > 0`, the event `closedStay B c δ s` that `B t + c t ≥ -δ`
for every `t ≤ s` has probability at most `C δ` for `s = 1`, uniformly in `0 < δ ≤ 1/4`, where
`C` depends only on `c`.

The proof is a one-scale recursion.  For `16 δ² ≤ s`, splitting according to whether `B_s + c s`
is above or below `√s / 2`, the survival comparison of the previous module bounds the high part
by `2 δ / √s + 2 c δ`, and Gaussian freezing across the time `s / 2` bounds the low part by
half of the probability of the event at the scale `s / 2`.  Iterating down the dyadic scales
until `√s` is of the order of `δ` gives the bound.

## Main results

* `LatticeProb.measureReal_closedStay_le_half`: the one-scale recursion.
* `LatticeProb.measureReal_closedStay_one_le`: `P(closedStay B c δ 1) ≤ C δ`.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-- A real inequality used in the recursion: if `g (1 - exp (-2 c (δ + σ/2))) ≤ 1 - exp (-2 c δ)`
and `g ≥ 0`, then `g ≤ 2 δ / σ + 2 c δ`. -/
theorem ratio_bound {c δ σ g : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hσ : 0 < σ) (hg0 : 0 ≤ g)
    (hg : g * (1 - Real.exp (-(2 * c * (δ + σ / 2)))) ≤ 1 - Real.exp (-(2 * c * δ))) :
    g ≤ 2 * δ / σ + 2 * c * δ := by
  have hx : 0 < c * σ := mul_pos hc hσ
  have hexp : Real.exp (-(c * σ)) ≤ 1 / (1 + c * σ) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (c * σ)])
  have hmono : Real.exp (-(2 * c * (δ + σ / 2))) ≤ Real.exp (-(c * σ)) :=
    Real.exp_le_exp.2 (by nlinarith [mul_pos hc hδ])
  have hw : c * σ / (1 + c * σ) ≤ 1 - Real.exp (-(2 * c * (δ + σ / 2))) := by
    have : c * σ / (1 + c * σ) = 1 - 1 / (1 + c * σ) := by field_simp; ring
    linarith
  have hp : 1 - Real.exp (-(2 * c * δ)) ≤ 2 * c * δ := by
    linarith [Real.add_one_le_exp (-(2 * c * δ))]
  have hg' : g * (c * σ / (1 + c * σ)) ≤ 2 * c * δ :=
    calc g * (c * σ / (1 + c * σ)) ≤ g * (1 - Real.exp (-(2 * c * (δ + σ / 2)))) :=
          mul_le_mul_of_nonneg_left hw hg0
      _ ≤ 1 - Real.exp (-(2 * c * δ)) := hg
      _ ≤ 2 * c * δ := hp
  have h3 : g * (c * σ) ≤ 2 * c * δ * (1 + c * σ) := by
    have h1pos : 0 < 1 + c * σ := by positivity
    have h5 := mul_le_mul_of_nonneg_right hg' h1pos.le
    have e : g * (c * σ / (1 + c * σ)) * (1 + c * σ) = g * (c * σ) := by field_simp
    linarith
  have e2 : 2 * δ / σ + 2 * c * δ = 2 * c * δ * (1 + c * σ) / (c * σ) := by
    field_simp
  rw [e2, le_div_iff₀ hx]
  exact h3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **One-scale recursion for the small-ball bound.**  If `16 δ² ≤ s`, the chance of staying above
`-δ` up to time `s` is at most `2 δ / √s + 2 c δ` plus half of the chance of staying above `-δ`
up to time `s / 2`. -/
theorem measureReal_closedStay_le_half (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c)
    {δ : ℝ} (hδ : 0 < δ) (s : ℝ≥0) (hs : 16 * δ ^ 2 ≤ (s : ℝ)) :
    P.real (closedStay B c δ s) ≤
      2 * δ / √(s : ℝ) + 2 * c * δ + P.real (closedStay B c δ (s / 2)) / 2 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hspos : 0 < (s : ℝ) := lt_of_lt_of_le (by positivity) hs
  have hs0 : 0 < s := by exact_mod_cast hspos
  have hσpos : 0 < √(s : ℝ) := Real.sqrt_pos.2 hspos
  have hσsq : (√(s : ℝ)) ^ 2 = s := Real.sq_sqrt hspos.le
  set σ : ℝ := √(s : ℝ) with hσ
  have h4 : 4 * δ ≤ σ := by
    rw [hσ, Real.le_sqrt' (by positivity)]
    nlinarith
  have hrs : s / 2 < s := half_lt_self hs0
  have hhalf : (((s / 2 : ℝ≥0)) : ℝ) = (s : ℝ) / 2 := by push_cast; ring
  set G1 : Set Ω := closedStay B c δ s ∩ {ω | σ / 2 ≤ B s ω + c * s} with hG1
  set G2 : Set Ω := closedStay B c δ (s / 2) ∩ {ω | B s ω + c * s ∈ Set.Icc (-δ) (σ / 2)}
    with hG2
  have hsub : closedStay B c δ s ⊆ G1 ∪ G2 := by
    intro ω hω
    by_cases h : σ / 2 ≤ B s ω + c * s
    · exact Or.inl ⟨hω, h⟩
    · refine Or.inr ⟨closedStay_anti hrs.le hω, ?_, ?_⟩
      · have := hω s le_rfl
        linarith
      · exact (not_le.1 h).le
  -- the high part
  have hb1 : P.real G1 ≤ 2 * δ / σ + 2 * c * δ := by
    have h := measureReal_closedStay_inter_ge_mul_le hB hm hcont hc hδ s (σ / 2)
    exact ratio_bound hc hδ hσpos measureReal_nonneg h
  -- the low part
  have hden : 3 / 2 * σ ≤ √(2 * Real.pi * ((s : ℝ) - ((s / 2 : ℝ≥0) : ℝ))) := by
    rw [Real.le_sqrt' (by positivity), hhalf]
    nlinarith [Real.pi_gt_three, hσsq]
  have hdenpos : 0 < √(2 * Real.pi * ((s : ℝ) - ((s / 2 : ℝ≥0) : ℝ))) := by linarith
  have hb2 : P.real G2 ≤ P.real (closedStay B c δ (s / 2)) *
      ((σ / 2 - -δ) / √(2 * Real.pi * ((s : ℝ) - ((s / 2 : ℝ≥0) : ℝ)))) := by
    have h := measure_inter_drift_mem_Icc_le hB hm hrs
      (measurableSet_closedStay hm hcont c δ (s / 2)) c (show -δ ≤ σ / 2 by linarith)
    have hne : P (closedStay B c δ (s / 2)) * ENNReal.ofReal ((σ / 2 - -δ) /
        √(2 * Real.pi * ((s : ℝ) - ((s / 2 : ℝ≥0) : ℝ)))) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    have h' := ENNReal.toReal_mono hne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (by linarith) hdenpos.le)] at h'
    exact h'
  have hratio : (σ / 2 - -δ) / √(2 * Real.pi * ((s : ℝ) - ((s / 2 : ℝ≥0) : ℝ))) ≤ 1 / 2 := by
    rw [div_le_iff₀ hdenpos]
    linarith
  have hb2' : P.real G2 ≤ P.real (closedStay B c δ (s / 2)) / 2 := by
    calc P.real G2 ≤ _ := hb2
      _ ≤ P.real (closedStay B c δ (s / 2)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hratio measureReal_nonneg
      _ = _ := by ring
  calc P.real (closedStay B c δ s) ≤ P.real (G1 ∪ G2) := measureReal_mono hsub
    _ ≤ P.real G1 + P.real G2 := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- The telescoped form of a recursion `A j ≤ b j + A (j + 1) / 2`. -/
theorem telescope_half (A b : ℕ → ℝ) (m : ℕ) (hrec : ∀ j < m, A j ≤ b j + A (j + 1) / 2) :
    ∀ k ≤ m, A 0 ≤ ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j * b j + (1 / 2 : ℝ) ^ k * A k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hrec k (by omega)
    have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

theorem sqrt_half_pow (j : ℕ) : √((((1 / 2 : ℝ≥0) ^ j : ℝ≥0)) : ℝ) = ((√2) ^ j)⁻¹ := by
  have h2 : ((√2) ^ j) ^ 2 = 2 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
  have : (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ) = (((√2) ^ j)⁻¹) ^ 2 := by
    rw [inv_pow, h2]; push_cast; rw [one_div, inv_pow]
  rw [this, Real.sqrt_sq (by positivity)]

theorem geom_sum_sqrt_two_half_le (m : ℕ) : ∑ j ∈ Finset.range m, (√2 / 2) ^ j ≤ 4 := by
  have h2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hx0 : 0 ≤ √2 / 2 := by positivity
  have hx1 : √2 / 2 < 1 := by linarith
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hx0 hx1
  rw [Finset.range_eq_Ico]
  refine this.trans ?_
  rw [pow_zero, div_le_iff₀ (by linarith)]
  linarith

theorem geom_sum_half_le (m : ℕ) : ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j ≤ 2 := by
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) (x := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)
  rw [Finset.range_eq_Ico]
  refine this.trans ?_
  norm_num

/-- **Small-ball bound.**  For a Brownian motion `B` with continuous paths and `c > 0`, there is
`C` (depending on `c` only) with `P(B t + c t ≥ -δ ∀ t ≤ 1) ≤ C δ` for all `0 < δ ≤ 1/4`. -/
theorem measureReal_closedStay_one_le (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      P.real (closedStay B c δ 1) ≤ C * δ := by
  refine ⟨12 + 4 * c, by positivity, fun δ hδ hδ4 => ?_⟩
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set A : ℕ → ℝ := fun j => P.real (closedStay B c δ ((1 / 2 : ℝ≥0) ^ j)) with hA
  have hA0 : ∀ j, 0 ≤ A j := fun j => measureReal_nonneg
  have hA1 : ∀ j, A j ≤ 1 := fun j => measureReal_le_one
  have hex : ∃ m : ℕ, (1 / 2 : ℝ) ^ m < 16 * δ ^ 2 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  classical
  set m := Nat.find hex with hmdef
  have hm1 : (1 / 2 : ℝ) ^ m < 16 * δ ^ 2 := Nat.find_spec hex
  have hmin : ∀ j < m, ¬ (1 / 2 : ℝ) ^ j < 16 * δ ^ 2 := fun j hj => Nat.find_min hex hj
  set u : ℝ := √2 with hu
  have hrec : ∀ j < m, A j ≤ (2 * δ * u ^ j + 2 * c * δ) + A (j + 1) / 2 := by
    intro j hj
    have hs : 16 * δ ^ 2 ≤ (((1 / 2 : ℝ≥0) ^ j : ℝ≥0) : ℝ) := by
      push_cast
      exact not_lt.1 (hmin j hj)
    have h := measureReal_closedStay_le_half hB hm hcont hc hδ ((1 / 2 : ℝ≥0) ^ j) hs
    have e1 : ((1 / 2 : ℝ≥0) ^ j) / 2 = (1 / 2 : ℝ≥0) ^ (j + 1) := by
      rw [pow_succ, div_eq_mul_one_div]
    have e2 : 2 * δ / √((((1 / 2 : ℝ≥0) ^ j : ℝ≥0)) : ℝ) = 2 * δ * u ^ j := by
      rw [sqrt_half_pow, div_inv_eq_mul]
    rw [e1, e2] at h
    exact h
  have htel := telescope_half A (fun j => 2 * δ * u ^ j + 2 * c * δ) m hrec m le_rfl
  have hsum : ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j * (2 * δ * u ^ j + 2 * c * δ) =
      2 * δ * ∑ j ∈ Finset.range m, (u / 2) ^ j +
        2 * c * δ * ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_one_div u 2, mul_pow]
    ring
  have hg1 := geom_sum_sqrt_two_half_le m
  have hg2 := geom_sum_half_le m
  have hlast : (1 / 2 : ℝ) ^ m * A m ≤ (1 / 2 : ℝ) ^ m := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
    nlinarith [hA1 m]
  have hA0' : A 0 = P.real (closedStay B c δ 1) := by simp [hA]
  rw [← hA0']
  rw [hsum] at htel
  have h16 : 16 * δ ^ 2 ≤ 4 * δ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ 2 * δ),
    mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ 2 * c * δ)]

end LatticeProb
