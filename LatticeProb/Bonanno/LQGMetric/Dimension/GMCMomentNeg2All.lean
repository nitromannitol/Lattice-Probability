/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentNeg2All at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCMomentNeg2Mom

/-!
# All negative moments of discrete GMC sums (P2-NEGMOM)

`DGMC.LogCorr.exists_uniform_neg_moment` (node (N2) of `handoff/P2-KAHANE3.md`): for a
`β`-log-correlated family with `0 < β < 4` and every `q < 0`,
`sup_{n ≤ j} E gM_n([0,1]²)^q < ∞`.

Berestycki–Powell arXiv:2404.16642, Theorem `T:negmom` (`GMCproperties.tex` l. 1719–1745, after
Molchan): the bootstrap `LogCorr.integral_gM_neg_le` (`m = 2`) passes from `[q₀, 0]` to
`[N q₀, 0]`; the base interval `[q₀, 0]` comes from (N1) `LogCorr.exists_neg_moment_base` and
`y^q ≤ 1 + y^{q₀}`; scales `n < 2` use the a priori bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal

namespace LQGMetric

namespace DGMC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → ℂ → Ω → ℝ} {β c : ℝ}

lemma rpow_le_one_add_rpow {y q q₀ : ℝ} (hy : 0 < y) (hq₀ : q₀ ≤ q) (hq : q ≤ 0) :
    y ^ q ≤ 1 + y ^ q₀ := by
  by_cases h1 : 1 ≤ y
  · have := Real.rpow_le_one_of_one_le_of_nonpos h1 hq
    have := Real.rpow_nonneg hy.le q₀
    linarith
  · push Not at h1
    have := Real.rpow_le_rpow_of_exponent_ge hy h1.le hq₀
    linarith

/-- **(N2): all negative moments, uniformly in `n ≤ j`** (BP Theorem `T:negmom`) -/
theorem LogCorr.exists_uniform_neg_moment (hZ : LogCorr Z P β c) (hβ : 0 < β) (hβ4 : β < 4)
    {q : ℝ} (hq : q < 0) :
    ∃ C : ℝ, ∀ n j : ℕ, n ≤ j → ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤ C := by
  have hP := hZ.isProb
  obtain ⟨q₀, hq₀, C₀, hC₀⟩ := hZ.exists_neg_moment_base hβ hβ4
  set N := (grp0 2).card
  have hN2 : 2 ≤ N := le_card_grp0 2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the induction over the intervals `[N^i q₀, 0]`
  have key : ∀ i : ℕ, ∀ q : ℝ, (N : ℝ) ^ i * q₀ ≤ q → q ≤ 0 →
      ∃ C : ℝ, ∀ n j : ℕ, n ≤ j → ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P ≤ C := by
    intro i
    induction i with
    | zero =>
      intro q hq0 hq
      refine ⟨1 + C₀, fun n j hnj => ?_⟩
      have hint := hZ.integrable_gM_rpow_nonpos n j (grid_nonempty' j) hq
      have hint₀ := hZ.integrable_gM_rpow_nonpos n j (grid_nonempty' j) hq₀.le
      calc ∫ ω, gM (Z n) P j (grid j) ω ^ q ∂P
          ≤ ∫ ω, (1 + gM (Z n) P j (grid j) ω ^ q₀) ∂P :=
            integral_mono hint ((integrable_const 1).add hint₀) fun ω =>
              rpow_le_one_add_rpow (gM_pos _ _ (grid_nonempty' j) ω) (by simpa using hq0) hq
        _ ≤ 1 + C₀ := by
            rw [integral_add (integrable_const 1) hint₀, integral_const, probReal_univ,
              smul_eq_mul, one_mul]
            linarith [hC₀ n j hnj]
    | succ i ih =>
      intro q hq0 hq
      obtain ⟨C', hC'⟩ := ih (q / N) (by
        rw [le_div_iff₀ hN0, pow_succ] at *
        linarith) (div_nonpos_of_nonpos_of_nonneg hq hN0.le)
      set A := Real.exp (q * (q - 1) * (β * ((2 : ℕ) * Real.log 2) + 2 * c) / 2) *
        ((N : ℝ) * (4 : ℝ)⁻¹ ^ 2) ^ q
      set B := Real.exp (q * (q - 1) * (β * (2 * Real.log 2) + c) / 2)
      refine ⟨max B (A * C' ^ N), fun n j hnj => ?_⟩
      by_cases hn : n < 2
      · refine (hZ.integral_gM_grid_rpow_le_apriori_neg n j hq).trans (le_trans ?_ (le_max_left _ _))
        refine Real.exp_le_exp.2 ?_
        have h1 : (n : ℝ) ≤ 2 := by exact_mod_cast hn.le
        have h2 : 0 ≤ q * (q - 1) := mul_nonneg_of_nonpos_of_nonpos hq (by linarith)
        have h3 : β * (n * Real.log 2) ≤ β * (2 * Real.log 2) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h1 (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) hβ.le
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_left h3 c) h2)
          (by norm_num)
      · push Not at hn
        obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hn.trans hnj)
        refine (hZ.integral_gM_neg_le hβ.le hq 2 l k).trans (le_trans ?_ (le_max_right _ _))
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (integral_nonneg fun ω => Real.rpow_nonneg (gM_nonneg _ _ _ _) _)
          (hC' l k (by omega)) _
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (q / q₀) (show (1 : ℝ) < N by exact_mod_cast (by omega : 1 < N))
  refine key i q ?_ hq.le
  have := (div_lt_iff_of_neg hq₀).1 hi
  linarith

end DGMC

end LQGMetric
