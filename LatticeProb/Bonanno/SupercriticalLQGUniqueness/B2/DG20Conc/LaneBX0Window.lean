/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Window at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Slope
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Window
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Uniqueness

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

private theorem finite_prefix_window
    (lam low upp : ℕ → ℝ)
    (hlam : ∀ m, 0 < lam m) (hlo : ∀ m, 0 < low m)
    (hup : ∀ m, 0 < upp m) (N : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ m, m < N → c * low m ≤ lam m ∧ lam m ≤ C * upp m := by
  induction N with
  | zero =>
      exact ⟨1, 1, by norm_num, by norm_num, by intro m hm; omega⟩
  | succ N ih =>
      obtain ⟨c, C, hc, hC, hprev⟩ := ih
      let c' : ℝ := min c (lam N / low N)
      let C' : ℝ := max C (lam N / upp N)
      have hc' : 0 < c' := lt_min hc (div_pos (hlam N) (hlo N))
      have hC' : 0 < C' := lt_of_lt_of_le hC (le_max_left _ _)
      refine ⟨c', C', hc', hC', ?_⟩
      intro m hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · obtain ⟨hml, hmu⟩ := hprev m h
        constructor
        · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hlo m).le).trans hml
        · exact hmu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hup m).le)
      · subst m
        constructor
        · calc c' * low N ≤ (lam N / low N) * low N :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (hlo N).le
            _ = lam N := div_mul_cancel₀ _ (ne_of_gt (hlo N))
        · calc lam N = (lam N / upp N) * upp N :=
              (div_mul_cancel₀ _ (ne_of_gt (hup N))).symm
            _ ≤ C' * upp N :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (hup N).le

private theorem dyadic_window_of_slope
    (lam : ℕ → ℝ) (α ζ : ℝ)
    (hlam : ∀ m, 0 < lam m) (hζ : 0 < ζ)
    (hSlope : Tendsto
      (fun m : ℕ => Real.logb 2 (lam m) / (m : ℝ))
      atTop (𝓝 (-α))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ,
      c * (2 : ℝ) ^ (-(α + ζ) * (m : ℝ)) ≤ lam m ∧
      lam m ≤ C * (2 : ℝ) ^ (-(α - ζ) * (m : ℝ)) := by
  have hnear : ∀ᶠ m : ℕ in atTop,
      -α - ζ < Real.logb 2 (lam m) / (m : ℝ) ∧
      Real.logb 2 (lam m) / (m : ℝ) < -α + ζ :=
    hSlope.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hnear
  let N := max N₀ 1
  have htail : ∀ m : ℕ, N ≤ m →
      (2 : ℝ) ^ (-(α + ζ) * (m : ℝ)) ≤ lam m ∧
      lam m ≤ (2 : ℝ) ^ (-(α - ζ) * (m : ℝ)) := by
    intro m hm
    have hm0 : 0 < (m : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) ((le_max_right _ _).trans hm)
    have hq := hN₀ m ((le_max_left _ _).trans hm)
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog : Real.logb 2 (lam m) * Real.log 2 = Real.log (lam m) := by
      rw [Real.logb, div_mul_cancel₀ _ (ne_of_gt hlog2)]
    have hlow : (-(α + ζ) * (m : ℝ)) * Real.log 2 ≤ Real.log (lam m) := by
      have hq' := (lt_div_iff₀ hm0).mp hq.1
      rw [← hlog]
      nlinarith [mul_pos (sub_pos.mpr (by linarith : -α - ζ <
        Real.logb 2 (lam m) / (m : ℝ))) hlog2]
    have hupp : Real.log (lam m) ≤ (-(α - ζ) * (m : ℝ)) * Real.log 2 := by
      have hq' := (div_lt_iff₀ hm0).mp hq.2
      rw [← hlog]
      nlinarith
    constructor
    · exact (Real.rpow_le_iff_le_log (by norm_num : (0 : ℝ) < 2) (hlam m)).2
        (by simpa [mul_comm] using hlow)
    · exact (Real.le_rpow_iff_log_le (hlam m) (by norm_num : (0 : ℝ) < 2)).2
        (by simpa [mul_comm] using hupp)
  obtain ⟨c, C, hc, hC, hprefix⟩ :=
    finite_prefix_window lam
      (fun m => (2 : ℝ) ^ (-(α + ζ) * (m : ℝ)))
      (fun m => (2 : ℝ) ^ (-(α - ζ) * (m : ℝ)))
      hlam (fun m => by positivity) (fun m => by positivity) N
  refine ⟨min c 1, max C 1, lt_min hc (by norm_num),
    lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro m
  by_cases hm : m < N
  · obtain ⟨hl, hu⟩ := hprefix m hm
    constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hl
    · exact hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · obtain ⟨hl, hu⟩ := htail m (Nat.le_of_not_gt hm)
    constructor
    · calc min c 1 * _ ≤ 1 * _ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ ≤ lam m := by simpa using hl
    · calc lam m ≤ 1 * _ := by simpa using hu
          _ ≤ max C 1 * _ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

 
theorem laneB_whiteNoise_median_window
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ m : ℕ,
        c * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (m : ℝ)) ≤
          lambdaN (ξ : ℝ) W P m ∧
        lambdaN (ξ : ℝ) W P m ≤
          C * (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q - ζ) * (m : ℝ)) := by
  obtain ⟨W₀, hW₀⟩ := LQGMetric.WhiteNoise.exists_isWhiteNoise
  let P₀ := LQGDimension.ExistAsm.stdP
  letI := hW₀.isProbabilityMeasure
  obtain ⟨α, hα⟩ := laneB_reference_slope (P := P₀) (W := W₀) hW₀ ξ.property
  have hslope := Exponent.SlopeAssembly.slope_of_normalized_error
    (lambdaN (ξ : ℝ) W₀ P₀) α hα
  have hExp : IsLFPPExponent ξ ((1 - α) / (ξ : ℝ)) :=
    Exponent.Median.isLFPPExponent_of_dyadic_median_slope P₀ hW₀ ξ α hslope
  have hEq : Q = (1 - α) / (ξ : ℝ) :=
    Exponent.isLFPPExponent_unique ξ Q _ hQ hExp
  have hαeq : α = 1 - (ξ : ℝ) * Q := by
    have hξ : (ξ : ℝ) ≠ 0 := ne_of_gt ξ.property
    rw [hEq]
    field_simp
    ring
  obtain ⟨c, C, hc, hC, hw⟩ := dyadic_window_of_slope
    (lambdaN (ξ : ℝ) W₀ P₀) α ζ
    (fun m => Exponent.AnnularRecursion.lambdaN_pos' hW₀ (ξ : ℝ) m) hζ hslope
  refine ⟨c, C, hc, hC, ?_⟩
  intro Ω _ P W hW m
  have heq := Exponent.Median.lambdaN_eq_of_whiteNoise hW hW₀ (ξ : ℝ) m
  rw [heq]
  simpa only [hαeq] using hw m

end SupercriticalLQGUniqueness.B2.DG20Conc
