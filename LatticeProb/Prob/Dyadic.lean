/-
The dyadic skeleton witnesses the supremum of a continuous path.

For the Brownian maximal estimate one bounds the probability that a
continuous path on `[0, T]` ever leaves a band by the probability that it
leaves the band at some dyadic time `k T / 2^n`; the path is uniformly
continuous on the compact interval, so a point where the band is left is
within `a / 2` of a dyadic point.  This is the deterministic heart of the
reduction of a continuous-time maximal inequality to its discrete skeleton.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem dyadic_witness {T : ℝ≥0} {a : ℝ} {ω : Ω}
    (hcont : Continuous (B · ω)) (hmem : ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω|) :
    ∃ (n k : ℕ), (k : ℝ) / 2 ^ n ≤ T ∧ a / 2 ≤ |B (Real.toNNReal ((k : ℝ) / 2 ^ n)) ω| := by
  by_cases ha0 : 0 < a
  · obtain ⟨s, hs, ha⟩ := hmem
    have hcon : ContinuousOn (fun t : ℝ≥0 => B t ω) (Set.Icc (0:ℝ≥0) T) :=
      hcont.continuousOn
    have hcomp : IsCompact (Set.Icc (0:ℝ≥0) T) := isCompact_Icc
    obtain ⟨δ, hδ, huu⟩ := Metric.uniformContinuousOn_iff_le.1
      (hcomp.uniformContinuousOn_of_continuous hcon)
      (a / 2) (by positivity)
    -- choose n with 2 ^ n > max (max T 1) (1/δ)
    obtain ⟨n, hn⟩ := exists_nat_gt (max (max (T : ℝ) 1) (1 / δ))
    have h2n : max (max (T : ℝ) 1) (1 / δ) < (2 ^ n : ℝ) :=
      lt_trans hn (by exact_mod_cast Nat.lt_two_pow_self (n := n))
    have hTn : (T : ℝ) < (2 ^ n : ℝ) := lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) h2n)
    have h1n : (1:ℝ) < (2 ^ n : ℝ) := lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _) h2n)
    have hδn : 1 / δ < (2 ^ n : ℝ) := lt_of_le_of_lt (le_max_right _ _) h2n
    have hδpos : 0 < δ := hδ
    -- k = floor (s * 2^n)
    set k := Nat.floor ((s : ℝ) * (2 ^ n : ℝ)) with hk
    have hs2n : 0 ≤ (s : ℝ) * (2 ^ n : ℝ) := by positivity
    have hk1 : (k : ℝ) ≤ (s : ℝ) * (2 ^ n : ℝ) := Nat.floor_le hs2n
    have hk2 : (s : ℝ) * (2 ^ n : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpos2 : (0:ℝ) < (2 ^ n : ℝ) := by positivity
    -- k/2^n ≤ s ≤ T
    have hks : (k : ℝ) / (2 ^ n : ℝ) ≤ (s : ℝ) := by
      rw [div_le_iff₀ hpos2]
      exact hk1
    have hkT : (k : ℝ) / (2 ^ n : ℝ) ≤ (T : ℝ) := le_trans hks (by exact_mod_cast hs)
    -- |s - k/2^n| < 1/2^n < δ
    have hsub : |(s : ℝ) - (k : ℝ) / (2 ^ n : ℝ)| < 1 / (2 ^ n : ℝ) := by
      have h1 : (s : ℝ) - (k : ℝ) / (2 ^ n : ℝ) < 1 / (2 ^ n : ℝ) := by
        have hlt : (s : ℝ) < ((k : ℝ) + 1) / (2 ^ n : ℝ) :=
          (lt_div_iff₀ hpos2).mpr hk2
        have hdiv : ((k : ℝ) + 1) / (2 ^ n : ℝ)
            = (k : ℝ) / (2 ^ n : ℝ) + 1 / (2 ^ n : ℝ) := by
          rw [add_div]
        rw [hdiv] at hlt
        linarith
      rw [abs_lt]
      constructor
      · linarith
      · exact h1
    have hltδ : |(s : ℝ) - (k : ℝ) / (2 ^ n : ℝ)| < δ := by
      have h1 : 1 < δ * (2 ^ n : ℝ) := by
        have h2 : 1 / δ < (2 ^ n : ℝ) := hδn
        have h3 : 1 / δ * δ < (2 ^ n : ℝ) * δ := by exact mul_lt_mul_of_pos_right h2 hδpos
        rw [div_mul_cancel₀ _ (ne_of_gt hδpos)] at h3
        linarith
      have hltδ : 1 / (2 ^ n : ℝ) < δ := (div_lt_iff₀ hpos2).mpr h1
      exact lt_trans hsub hltδ
    -- t := toNNReal (k/2^n)
    set t : ℝ≥0 := Real.toNNReal ((k : ℝ) / (2 ^ n : ℝ)) with ht
    have htc : (t : ℝ) = (k : ℝ) / (2 ^ n : ℝ) := by
      exact Real.coe_toNNReal _ (by positivity)
    have htT : t ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [htc]
      exact hkT
    have hfin : a / 2 ≤ |B t ω| := by
      have hmem2 : s ∈ Set.Icc (0:ℝ≥0) T := ⟨by simp, hs⟩
      have hmem3 : t ∈ Set.Icc (0:ℝ≥0) T := ⟨by simp, htT⟩
      have hd : dist s t ≤ δ := by
        have h4 : dist s t = |(s : ℝ) - (t : ℝ)| := by
          simp [NNReal.dist_eq]
        rw [h4, htc]
        exact le_of_lt hltδ
      have huu2 := huu s hmem2 t hmem3 hd
      -- a ≤ |B s| ≤ |B s - B t| + |B t| ≤ a/2 + |B t|
      have htri : |B s ω| ≤ |B s ω - B t ω| + |B t ω| := by
        have := abs_add_le (B s ω - B t ω) (B t ω)
        rwa [sub_add_cancel] at this
      rw [Real.dist_eq] at huu2
      linarith
    exact ⟨n, k, hkT, hfin⟩
  · refine ⟨0, 0, by simp, ?_⟩
    have : a ≤ 0 := le_of_not_gt ha0
    have h1 : a / 2 ≤ 0 := by linarith
    exact le_trans h1 (abs_nonneg _)

end LatticeProb

end
