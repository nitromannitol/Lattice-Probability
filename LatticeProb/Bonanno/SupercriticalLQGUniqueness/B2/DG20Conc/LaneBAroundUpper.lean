/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundUpper at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterSeparator
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.LFPP.Length

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

private theorem laneB_le_mul_of_forall_pos_add {A b : ℝ≥0∞} (n : ℕ)
    (hn : 0 < n)
    (h : ∀ δ : ℝ≥0∞, 0 < δ → A ≤ (n : ℝ≥0∞) * (b + δ)) :
    A ≤ (n : ℝ≥0∞) * b := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnfin : (n : ℝ≥0∞) ≠ ∞ := by finiteness
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have hδ : 0 < (ε : ℝ≥0∞) / n := ENNReal.div_pos hε0 hnfin
  calc
    A ≤ (n : ℝ≥0∞) * (b + (ε : ℝ≥0∞) / n) := h _ hδ
    _ = (n : ℝ≥0∞) * b + ε := by
      rw [mul_add, ENNReal.mul_div_cancel hn0 hnfin]

 


theorem laneB_large_aroundDist_le_cost {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {R bnd : ℝ} (hR : 24 ≤ R)
    (hfamily : ∀ j ∈ laneBLongRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 3 1 ≤ bnd) :
    (lfppContMetric ξ f hf).aroundDist
      {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
      (sphere 0 R) (sphere 0 (2 * R)) ≤
      (((4 * (2 * laneBGridRadius R + 1)).toNat + 1 : ℕ) : ℝ≥0∞) *
        (3 * (3 * (4 * ENNReal.ofReal bnd))) := by
  let n : ℕ := (4 * (2 * laneBGridRadius R + 1)).toNat + 1
  have hn : 0 < n := by dsimp [n]; omega
  have happrox (δ : ℝ≥0∞) (hδ : 0 < δ) :
      (lfppContMetric ξ f hf).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere 0 R) (sphere 0 (2 * R)) ≤
        (n : ℝ≥0∞) * (3 * (3 * (4 * (ENNReal.ofReal bnd + δ)))) := by
    obtain ⟨V, a, d, hp, hm, hsep, hlen⟩ :=
      laneB_perimeter_separating_walk hf hR hfamily hδ
    have hsub : V '' Icc (0 : ℝ) 1 ⊆
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} := by
      rintro z ⟨t, ht, rfl⟩
      exact hm ht
    calc
      (lfppContMetric ξ f hf).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere 0 R) (sphere 0 (2 * R))
        ≤ (lfppContMetric ξ f hf).len V 0 1 := by
          unfold ContMetric.aroundDist
          exact iInf_le_of_le (0 : ℝ) (iInf_le_of_le (1 : ℝ)
            (iInf_le_of_le V (iInf_le_of_le zero_le_one
              (iInf_le_of_le hp.continuousOn
                (iInf_le_of_le hsub (iInf_le_of_le hsep le_rfl))))))
      _ ≤ lfppLen ξ f V := by
        simpa only [lfppLen_eq] using len_le_lfppLen hf hp le_rfl le_rfl
      _ ≤ _ := by simpa only [n] using hlen
  have hmul : ∀ δ : ℝ≥0∞, 0 < δ →
      (lfppContMetric ξ f hf).aroundDist
          {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
          (sphere 0 R) (sphere 0 (2 * R)) ≤
        ((36 * n : ℕ) : ℝ≥0∞) * (ENNReal.ofReal bnd + δ) := by
    intro δ hδ
    calc
      _ ≤ (n : ℝ≥0∞) * (3 * (3 * (4 * (ENNReal.ofReal bnd + δ)))) := happrox δ hδ
      _ = ((36 * n : ℕ) : ℝ≥0∞) * (ENNReal.ofReal bnd + δ) := by
        push_cast
        ring
  have h := laneB_le_mul_of_forall_pos_add (36 * n) (by positivity) hmul
  convert h using 1 <;> simp only [n] <;> push_cast <;> ring

end SupercriticalLQGUniqueness.B2.DG20Conc
