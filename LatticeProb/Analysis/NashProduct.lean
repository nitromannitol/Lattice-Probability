import LatticeProb.Analysis.NashProfile
import LatticeProb.Analysis.CriticalProfile

/-!
# Product condition for the Nash profile

The two-sided critical-profile comparison controls the logarithmic product series.
It transfers the critical product estimate to every positive scaling of the Nash profile.
-/

namespace LatticeProb

noncomputable section

/-- The logarithmic gap between the critical and Nash profiles is uniformly bounded. -/
lemma nashProfile_log_gap {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    0 ≤ Real.log (criticalProfile d t) - Real.log (nashProfile d t) ∧
      Real.log (criticalProfile d t) - Real.log (nashProfile d t) ≤
        (d : ℝ) * Real.log 2 := by
  obtain ⟨hlo, hhi⟩ := nashProfile_comparison hd ht
  have hp := criticalProfile_pos d ht
  have hn := nashProfile_pos hd ht
  change (2 : ℝ) ^ (-(d : ℝ)) * criticalProfile d t ≤ _ at hlo
  have hb := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hp) hlo
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
    hp.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hb
  exact ⟨sub_nonneg.mpr (Real.log_le_log hn hhi), by linarith⟩

/-- Every positive scaling of the Nash profile satisfies the explicit product bound. -/
theorem nashProfile_productBound {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {l : ℝ} (hl : 2 < l) :
    External.ckkwProductBound (fun t ↦ nashProfile d (α * t)) l 1
      (2 ^ d * (l ^ 3 / (l - 1)) ^ d) := by
  intro t ht
  let w := fun n : ℕ ↦ (2 : ℝ) ^ (-(n + 1 : ℤ))
  let x := fun n : ℕ ↦ (l - 1) * l ^ (-(n + 2 : ℤ)) * (α * t)
  have hx (n : ℕ) : 0 < x n :=
    mul_pos (criticalProfile_product_scale hl n).1 (mul_pos hα ht)
  let a := Real.log (criticalProfile d (α * t))
  let g := fun n ↦ w n * (Real.log (criticalProfile d (x n)) - a)
  let u := fun n ↦ w n *
    ((d : ℝ) * (((n : ℝ) + 2) * Real.log l - Real.log (l - 1)))
  obtain ⟨hw, hm⟩ := criticalProfile_product_weights
  have hu : HasSum u ((d : ℝ) * (3 * Real.log l - Real.log (l - 1))) := by
    convert! ((hm.mul_right (Real.log l)).sub
      (hw.mul_right (Real.log (l - 1)))).mul_right (d : ℝ) using 1
    · ext n; dsimp [u, w]; ring
    · ring
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
      (criticalProfile_product_log_bounds hd hl (mul_pos hα ht) n).1)
    (fun n ↦ mul_le_mul_of_nonneg_left
      (criticalProfile_product_log_bounds hd hl (mul_pos hα ht) n).2
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le) hu.summable
  let f := fun n ↦ w n * Real.log (criticalProfile d (x n))
  have hf : Summable f := by
    convert! hg.add (hw.summable.mul_right a) using 1
    ext n; dsimp [f, g]; ring
  let e := fun n ↦ w n *
    (Real.log (criticalProfile d (x n)) - Real.log (nashProfile d (x n)))
  have he : Summable e := Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
      (nashProfile_log_gap hd (hx n)).1)
    (fun n ↦ mul_le_mul_of_nonneg_left (nashProfile_log_gap hd (hx n)).2
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le)
    (hw.summable.mul_right ((d : ℝ) * Real.log 2))
  let q := fun n ↦ w n * Real.log (nashProfile d (x n))
  have hq : Summable q := by
    convert! hf.sub he using 1
    ext n; dsimp [q, f, e]; ring
  have hsum : (∑' n, q n) ≤ ∑' n, f n := hq.tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left
      (Real.log_le_log (nashProfile_pos hd (hx n))
        (nashProfile_comparison hd (hx n)).2)
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le) hf
  have hprod : HasProd (fun n ↦ (criticalProfile d (x n)) ^ w n)
      (Real.exp (∑' n, f n)) := by
    convert! hf.hasSum.rexp using 1
    ext n
    rw [Real.rpow_def_of_pos (criticalProfile_pos d (hx n))]
    dsimp [Function.comp_def, f]
    congr 1
    ring
  obtain ⟨P, hP, hbound⟩ := criticalProfile_productBound hd hl (α * t) (mul_pos hα ht)
  have hPeq : Real.exp (∑' n, f n) = P := hprod.unique hP
  refine ⟨Real.exp (∑' n, q n), ?_, ?_⟩
  · convert! hq.hasSum.rexp using 1
    ext n
    dsimp only [Function.comp_def]
    have htime : α * ((l - 1) * l ^ (-(n + 2 : ℤ)) * t) = x n := by
      dsimp [x]
      ring
    rw [htime]
    exact (Real.rpow_def_of_pos (nashProfile_pos hd (hx n)) (w n)).trans
      (congrArg Real.exp (mul_comm _ _))
  · rw [one_mul] at hbound ⊢
    have hcomp := (nashProfile_comparison hd (mul_pos hα ht)).1
    have htwo : (2 : ℝ) ^ (-(d : ℝ)) = ((2 : ℝ) ^ d)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    change (2 : ℝ) ^ (-(d : ℝ)) * criticalProfile d (α * t) ≤ _ at hcomp
    rw [htwo, ← div_eq_inv_mul] at hcomp
    have hc := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) d)).1 hcomp
    calc
      Real.exp (∑' n, q n) ≤ Real.exp (∑' n, f n) := Real.exp_le_exp.mpr hsum
      _ = P := hPeq
      _ ≤ (l ^ 3 / (l - 1)) ^ d * criticalProfile d (α * t) := hbound
      _ ≤ (l ^ 3 / (l - 1)) ^ d * (nashProfile d (α * t) * 2 ^ d) :=
        mul_le_mul_of_nonneg_left hc
          (pow_nonneg (div_pos (pow_pos (by linarith) _) (by linarith)).le _)
      _ = _ := by ring

/-- Explicit positive witnesses give the scaled Nash product-profile condition. -/
theorem nashProfile_productProfile {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    External.ckkwProductData (fun _ ↦ 1) (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d) ∧
      External.ckkwProductProfile (fun t ↦ nashProfile d (α * t)) (fun _ ↦ 1)
        (fun l ↦ 2 ^ d * (l ^ 3 / (l - 1)) ^ d) := by
  constructor
  · refine ⟨3, by norm_num, ?_⟩
    intro l hl
    exact ⟨zero_lt_one, mul_pos (pow_pos (by norm_num) _)
      (pow_pos (div_pos (pow_pos (by linarith) _) (by linarith)) _)⟩
  · intro l hl _ _
    exact nashProfile_productBound hd hα hl

end

end LatticeProb
