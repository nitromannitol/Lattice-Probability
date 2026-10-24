import LatticeProb.Prob.Cadlag.HalfLine.Defs

/-!
# Logarithmic distortion of half-line time changes

Secant estimates for the Ethier–Kurtz time changes, their inverses and compositions.
-/

namespace LatticeProb.Cadlag.HalfLine

open scoped ENNReal NNReal

noncomputable section

/-- Every increasing onto half-line time change fixes zero. -/
theorem LambdaPrime.map_zero (l : LambdaPrime) : l 0 = 0 := l.map_bot

/-- An order isomorphism of the half-line is continuous. -/
theorem LambdaPrime.continuous (l : LambdaPrime) : Continuous l :=
  OrderIso.continuous l

/-- Half-line time changes are strictly increasing. -/
theorem LambdaPrime.strictMono (l : LambdaPrime) : StrictMono l :=
  OrderIso.strictMono l

/-- Each logarithmic secant is bounded by the defining supremum. -/
theorem log_secant_le_gamma (l : LambdaPrime) {s t : Time} (h : t < s) :
    ENNReal.ofReal |Real.log (((l s : ℝ) - l t) / ((s : ℝ) - t))| ≤ gamma l :=
  le_iSup_of_le s (le_iSup_of_le t (le_iSup_of_le h le_rfl))

/-- Finite logarithmic distortion gives two-sided exponential secant bounds. -/
theorem secant_bounds (l : LambdaPrime) (h : gamma l ≠ ∞) {t s : Time}
    (hts : t < s) :
    Real.exp (-(gamma l).toReal) ≤ ((l s : ℝ) - l t) / ((s : ℝ) - t) ∧
      ((l s : ℝ) - l t) / ((s : ℝ) - t) ≤ Real.exp (gamma l).toReal := by
  have hp : 0 < ((l s : ℝ) - l t) / ((s : ℝ) - t) :=
    div_pos (sub_pos.mpr (l.strictMono hts)) (sub_pos.mpr hts)
  have hb := (ENNReal.ofReal_le_iff_le_toReal h).mp (log_secant_le_gamma l hts)
  exact ⟨(Real.le_log_iff_exp_le hp).mp (abs_le.mp hb).1,
    (Real.log_le_iff_le_exp hp).mp (abs_le.mp hb).2⟩

/-- Uniform exponential secant bounds control logarithmic distortion. -/
theorem gamma_le_of_secant (l : LambdaPrime) {g : ℝ} (hg : 0 ≤ g)
    (h : ∀ t s : Time, t < s →
      Real.exp (-g) ≤ ((l s : ℝ) - l t) / ((s : ℝ) - t) ∧
        ((l s : ℝ) - l t) / ((s : ℝ) - t) ≤ Real.exp g) :
    gamma l ≤ ENNReal.ofReal g := by
  refine iSup_le fun s => iSup_le fun t => iSup_le fun hts => ?_
  have hp : 0 < ((l s : ℝ) - l t) / ((s : ℝ) - t) :=
    div_pos (sub_pos.mpr (l.strictMono hts)) (sub_pos.mpr hts)
  apply (ENNReal.ofReal_le_ofReal_iff hg).mpr
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hp).mpr (h t s hts).1,
    (Real.log_le_iff_le_exp hp).mpr (h t s hts).2⟩

/-- Inverting a time change preserves logarithmic distortion. -/
theorem gamma_symm (l : LambdaPrime) : gamma l.symm = gamma l := by
  have bound (k : LambdaPrime) : gamma k.symm ≤ gamma k := by
    refine iSup_le fun s => iSup_le fun t => iSup_le fun hts => ?_
    have hb := log_secant_le_gamma k (k.symm.strictMono hts)
    simp only [OrderIso.apply_symm_apply] at hb
    have he : ((k.symm s : ℝ) - k.symm t) / ((s : ℝ) - t) =
        (((s : ℝ) - t) / ((k.symm s : ℝ) - k.symm t))⁻¹ := by
      rw [inv_div]
    rw [he, Real.log_inv, abs_neg]
    exact hb
  exact le_antisymm (bound l) (by simpa only [OrderIso.symm_symm] using bound l.symm)

/-- Composition adds at most the two logarithmic distortions. -/
theorem gamma_trans_le (l₁ l₂ : LambdaPrime) :
    gamma (l₁.trans l₂) ≤ gamma l₁ + gamma l₂ := by
  refine iSup_le fun s => iSup_le fun t => iSup_le fun hts => ?_
  have hp : 0 < (l₁ s : ℝ) - l₁ t := sub_pos.mpr (l₁.strictMono hts)
  have hq : 0 < (s : ℝ) - t := sub_pos.mpr hts
  have hr : 0 < (l₂ (l₁ s) : ℝ) - l₂ (l₁ t) :=
    sub_pos.mpr (l₂.strictMono (l₁.strictMono hts))
  have he : ((l₂ (l₁ s) : ℝ) - l₂ (l₁ t)) / ((s : ℝ) - t) =
      (((l₁ s : ℝ) - l₁ t) / ((s : ℝ) - t)) *
        (((l₂ (l₁ s) : ℝ) - l₂ (l₁ t)) / ((l₁ s : ℝ) - l₁ t)) := by
    exact (div_mul_div_cancel₀' hp.ne' _ _).symm
  change ENNReal.ofReal |Real.log
    (((l₂ (l₁ s) : ℝ) - l₂ (l₁ t)) / ((s : ℝ) - t))| ≤ _
  rw [he, Real.log_mul (ne_of_gt (div_pos hp hq)) (ne_of_gt (div_pos hr hp))]
  exact (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans
    (ENNReal.ofReal_add_le.trans
      (add_le_add (log_secant_le_gamma l₁ hts)
        (log_secant_le_gamma l₂ (l₁.strictMono hts))))

/-- A finite distortion time change has the expected exponential Lipschitz constant. -/
theorem lipschitzWith_of_gamma (l : LambdaPrime) (h : gamma l ≠ ∞) :
    LipschitzWith ⟨Real.exp (gamma l).toReal, (Real.exp_pos _).le⟩ l := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |(l s : ℝ) - l t| ≤ Real.exp (gamma l).toReal * |(s : ℝ) - t|
  wlog hst : t ≤ s generalizing s t
  · simpa only [abs_sub_comm] using this t s (le_of_not_ge hst)
  rcases hst.eq_or_lt with he | hts
  · subst s
    simp only [sub_self, abs_zero, mul_zero, le_refl]
  have hb := (secant_bounds l h hts).2
  have hd : 0 < (s : ℝ) - t := sub_pos.mpr hts
  have hm := (div_le_iff₀ hd).mp hb
  have hsReal : (t : ℝ) ≤ s := hst
  have hlReal : (l t : ℝ) ≤ l s := l.monotone hst
  simpa only [abs_of_nonneg (sub_nonneg.mpr hsReal),
    abs_of_nonneg (sub_nonneg.mpr hlReal)] using hm

/-- Admissible time changes are closed under inversion. -/
def Lambda.symm (l : Lambda) : Lambda :=
  ⟨l.1.symm, ⟨⟨_, lipschitzWith_of_gamma _ (by
    rw [gamma_symm]; exact ne_of_lt l.2.2)⟩, by rw [gamma_symm]; exact l.2.2⟩⟩

/-- The admissible inverse has the same logarithmic distortion. -/
theorem Lambda.gamma_symm (l : Lambda) : gamma l.symm.1 = gamma l.1 :=
  HalfLine.gamma_symm l.1

/-- Admissible time changes are closed under composition. -/
def Lambda.trans (l₁ l₂ : Lambda) : Lambda :=
  ⟨l₁.1.trans l₂.1, ⟨⟨_, lipschitzWith_of_gamma _
    (ne_of_lt ((gamma_trans_le _ _).trans_lt (ENNReal.add_lt_top.mpr
      ⟨l₁.2.2, l₂.2.2⟩)))⟩,
    (gamma_trans_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨l₁.2.2, l₂.2.2⟩)⟩⟩

/-- The admissible composition satisfies the distortion triangle inequality. -/
theorem Lambda.gamma_trans_le (l₁ l₂ : Lambda) :
    gamma (l₁.trans l₂).1 ≤ gamma l₁.1 + gamma l₂.1 :=
  HalfLine.gamma_trans_le _ _

/-- Finite distortion bounds the displacement from the identity at every time. -/
theorem abs_sub_le_of_gamma (l : LambdaPrime) (h : gamma l ≠ ∞) (t : Time) :
    |(l t : ℝ) - t| ≤ t * (Real.exp (gamma l).toReal - 1) := by
  by_cases ht : t = 0
  · subst t
    simp only [LambdaPrime.map_zero, NNReal.coe_zero, sub_self, abs_zero, zero_mul,
      le_refl]
  have htpos : (0 : Time) < t := lt_of_le_of_ne (zero_le : (0 : Time) ≤ t) (Ne.symm ht)
  have hb := secant_bounds l h htpos
  simp only [LambdaPrime.map_zero, NNReal.coe_zero, sub_zero] at hb
  have htReal : (0 : ℝ) < t := htpos
  have hlo := (le_div_iff₀ htReal).mp hb.1
  have hhi := (div_le_iff₀ htReal).mp hb.2
  have he : 1 - Real.exp (-(gamma l).toReal) ≤
      Real.exp (gamma l).toReal - 1 := by
    have ha := Real.add_one_le_exp (gamma l).toReal
    have hb := Real.add_one_le_exp (-(gamma l).toReal)
    linarith
  have algebra (a u lo hi : ℝ) (hu : 0 ≤ u) (hl : lo * u ≤ a)
      (hh : a ≤ hi * u) (hc : 1 - lo ≤ hi - 1) : |a - u| ≤ u * (hi - 1) := by
    apply abs_le.mpr
    constructor
    · have hm := mul_le_mul_of_nonneg_left hc hu
      nlinarith only [hl, hm]
    · nlinarith only [hh]
  exact algebra _ _ _ _ t.2 hlo hhi he

/-- Positive scalar multiplication gives a genuine onto half-line time change. -/
def dilation (c : ℝ≥0) (hc : 0 < c) : LambdaPrime := OrderIso.mulLeft₀ c hc

/-- The distortion of a positive dilation is exactly the absolute logarithm. -/
theorem gamma_dilation (c : ℝ≥0) (hc : 0 < c) :
    gamma (dilation c hc) = ENNReal.ofReal |Real.log (c : ℝ)| := by
  have hs (s t : Time) (hts : t < s) :
      (((dilation c hc) s : ℝ) - (dilation c hc) t) / ((s : ℝ) - t) = c := by
    change ((c : ℝ) * s - (c : ℝ) * t) / ((s : ℝ) - t) = c
    have hne : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt hts)
    rw [← mul_sub, mul_div_cancel_right₀ _ hne]
  apply le_antisymm
  · exact iSup_le fun s => iSup_le fun t => iSup_le fun hts => by rw [hs s t hts]
  · have hb := log_secant_le_gamma (dilation c hc) (show (0 : Time) < 1 by norm_num)
    rw [hs 1 0 (by norm_num)] at hb
    exact hb

end

end LatticeProb.Cadlag.HalfLine
