import Mathlib
import LatticeProb.LQG.LQGMeasureFullSupport2
import LatticeProb.LQG.LQGMeasureFullSupport
import LatticeProb.LQG.LQGMeasureInputs
import LatticeProb.LQG.LQGMeasureNonatomic
import LatticeProb.LQG.LQGMeasureNonatomicMassScaled
import LatticeProb.LQG.LQGMeasureNonatomicMassWeight

/-!
# The ball clause of Lemma 2.4 from the multiscale bound, part A

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4: the per-sample reduction of the ball-mass bounds, `ballMass_upper_of_scaled` (the upper bound of the
ball-volume estimate) and `ballMass_lower_of_scaled` (the lower bound), from the scaled multiscale bound `ScaledBallBound`
at the scales `ε` and `ε/4` and the power weight `μ_h = |x|^e μ₀` off `0` (Berestycki and Gwynne 2020, Lemma A.1).
The weight relation is taken as the hypothesis `hW`.
-/

namespace LatticeProb.LQG

open MeasureTheory Metric Filter Set Topology
open scoped ENNReal

universe u

/-- The per-sample content of the event of `WholePlaneScaledBallMassStep` at scale `δ`, for a measure `m₀` and
`G = γQ`: for `t ∈ [δ^{1-ζ}, 1]` and `z ∈ closedBall 0 (R₁ t)`,
`t^G (δ/t)^{β⁻} δ^ζ ≤ m₀(B_δ(z)) ≤ t^G (δ/t)^{β⁺} δ^{-ζ}`. -/
def ScaledBallBound (m₀ : Measure ℂ) (G R₁ βp βm ζ δ : ℝ) : Prop :=
  ∀ t : ℝ, δ ^ (1 - ζ) ≤ t → t ≤ 1 → ∀ z ∈ closedBall (0 : ℂ) (R₁ * t),
    ENNReal.ofReal (t ^ G * (δ / t) ^ βm * δ ^ ζ) ≤ m₀ (ball z δ) ∧
      m₀ (ball z δ) ≤ ENNReal.ofReal (t ^ G * (δ / t) ^ βp * δ ^ (-ζ))

/-- `s^e (s^G (ε/s)^b ε^c) = s^{e+G-b} ε^{b+c}`. -/
theorem rpow_mul_div_rpow_eq {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (e G b c : ℝ) :
    s ^ e * (s ^ G * (ε / s) ^ b * ε ^ c) = s ^ (e + G - b) * ε ^ (b + c) := by
  rw [Real.rpow_sub hs, Real.rpow_add hs, Real.rpow_add hε, Real.div_rpow hε.le hs.le]
  ring

/-- At `t = δ^{1-ζ}`: `t^G (δ/t)^b δ^c = δ^{(1-ζ)G + ζb + c}`. -/
theorem scaled_rpow_eq {δ : ℝ} (hδ : 0 < δ) (ζ G b c : ℝ) :
    (δ ^ (1 - ζ)) ^ G * (δ / δ ^ (1 - ζ)) ^ b * δ ^ c = δ ^ ((1 - ζ) * G + ζ * b + c) := by
  have h1 : δ / δ ^ (1 - ζ) = δ ^ ζ := by
    rw [div_eq_iff (Real.rpow_pos_of_pos hδ _).ne', ← Real.rpow_add hδ]
    have : ζ + (1 - ζ) = 1 := by ring
    rw [this, Real.rpow_one]
  rw [h1, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]

/-- A point at distance at most `ε/2` from `z` with norm at least `ε/2` and at most `|z| + ε/2`. -/
theorem exists_away_from_zero (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, dist w z ≤ ε / 2 ∧ ε / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ ‖z‖ + ε / 2 := by
  by_cases hz : z = 0
  · refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_, ?_⟩ <;>
      simp [hz, dist_eq_norm, Complex.norm_real, abs_of_pos hε]
  · have hs : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hc : 0 ≤ ε / (2 * ‖z‖) := by positivity
    refine ⟨(1 + ε / (2 * ‖z‖)) • z, ?_, ?_, ?_⟩
    · rw [dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc]
      field_simp
      rfl
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (1 + ε / (2 * ‖z‖)) * ‖z‖ = ‖z‖ + ε / 2 := by field_simp
      rw [this]; linarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (1 + ε / (2 * ‖z‖)) * ‖z‖ = ‖z‖ + ε / 2 := by field_simp
      rw [this]

variable {m m₀ : Measure ℂ} {e G βp₀ βm₀ ζ R R₁ ε : ℝ}

/-- Upper bound in the ball-volume estimate of Lemma 2.4, for one sample: `μ_h(B_ε(z)) ≤ max(C₁ ε^{β⁺₀-ζ}, C₂ ε^{(1-ζ)(G₁+e)})`. -/
theorem ballMass_upper_of_scaled
    (hW : m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (h0 : m {0} = 0) (hε : 0 < ε) (hε1 : ε < 1) (hζ1 : ζ < 1) (hR₁ : R ≤ R₁) (h1R₁ : 1 ≤ R₁)
    (hT : βp₀ ≤ G + e) (hT₁ : 0 < (1 - ζ) * G + ζ * βp₀ - ζ + e)
    (h2ε : 2 * ε ≤ ε ^ (1 - ζ)) (h2ε' : 2 * ε ^ (1 - ζ) ≤ 1)
    (hF : ScaledBallBound m₀ G R₁ βp₀ βm₀ ζ ε)
    (hFj : ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ 4 * ε ^ (1 - ζ) → ScaledBallBound m₀ G R₁ βp₀ βm₀ ζ ((2 : ℝ)⁻¹ ^ j))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    m (ball z ε) ≤ ENNReal.ofReal (max (2 ^ |e| * max 1 R ^ |e| * ε ^ (βp₀ - ζ))
      (2 ^ |e| * 4 ^ ((1 - ζ) * G + ζ * βp₀ - ζ + e) /
          (1 - (2 : ℝ)⁻¹ ^ ((1 - ζ) * G + ζ * βp₀ - ζ + e)) *
        ε ^ ((1 - ζ) * ((1 - ζ) * G + ζ * βp₀ - ζ + e)))) := by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.1 hz
  have hmeas : MeasurableSet (ball z ε) := measurableSet_ball
  have hερ : 0 < ε ^ (1 - ζ) := Real.rpow_pos_of_pos hε _
  rcases le_or_gt (ε ^ (1 - ζ)) ‖z‖ with hs | hs
  · -- `|z| ≥ ε^{1-ζ}`: comparison of the weight with `|z|^e`
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    set s := ‖z‖ with hs_def
    have hs0 : 0 < s := hερ.trans_le hs
    have hweight : ∀ x ∈ ball z ε, x ≠ 0 → ‖x‖ ^ e ≤ 2 ^ |e| * s ^ e := by
      intro x hx _
      rw [mem_ball, dist_eq_norm] at hx
      have h1 := norm_sub_norm_le x z
      have h2 := norm_sub_norm_le z x
      rw [norm_sub_rev] at h2
      exact rpow_le_two_rpow_abs_mul hs0 (by linarith) (by linarith)
    set t := min s 1 with ht_def
    have ht1 : t ≤ 1 := min_le_right _ _
    have hεt : ε ^ (1 - ζ) ≤ t := le_min hs (Real.rpow_le_one hε.le hε1.le (by linarith))
    have hzt : z ∈ closedBall (0 : ℂ) (R₁ * t) := by
      rw [mem_closedBall_zero_iff, ← hs_def]
      rcases le_total s 1 with h | h
      · rw [ht_def, min_eq_left h]; nlinarith
      · rw [ht_def, min_eq_right h, mul_one]; linarith
    have hm₀ := (hF t hεt ht1 z hzt).2
    calc m (ball z ε) ≤ ENNReal.ofReal (2 ^ |e| * s ^ e) * m₀ (ball z ε) :=
          measure_le_of_rpow_norm_le hW h0 hmeas hweight
      _ ≤ ENNReal.ofReal (2 ^ |e| * s ^ e) * ENNReal.ofReal (t ^ G * (ε / t) ^ βp₀ * ε ^ (-ζ)) :=
          mul_le_mul_right hm₀ _
      _ = ENNReal.ofReal (2 ^ |e| * s ^ e * (t ^ G * (ε / t) ^ βp₀ * ε ^ (-ζ))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc (2 ^ |e|) (s ^ e), mul_assoc (2 ^ |e|) (max 1 R ^ |e|)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total s 1 with h | h
          · rw [ht_def, min_eq_left h, rpow_mul_div_rpow_eq hs0 hε, ← sub_eq_add_neg]
            calc s ^ (e + G - βp₀) * ε ^ (βp₀ - ζ) ≤ 1 * ε ^ (βp₀ - ζ) := by
                  gcongr; exact Real.rpow_le_one hs0.le h (by linarith)
              _ ≤ max 1 R ^ |e| * ε ^ (βp₀ - ζ) := by
                  gcongr; exact Real.one_le_rpow (le_max_left _ _) (abs_nonneg _)
          · rw [ht_def, min_eq_right h, Real.one_rpow, div_one, one_mul, ← Real.rpow_add hε,
              ← sub_eq_add_neg]
            gcongr
            calc s ^ e ≤ s ^ |e| := Real.rpow_le_rpow_of_exponent_le h (le_abs_self e)
              _ ≤ max 1 R ^ |e| :=
                  Real.rpow_le_rpow hs0.le (hzR.le.trans (le_max_right _ _)) (abs_nonneg _)
  · -- `|z| < ε^{1-ζ}`: the shells around the origin
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    set G₁ := (1 - ζ) * G + ζ * βp₀ - ζ with hG₁
    have hρ0 : 0 < 2 * ε ^ (1 - ζ) := by positivity
    obtain ⟨j₀, hj₀1, hj₀2⟩ :=
      exists_nat_pow_near_of_lt_one hρ0 h2ε' (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
    have hj₀4 : (2 : ℝ)⁻¹ ^ j₀ ≤ 4 * ε ^ (1 - ζ) := by
      have : (2 : ℝ)⁻¹ ^ j₀ = 2 * (2 : ℝ)⁻¹ ^ (j₀ + 1) := by rw [pow_succ]; ring
      rw [this]; linarith
    have hεle : ε ≤ ε ^ (1 - ζ) := by linarith
    have hsub : ball z ε ⊆ ball (0 : ℂ) ((2 : ℝ)⁻¹ ^ j₀) := by
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have h1 := norm_sub_norm_le x z
      linarith
    have hball : ∀ j : ℕ, j₀ ≤ j →
        m₀ (ball 0 ((2 : ℝ)⁻¹ ^ j)) ≤ ENNReal.ofReal (1 * ((2 : ℝ)⁻¹ ^ j) ^ G₁) := by
      intro j hj
      have hδ0 : 0 < (2 : ℝ)⁻¹ ^ j := by positivity
      have hδ1 : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hδj : (2 : ℝ)⁻¹ ^ j ≤ 4 * ε ^ (1 - ζ) :=
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj₀4
      have h := (hFj j hδj (((2 : ℝ)⁻¹ ^ j) ^ (1 - ζ)) le_rfl
        (Real.rpow_le_one hδ0.le hδ1 (by linarith)) 0
        (by rw [mem_closedBall_zero_iff, norm_zero]; positivity)).2
      rw [scaled_rpow_eq hδ0] at h
      rw [one_mul, hG₁]
      convert h using 3
    calc m (ball z ε) ≤ m (ball 0 ((2 : ℝ)⁻¹ ^ j₀)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 ^ |e| * 1 * ((2 : ℝ)⁻¹ ^ (G₁ + e)) ^ j₀ / (1 - (2 : ℝ)⁻¹ ^ (G₁ + e))) :=
          measure_ball_zero_le_of_dyadic hW h0 zero_le_one hT₁ hball
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hq1 : (2 : ℝ)⁻¹ ^ (G₁ + e) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hT₁
          have hpow : ((2 : ℝ)⁻¹ ^ (G₁ + e)) ^ j₀ ≤ 4 ^ (G₁ + e) * ε ^ ((1 - ζ) * (G₁ + e)) := by
            rw [Real.rpow_pow_comm (by norm_num), Real.rpow_mul hε.le,
              ← Real.mul_rpow (by norm_num) hερ.le]
            exact Real.rpow_le_rpow (by positivity) hj₀4 hT₁.le
          have hinv : 0 ≤ (1 - (2 : ℝ)⁻¹ ^ (G₁ + e))⁻¹ := inv_nonneg.2 (by linarith)
          rw [mul_one, div_eq_mul_inv, div_eq_mul_inv]
          calc 2 ^ |e| * ((2 : ℝ)⁻¹ ^ (G₁ + e)) ^ j₀ * (1 - (2 : ℝ)⁻¹ ^ (G₁ + e))⁻¹
              ≤ 2 ^ |e| * (4 ^ (G₁ + e) * ε ^ ((1 - ζ) * (G₁ + e))) * (1 - (2 : ℝ)⁻¹ ^ (G₁ + e))⁻¹ := by
                gcongr
            _ = _ := by ring

/-- Lower bound in the ball-volume estimate of Lemma 2.4, for one sample:
`μ_h(B_ε(z)) ≥ min(c₁ ε^{β⁻₀+ζ}, (ε/4)^{max(e,0) + (1-ζ)G + ζβ⁻₀ + ζ})`. -/
theorem ballMass_lower_of_scaled
    (hW : m.restrict {0}ᶜ = (m₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hε : 0 < ε) (hε1 : ε < 1) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (hR₁ : R ≤ R₁) (h8R₁ : 8 ≤ R₁)
    (hT : G + e ≤ βm₀) (h2ε : 2 * ε ≤ ε ^ (1 - ζ)) (h2ε' : 2 * ε ^ (1 - ζ) ≤ 1)
    (hF : ScaledBallBound m₀ G R₁ βp₀ βm₀ ζ ε) (hF4 : ScaledBallBound m₀ G R₁ βp₀ βm₀ ζ (ε / 4))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ENNReal.ofReal (min ((2 ^ |e|)⁻¹ * (max 1 R ^ |e|)⁻¹ * ε ^ (βm₀ + ζ))
      ((ε / 4) ^ (max e 0 + ((1 - ζ) * G + ζ * βm₀ + ζ)))) ≤ m (ball z ε) := by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.1 hz
  have hερ : 0 < ε ^ (1 - ζ) := Real.rpow_pos_of_pos hε _
  rcases le_or_gt (ε ^ (1 - ζ)) ‖z‖ with hs | hs
  · -- `|z| ≥ ε^{1-ζ}`
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    set s := ‖z‖ with hs_def
    have hs0 : 0 < s := hερ.trans_le hs
    have hweight : ∀ x ∈ ball z ε, (2 ^ |e|)⁻¹ * s ^ e ≤ ‖x‖ ^ e := by
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      have h1 := norm_sub_norm_le x z
      have h2 := norm_sub_norm_le z x
      rw [norm_sub_rev] at h2
      have hx0 : 0 < ‖x‖ := by linarith
      rw [inv_mul_le_iff₀ (by positivity)]
      exact rpow_le_two_rpow_abs_mul hx0 (by linarith) (by linarith)
    have h0A : (0 : ℂ) ∉ ball z ε := by
      rw [mem_ball, dist_comm, dist_zero_right, not_lt, ← hs_def]; linarith
    set t := min s 1 with ht_def
    have ht1 : t ≤ 1 := min_le_right _ _
    have hεt : ε ^ (1 - ζ) ≤ t := le_min hs (Real.rpow_le_one hε.le hε1.le (by linarith))
    have hzt : z ∈ closedBall (0 : ℂ) (R₁ * t) := by
      rw [mem_closedBall_zero_iff, ← hs_def]
      rcases le_total s 1 with h | h
      · rw [ht_def, min_eq_left h]; nlinarith
      · rw [ht_def, min_eq_right h, mul_one]; linarith
    have hm₀ := (hF t hεt ht1 z hzt).1
    calc ENNReal.ofReal ((2 ^ |e|)⁻¹ * (max 1 R ^ |e|)⁻¹ * ε ^ (βm₀ + ζ))
        ≤ ENNReal.ofReal ((2 ^ |e|)⁻¹ * s ^ e * (t ^ G * (ε / t) ^ βm₀ * ε ^ ζ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc ((2 : ℝ) ^ |e|)⁻¹ (max 1 R ^ |e|)⁻¹, mul_assoc ((2 : ℝ) ^ |e|)⁻¹ (s ^ e)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rcases le_total s 1 with h | h
          · rw [ht_def, min_eq_left h, rpow_mul_div_rpow_eq hs0 hε]
            calc (max 1 R ^ |e|)⁻¹ * ε ^ (βm₀ + ζ) ≤ 1 * ε ^ (βm₀ + ζ) := by
                  gcongr
                  exact inv_le_one_of_one_le₀ (Real.one_le_rpow (le_max_left _ _) (abs_nonneg _))
              _ ≤ s ^ (e + G - βm₀) * ε ^ (βm₀ + ζ) := by
                  gcongr; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 h (by linarith)
          · rw [ht_def, min_eq_right h, Real.one_rpow, div_one, one_mul, ← Real.rpow_add hε]
            gcongr
            calc (max 1 R ^ |e|)⁻¹ = max 1 R ^ (-|e|) :=
                  (Real.rpow_neg (by positivity) _).symm
              _ ≤ s ^ (-|e|) := Real.rpow_le_rpow_of_nonpos hs0 (hzR.le.trans (le_max_right _ _))
                  (neg_nonpos.2 (abs_nonneg e))
              _ ≤ s ^ e := Real.rpow_le_rpow_of_exponent_le h (neg_abs_le e)
      _ = ENNReal.ofReal ((2 ^ |e|)⁻¹ * s ^ e) * ENNReal.ofReal (t ^ G * (ε / t) ^ βm₀ * ε ^ ζ) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal ((2 ^ |e|)⁻¹ * s ^ e) * m₀ (ball z ε) := mul_le_mul_right hm₀ _
      _ ≤ m (ball z ε) := le_measure_of_le_rpow_norm hW measurableSet_ball h0A hweight
  · -- `|z| < ε^{1-ζ}`: a ball of radius `ε/4` away from the origin
    refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    obtain ⟨w, hwz, hw1, hw2⟩ := exists_away_from_zero z hε
    have hδ0 : 0 < ε / 4 := by positivity
    have hδ1 : ε / 4 ≤ 1 := by linarith
    have hsub : ball w (ε / 4) ⊆ ball z ε := by
      intro x hx; rw [mem_ball] at hx ⊢; linarith [dist_triangle x w z]
    have h0A : (0 : ℂ) ∉ ball w (ε / 4) := by
      rw [mem_ball, dist_comm, dist_zero_right, not_lt]; linarith
    have hweight : ∀ x ∈ ball w (ε / 4), (ε / 4) ^ max e 0 ≤ ‖x‖ ^ e := by
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      have h1 := norm_sub_norm_le x w
      have h2 := norm_sub_norm_le w x
      rw [norm_sub_rev] at h2
      have hxl : ε / 4 ≤ ‖x‖ := by linarith
      have hxu : ‖x‖ ≤ 1 := by linarith
      rcases le_total 0 e with he | he
      · rw [max_eq_left he]; exact Real.rpow_le_rpow hδ0.le hxl he
      · rw [max_eq_right he, Real.rpow_zero]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) hxu he
    have hδρ : ε ^ (1 - ζ) ≤ 4 * (ε / 4) ^ (1 - ζ) := by
      have h4 : ε ^ (1 - ζ) = 4 ^ (1 - ζ) * (ε / 4) ^ (1 - ζ) := by
        rw [← Real.mul_rpow (by norm_num) hδ0.le]; congr 1; ring
      rw [h4]
      gcongr
      calc (4 : ℝ) ^ (1 - ζ) ≤ 4 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := Real.rpow_one 4
    have hwt : w ∈ closedBall (0 : ℂ) (R₁ * (ε / 4) ^ (1 - ζ)) := by
      rw [mem_closedBall_zero_iff]
      have : 0 ≤ (ε / 4) ^ (1 - ζ) := (Real.rpow_pos_of_pos hδ0 _).le
      nlinarith
    have hm₀ := (hF4 ((ε / 4) ^ (1 - ζ)) le_rfl (Real.rpow_le_one hδ0.le hδ1 (by linarith)) w hwt).1
    rw [scaled_rpow_eq hδ0] at hm₀
    calc ENNReal.ofReal ((ε / 4) ^ (max e 0 + ((1 - ζ) * G + ζ * βm₀ + ζ)))
        = ENNReal.ofReal ((ε / 4) ^ max e 0) *
            ENNReal.ofReal ((ε / 4) ^ ((1 - ζ) * G + ζ * βm₀ + ζ)) := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add hδ0]
      _ ≤ ENNReal.ofReal ((ε / 4) ^ max e 0) * m₀ (ball w (ε / 4)) := mul_le_mul_right hm₀ _
      _ ≤ m (ball w (ε / 4)) := le_measure_of_le_rpow_norm hW measurableSet_ball h0A hweight
      _ ≤ m (ball z ε) := measure_mono hsub

/-! ### The reduction of Lemma 2.4 (ball clause), of volume growth and of full support, to the scaled step -/

section Scaled

open LatticeProb.Gauss LatticeProb.LQG.LQGMeasureNonatomicMass

/-- Reduction for Lemma 2.4: `LiouvilleBallMassBoundStepLP` (the ball-volume estimate on every `B_R`, with the exponent
ranges of its statement) from the multiscale ball
bound for `h^ℂ` (`WholePlaneScaledBallMassStepLP`, hypothesis `hS`), the singular weight `μ_h = |x|^{-γα₀} μ_{h^ℂ}` off `0`
(`singularWeightStep_lp`, proved), the existence of `μ_{h^ℂ}` on the same probability space (`hE`, at `α₀ = 0`) and
`μ_h({0}) = 0` (`hN`, `LQGMeasureNonatomicLP`). -/
theorem liouvilleBallMassBoundStep_of_scaled_lp
    (hS : WholePlaneScaledBallMassStepLP.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α₀ hC hcirc) :
    LiouvilleBallMassBoundStepLP.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ R hR βp βm hβp hβpT hβm
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE Ω P γ hC hcirc hGFF hγ hγ2 hQ
  have hTe : γ * (lqgQ γ - α₀) = γ * lqgQ γ + -(γ * α₀) := by ring
  rw [hTe] at hβpT hβm
  set G := γ * lqgQ γ with hG
  set e := -(γ * α₀) with he
  have hGeq : G = 2 + γ ^ 2 / 2 := by rw [hG]; unfold lqgQ; field_simp
  have hGAm : G < (2 + γ) ^ 2 / 2 := by rw [hGeq]; nlinarith
  have hm1 := min_le_left ((2 - γ) ^ 2 / 2) (G + e)
  have hm2 := min_le_right ((2 - γ) ^ 2 / 2) (G + e)
  have hM1 := le_max_left ((2 + γ) ^ 2 / 2) (G + e)
  have hM2 := le_max_right ((2 + γ) ^ 2 / 2) (G + e)
  set βp₀ := (βp + min ((2 - γ) ^ 2 / 2) (G + e)) / 2 with hβp₀
  set βm₀ := (max ((2 + γ) ^ 2 / 2) (G + e) + βm) / 2 with hβm₀
  have hp1 : βp < βp₀ := by rw [hβp₀]; linarith
  have hp2 : βp₀ < (2 - γ) ^ 2 / 2 := by rw [hβp₀]; linarith
  have hp3 : βp₀ < G + e := by rw [hβp₀]; linarith
  have hq1 : βm₀ < βm := by rw [hβm₀]; linarith
  have hq2 : (2 + γ) ^ 2 / 2 < βm₀ := by rw [hβm₀]; linarith
  have hq3 : G + e < βm₀ := by rw [hβm₀]; linarith
  have hGe : max e 0 + G < βm := by
    rcases le_total 0 e with h | h
    · rw [max_eq_left h]; linarith
    · rw [max_eq_right h]; linarith
  -- the parameter `ζ` of the multiscale bound
  have hev : ∀ᶠ ζ in 𝓝 (0 : ℝ), ζ < 1 ∧ ζ < βp₀ - βp ∧ 0 < (1 - ζ) * G + ζ * βp₀ - ζ + e ∧
      βp < (1 - ζ) * ((1 - ζ) * G + ζ * βp₀ - ζ + e) ∧ ζ < βm - βm₀ ∧
      max e 0 + ((1 - ζ) * G + ζ * βm₀ + ζ) < βm := by
    refine (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).and
      ((eventually_lt_nhds (by linarith : (0 : ℝ) < βp₀ - βp)).and
      ((ContinuousAt.eventually_lt (f := fun _ => (0 : ℝ))
          (g := fun ζ => (1 - ζ) * G + ζ * βp₀ - ζ + e) (by fun_prop) (by fun_prop)
          (by show (0 : ℝ) < (1 - 0) * G + 0 * βp₀ - 0 + e; linarith)).and
      ((ContinuousAt.eventually_lt (f := fun _ => βp)
          (g := fun ζ => (1 - ζ) * ((1 - ζ) * G + ζ * βp₀ - ζ + e)) (by fun_prop) (by fun_prop)
          (by show βp < (1 - 0) * ((1 - 0) * G + 0 * βp₀ - 0 + e); linarith)).and
      ((eventually_lt_nhds (by linarith : (0 : ℝ) < βm - βm₀)).and
      (ContinuousAt.eventually_lt (f := fun ζ => max e 0 + ((1 - ζ) * G + ζ * βm₀ + ζ))
          (g := fun _ => βm) (by fun_prop) (by fun_prop)
          (by show max e 0 + ((1 - 0) * G + 0 * βm₀ + 0) < βm; linarith))))))
  obtain ⟨ζ, ⟨hζ1, hz2, hz3, hz4, hz5, hz6⟩, hζ0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
  have hζ0' : 0 < ζ := hζ0
  -- the events
  set R₁ := R + 8 with hR₁
  set E : ℝ → Set Ω := fun δ => {ω | ScaledBallBound (μ₀ ω) G R₁ βp₀ βm₀ ζ δ} with hE_def
  have hstep : PolyHighProb P E :=
    hS γ hγ hγ2 Ω P hC hcirc μ₀ hGFF hμ₀ R₁ (by positivity) βp₀ βm₀ ζ (by linarith) hp2 hq2 hζ0' hζ1
  have h4 : PolyHighProb P fun r => E (r / 4) :=
    polyHighProb_mono (polyHighProb_comp_mul hstep (by norm_num : (0 : ℝ) < 1 / 4)) fun r ω h => by
      rwa [show (1 / 4 : ℝ) * r = r / 4 by ring] at h
  have htail := polyHighProb_dyadic_tail hstep (a := 1 - ζ) (c := 4) (by linarith) (by norm_num)
  set W : Set Ω := {ω | (μ ω).restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ ∧ μ ω {0} = 0} with hW_def
  have hW : ∀ᵐ ω ∂P, ω ∈ W := by
    filter_upwards [singularWeightStep_lp.{u} γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ μ₀ hGFF hμ hμ₀,
      hN Ω P γ α₀ hC hcirc hGFF hγ hγ2 hα₀ μ hμ] with ω h1 h2
    exact ⟨h1, h2 0⟩
  -- smallness of `ε`
  have hC₁ := eventually_mul_rpow_le (2 ^ |e| * max 1 R ^ |e|) (a := βp₀ - ζ) (b := βp) (by linarith)
  have hC₂ := eventually_mul_rpow_le (2 ^ |e| * 4 ^ ((1 - ζ) * G + ζ * βp₀ - ζ + e) /
      (1 - (2 : ℝ)⁻¹ ^ ((1 - ζ) * G + ζ * βp₀ - ζ + e))) hz4
  have hc₁ := eventually_rpow_le_mul (c := (2 ^ |e|)⁻¹ * (max 1 R ^ |e|)⁻¹) (by positivity)
    (a := βm₀ + ζ) (b := βm) (by linarith)
  have hc₂ := eventually_rpow_le_mul (c := ((4 : ℝ) ^ (max e 0 + ((1 - ζ) * G + ζ * βm₀ + ζ)))⁻¹)
    (by positivity) hz6
  have h2ε := eventually_mul_rpow_le 2 (a := 1) (b := 1 - ζ) (by linarith)
  have h2ε' := eventually_mul_rpow_le 2 (a := 1 - ζ) (b := 0) (by linarith)
  refine (polyHighProb_mono_of_eventually
    (polyHighProb_inter_ae (polyHighProb_inter (polyHighProb_inter hstep h4) htail) hW) ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ), hC₁, hC₂, hc₁, hc₂, h2ε, h2ε'] with
    ε hε hε₁ hε₂ hε₃ hε₄ hε₅ hε₆
  rintro ω ⟨⟨⟨hF, hF4⟩, hFj⟩, hWω, h0ω⟩ z hz
  rw [Real.rpow_one] at hε₅
  rw [Real.rpow_zero] at hε₆
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ballMass_lower_of_scaled hWω hε.1 hε.2 hζ0'.le hζ1
      (by linarith) (by linarith) hq3.le hε₅ hε₆ hF hF4 hz)
    refine le_min hε₃ ?_
    rw [Real.div_rpow hε.1.le (by norm_num), div_eq_inv_mul]
    exact hε₄
  · exact (ballMass_upper_of_scaled hWω h0ω hε.1 hε.2 hζ1 (by linarith) (by linarith) hp3.le hz3 hε₅ hε₆
      hF hFj hz).trans (ENNReal.ofReal_le_ofReal (max_le hε₁ hε₂))

/-- Volume growth at all small scales (`LQGVolumeGrowthAllScalesStmtLP`) from the scaled step `hS`, the existence `hE`
and the non-atomicity `hN`. -/
theorem lqgVolumeGrowthAllScalesStmt_of_scaled_lp
    (hS : WholePlaneScaledBallMassStepLP.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α₀ hC hcirc) :
    LQGVolumeGrowthAllScalesStmtLP.{u} :=
  lqgVolumeGrowthAllScalesStmt_of_ballMass_lp (liouvilleBallMassBoundStep_of_scaled_lp hS hE hN)

/-- Full support of the LQG measure (`LQGMeasureFullSupportStmtLP`) from the scaled step
`hS`, the existence `hE` and the non-atomicity `hN`. The singular-weight (Weyl scaling) input of the source route is
discharged by the proved `singularWeightStep_lp`, so it is not a hypothesis here. -/
theorem lqgMeasureFullSupportStmt_of_scaled_lp
    (hS : WholePlaneScaledBallMassStepLP.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistenceLP P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomicLP P γ α₀ hC hcirc) :
    LQGMeasureFullSupportStmtLP.{u} :=
  lqgMeasureFullSupportStmt_of_volumeGrowth_lp (lqgVolumeGrowthAllScalesStmt_of_scaled_lp hS hE hN)

end Scaled

end LatticeProb.LQG
