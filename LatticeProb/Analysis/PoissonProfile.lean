import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Poisson averaging of a logarithmic profile

The critical profile remains bounded by a constant multiple of itself under Poisson
averaging. The proof uses an exponential tilt to control the lower tail.
-/

namespace LatticeProb

open Filter

noncomputable section

/-- The positive base of the critical logarithmic profile. -/
private def profileBase (t : ℝ) : ℝ := 1 + t * Real.log (2 + t)

/-- The logarithmic profile base is at least one on the nonnegative half-line. -/
private lemma profileBase_one_le {t : ℝ} (ht : 0 ≤ t) : 1 ≤ profileBase t := by
  have hl : 0 ≤ Real.log (2 + t) := Real.log_nonneg (by linarith)
  exact le_add_of_nonneg_right (mul_nonneg ht hl)

/-- The logarithmic profile base increases on the nonnegative half-line. -/
private lemma profileBase_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    profileBase s ≤ profileBase t := by
  have hlog : Real.log (2 + s) ≤ Real.log (2 + t) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl : 0 ≤ Real.log (2 + s) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ t := hs.trans hst
  have hm := mul_le_mul hst hlog hl ht
  unfold profileBase
  linarith only [hm]

/-- The Poisson weights have total mass one for every nonnegative real parameter. -/
private lemma poisson_weights_hasSum {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun n : ℕ => Real.exp (-s) * s ^ n / n.factorial) 1 := by
  exact ProbabilityTheory.hasSum_one_poissonMeasure ⟨s, hs⟩

/-- The critical profile takes values between zero and one at nonnegative arguments. -/
private lemma profile_bounds (q : ℝ) (hq : 0 ≤ q) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (profileBase t) ^ (-q) ∧ (profileBase t) ^ (-q) ≤ 1 := by
  exact ⟨Real.rpow_nonneg (zero_le_one.trans (profileBase_one_le ht)) _,
    Real.rpow_le_one_of_one_le_of_nonpos (profileBase_one_le ht) (neg_nonpos.mpr hq)⟩

/-- The profile-weighted Poisson series is summable by domination by its probability weights. -/
theorem poisson_profile_summable (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Summable (fun n : ℕ => Real.exp (-s) * s ^ n / n.factorial *
      (1 + n * Real.log (2 + n)) ^ (-((d : ℝ) / 2))) := by
  apply (poisson_weights_hasSum hs).summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (by positivity)
      (profile_bounds ((d : ℝ) / 2) (by positivity) (Nat.cast_nonneg n)).1
  · intro n
    exact mul_le_of_le_one_right (by positivity)
      (profile_bounds ((d : ℝ) / 2) (by positivity) (Nat.cast_nonneg n)).2

/-- Exponential tilting computes the Poisson exponential moment without a tail indicator. -/
private lemma poisson_tilt_hasSum {s : ℝ} (hs : 0 ≤ s) :
    HasSum (fun n : ℕ => (Real.exp (-s) * s ^ n / n.factorial) *
      Real.exp (s / 4 - n)) (Real.exp (s / 4 + s * Real.exp (-1) - s)) := by
  have h := (poisson_weights_hasSum (mul_nonneg hs (Real.exp_pos (-1)).le)).mul_left
    (Real.exp (s / 4 + s * Real.exp (-1) - s))
  convert! h using 1
  · ext n
    rw [mul_pow, ← Real.exp_nat_mul]
    have he : Real.exp (-s) * Real.exp (s / 4 - n) =
        Real.exp (s / 4 + s * Real.exp (-1) - s) *
          Real.exp (-(s * Real.exp (-1))) * Real.exp ((n : ℝ) * (-1)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (-s) * Real.exp (s / 4 - n)) * (s ^ n / n.factorial) := by
        ring
      _ = _ := by rw [he]; ring
  · rw [mul_one]

/-- The reciprocal exponential at one is at most one half. -/
private lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h : 2 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [Real.exp_neg, ← one_div]
  exact (div_le_iff₀ (Real.exp_pos 1)).2 (by linarith)

/-- Splitting at one quarter of the mean bounds the average by a profile and a lower tail. -/
private lemma poisson_average_le_profile_add_exp (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (∑' n : ℕ, Real.exp (-s) * s ^ n / n.factorial *
      (profileBase n) ^ (-((d : ℝ) / 2))) ≤
      (profileBase (s / 4)) ^ (-((d : ℝ) / 2)) + Real.exp (-s / 4) := by
  let q : ℝ := (d : ℝ) / 2
  have hq : 0 ≤ q := by positivity
  have hpoint (n : ℕ) : (profileBase n) ^ (-q) ≤
      (profileBase (s / 4)) ^ (-q) + Real.exp (s / 4 - n) := by
    by_cases hn : s / 4 ≤ n
    · exact (Real.rpow_le_rpow_of_nonpos
        (lt_of_lt_of_le zero_lt_one (profileBase_one_le (by positivity)))
        (profileBase_mono (by positivity) hn) (neg_nonpos.mpr hq)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    · have he : 1 ≤ Real.exp (s / 4 - n) := Real.one_le_exp_iff.mpr (by linarith)
      exact (profile_bounds q hq (Nat.cast_nonneg n)).2.trans
        (he.trans (le_add_of_nonneg_left
          (profile_bounds q hq (by positivity : 0 ≤ s / 4)).1))
  have hsum := ((poisson_weights_hasSum hs).mul_right
    ((profileBase (s / 4)) ^ (-q))).add (poisson_tilt_hasSum hs)
  have hle := hasSum_le (fun n =>
    (mul_le_mul_of_nonneg_left (hpoint n) (by positivity)).trans_eq (mul_add _ _ _))
    (poisson_profile_summable d s hs).hasSum hsum
  have he : Real.exp (s / 4 + s * Real.exp (-1) - s) ≤ Real.exp (-s / 4) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left exp_neg_one_le_half hs
    linarith
  simp only [one_mul] at hle
  exact hle.trans (add_le_add le_rfl he)

/-- Rescaling the argument changes the logarithmic base by at most a fixed factor eventually. -/
private lemma profileBase_scale_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ t : ℝ in atTop, profileBase t ≤ (1 + 2 / a) * profileBase (a * t) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 / a ^ 2)] with t ht hta
  have ht0 : 0 ≤ t := by linarith
  have hat : 0 ≤ a * t := mul_nonneg ha.le ht0
  have hmul : 1 ≤ a ^ 2 * t := by
    have := (div_le_iff₀ (sq_pos_of_pos ha)).mp hta
    nlinarith
  have hsq : 2 + t ≤ (2 + a * t) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hmul ht0
    nlinarith [sq_nonneg (a * t)]
  have hlog : Real.log (2 + t) ≤ 2 * Real.log (2 + a * t) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by linarith : 0 < 2 + t) hsq
  have hl0 : 0 ≤ Real.log (2 + a * t) := Real.log_nonneg (by linarith)
  have hK : 1 ≤ 1 + 2 / a := le_add_of_nonneg_right (by positivity)
  have hKa : 2 ≤ (1 + 2 / a) * a := by
    rw [add_mul, div_mul_cancel₀ _ ha.ne']
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog ht0
  have hn := mul_le_mul_of_nonneg_right hKa (mul_nonneg ht0 hl0)
  unfold profileBase
  nlinarith

/-- A positive scale factor in the base gives the corresponding negative-power bound. -/
private lemma profile_scale_eventually (a q : ℝ) (ha : 0 < a) (hq : 0 ≤ q) :
    ∀ᶠ t : ℝ in atTop, (profileBase (a * t)) ^ (-q) ≤
      (1 + 2 / a) ^ q * (profileBase t) ^ (-q) := by
  filter_upwards [profileBase_scale_eventually a ha, eventually_ge_atTop (0 : ℝ)]
    with t ht ht0
  have hK : 0 < 1 + 2 / a := by positivity
  have hb : 0 < profileBase t := lt_of_lt_of_le zero_lt_one (profileBase_one_le ht0)
  have h := Real.rpow_le_rpow_of_nonpos hb ht (neg_nonpos.mpr hq)
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hK.le q)
  rw [Real.mul_rpow hK.le (zero_le_one.trans
    (profileBase_one_le (mul_nonneg ha.le ht0))), ← mul_assoc,
    ← Real.rpow_add hK, add_neg_cancel, Real.rpow_zero, one_mul] at hm
  exact hm

/-- The profile base grows at most cubically for sufficiently large arguments. -/
private lemma profileBase_le_cube {t : ℝ} (ht : 3 ≤ t) : profileBase t ≤ t ^ 3 := by
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + t)
  have hm := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ t)
  have hc := mul_nonneg (by nlinarith : 0 ≤ t ^ 2 - t - 1)
    (by linarith : 0 ≤ t - 1)
  unfold profileBase
  nlinarith

/-- Exponential decay dominates the reciprocal logarithmic profile eventually. -/
private lemma exp_le_profile_eventually (b q : ℝ) (hb : 0 < b) (hq : 0 ≤ q) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-b * t) ≤ (profileBase t) ^ (-q) := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 * q) b hb
  have he : ∀ᶠ t : ℝ in atTop, t ^ (3 * q) * Real.exp (-b * t) ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_ge_atTop (3 : ℝ)] with t ht ht3
  have ht0 : 0 ≤ t := by linarith
  have hb0 : 0 < profileBase t :=
    lt_of_lt_of_le zero_lt_one (profileBase_one_le ht0)
  have hp : (profileBase t) ^ q ≤ t ^ (3 * q) := by
    calc
      (profileBase t) ^ q ≤ (t ^ (3 : ℕ)) ^ q :=
        Real.rpow_le_rpow hb0.le (profileBase_le_cube ht3) hq
      _ = t ^ (3 * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
        norm_num
  have hm := (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans ht
  rw [Real.rpow_neg hb0.le]
  rw [← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hb0 q)).mpr (by simpa [mul_comm] using hm)

/-- Poisson averaging preserves the critical logarithmic decay profile. -/
theorem poisson_average_profile_le (d : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∑' n : ℕ, Real.exp (-(Λ * t)) * (Λ * t) ^ n / n.factorial *
          (1 + n * Real.log (2 + n)) ^ (-((d : ℝ) / 2)) ≤
        C * (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) := by
  let q : ℝ := (d : ℝ) / 2
  let a : ℝ := Λ / 4
  have hq : 0 ≤ q := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hev : ∀ᶠ t : ℝ in atTop,
      (profileBase (a * t)) ^ (-q) + Real.exp (-a * t) ≤
        ((1 + 2 / a) ^ q + 1) * (profileBase t) ^ (-q) := by
    filter_upwards [profile_scale_eventually a q ha hq,
      exp_le_profile_eventually a q ha hq] with t ht he
    calc
      _ ≤ (1 + 2 / a) ^ q * (profileBase t) ^ (-q) +
          (profileBase t) ^ (-q) := add_le_add ht he
      _ = _ := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let R : ℝ := max 0 T
  let C : ℝ := (1 + 2 / a) ^ q + 1 + (profileBase R) ^ q
  have hR : 0 ≤ R := le_max_left _ _
  have hpR : 0 ≤ (profileBase R) ^ q :=
    Real.rpow_nonneg (zero_le_one.trans (profileBase_one_le hR)) q
  have hCR : (profileBase R) ^ q ≤ C := by
    exact le_add_of_nonneg_left (by positivity)
  have hCK : (1 + 2 / a) ^ q + 1 ≤ C := by
    exact le_add_of_nonneg_right hpR
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht
  have hs : 0 ≤ Λ * t := mul_nonneg hΛ.le ht
  have hsum := poisson_average_le_profile_add_exp d (Λ * t) hs
  change (∑' n : ℕ, Real.exp (-(Λ * t)) * (Λ * t) ^ n / n.factorial *
    (profileBase n) ^ (-q)) ≤ C * (profileBase t) ^ (-q)
  by_cases htR : R ≤ t
  · have hlarge := hT t ((le_max_right 0 T).trans htR)
    have heq : Λ * t / 4 = a * t := by dsimp [a]; ring
    have hneg : -(Λ * t) / 4 = -a * t := by dsimp [a]; ring
    rw [heq, hneg] at hsum
    exact hsum.trans (hlarge.trans (mul_le_mul_of_nonneg_right hCK
      (profile_bounds q hq ht).1))
  · have hsmall : t ≤ R := le_of_not_ge htR
    have hone : (∑' n : ℕ, Real.exp (-(Λ * t)) * (Λ * t) ^ n / n.factorial *
        (profileBase n) ^ (-q)) ≤ 1 := by
      apply hasSum_le _ (poisson_profile_summable d (Λ * t) hs).hasSum
        (poisson_weights_hasSum hs)
      intro n
      exact mul_le_of_le_one_right (by positivity)
        (profile_bounds q hq (Nat.cast_nonneg n)).2
    have hp := Real.rpow_le_rpow_of_nonpos
      (lt_of_lt_of_le zero_lt_one (profileBase_one_le ht))
      (profileBase_mono ht hsmall) (neg_nonpos.mpr hq)
    have hpos : 0 < profileBase R :=
      lt_of_lt_of_le zero_lt_one (profileBase_one_le hR)
    calc
      _ ≤ 1 := hone
      _ = (profileBase R) ^ q * (profileBase R) ^ (-q) := by
        rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
      _ ≤ C * (profileBase t) ^ (-q) :=
        mul_le_mul hCR hp (profile_bounds q hq hR).1 (by dsimp [C]; positivity)

end

end LatticeProb
