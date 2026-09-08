/-
The pointwise inequality behind the von Bahr-Esseen moment bound.

For `1 ≤ p ≤ 2` and all reals,

    |a + b|^p ≤ |a|^p + p·sgn(a)·|a|^{p-1}·b + 2|b|^p .

Integrating it against an independent centred `b` kills the middle term, which is
how `E|∑ Y_i|^p ≤ C_p ∑ E|Y_i|^p` is proved by induction on the family; that
induction is not here, only the analytic step it rests on.

Three elementary bounds do it, and each is stated separately because each is
reusable.  For `a, b ≥ 0`, the fundamental theorem of calculus applied to
`s ↦ (a+s)^p` together with the subadditivity of `t ↦ t^{p-1}` (Mathlib's
`Real.rpow_add_le_add_rpow`, valid because `p - 1 ≤ 1`) gives

    (a+b)^p ≤ a^p + p a^{p-1} b + b^p .

Young's inequality at the conjugate pair `(p, p/(p-1))` gives

    p a^{p-1} c ≤ (p-1) a^p + c^p ≤ a^p + c^p ,

which covers the case where the negative increment `c = -b` overshoots `a`.  And for
`0 ≤ c ≤ a`, the same fundamental theorem bounds `a^p - (a-c)^p` from below by
`p c (a-c)^{p-1}`, which with the subadditivity again gives

    (a-c)^p ≤ a^p - p a^{p-1} c + 2 c^p ,

the constant `2` coming from `p ≤ 2`.  Reduction to `a ≥ 0` is the symmetry
`(a,b) ↦ (-a,-b)`.
-/
import Mathlib

open Real

namespace LatticeProb

theorem rpow_mul_le_add_rpow {p a c : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    p * a ^ (p - 1) * c ≤ a ^ p + c ^ p := by
  rcases eq_or_lt_of_le hp1 with hp | hp
  · have h1 : p - 1 = 0 := by linarith
    rw [h1, Real.rpow_zero, ← hp, Real.rpow_one, Real.rpow_one]
    linarith
  · have hp0 : (0 : ℝ) < p := by linarith
    have hpm : (0 : ℝ) < p - 1 := by linarith
    have hconj : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
    have hq : Real.conjExponent p = p / (p - 1) := by rw [Real.conjExponent]
    have hyoung := Real.young_inequality c (a ^ (p - 1)) hconj
    have habs1 : |c| = c := abs_of_nonneg hc
    have habs2 : |a ^ (p - 1)| = a ^ (p - 1) := abs_of_nonneg (Real.rpow_nonneg ha _)
    rw [habs1, habs2, hq] at hyoung
    have hpow : (a ^ (p - 1)) ^ (p / (p - 1)) = a ^ p := by
      rw [← Real.rpow_mul ha]
      congr 1
      field_simp
    rw [hpow] at hyoung
    have hanonneg : (0 : ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
    have hqpos : (0 : ℝ) < p / (p - 1) := by positivity
    have hkey : p * (c * a ^ (p - 1)) ≤ p * (c ^ p / p + a ^ p / (p / (p - 1))) :=
      mul_le_mul_of_nonneg_left hyoung (le_of_lt hp0)
    have he : p * (c ^ p / p + a ^ p / (p / (p - 1))) = c ^ p + (p - 1) * a ^ p := by
      field_simp
    rw [he] at hkey
    nlinarith [hkey, hanonneg]


theorem add_rpow_le_of_le_two {p a b : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ a ^ p + p * a ^ (p - 1) * b + b ^ p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ p - 1 := by linarith
  have hq1 : p - 1 ≤ 1 := by linarith
  have hderiv : ∀ s : ℝ, HasDerivAt (fun v : ℝ => (a + v) ^ p) (p * (a + s) ^ (p - 1)) s := by
    intro s
    have h1 : HasDerivAt (fun v : ℝ => a + v) 1 s := by
      simpa using (hasDerivAt_id s).const_add a
    have h2 := h1.rpow_const (p := p) (Or.inr hp1)
    simpa using h2
  have hcont : Continuous fun s : ℝ => p * (a + s) ^ (p - 1) := by
    fun_prop
  have hfd : (a + b) ^ p - (a + 0) ^ p = ∫ s in (0:ℝ)..b, p * (a + s) ^ (p - 1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable 0 b)]
  have hbound : ∫ s in (0:ℝ)..b, p * (a + s) ^ (p - 1)
      ≤ ∫ s in (0:ℝ)..b, (p * a ^ (p - 1) + p * s ^ (p - 1)) := by
    refine intervalIntegral.integral_mono_on hb (hcont.intervalIntegrable 0 b) ?_ ?_
    · have : Continuous fun s : ℝ => p * a ^ (p - 1) + p * s ^ (p - 1) := by fun_prop
      exact this.intervalIntegrable 0 b
    · intro s hs
      have hs0 : 0 ≤ s := hs.1
      have := Real.rpow_add_le_add_rpow ha hs0 hq0 hq1
      nlinarith [this, hp0.le]
  have hval : ∫ s in (0:ℝ)..b, (p * a ^ (p - 1) + p * s ^ (p - 1))
      = p * a ^ (p - 1) * b + b ^ p := by
    have hi1 : IntervalIntegrable (fun _ : ℝ => p * a ^ (p - 1)) MeasureTheory.volume 0 b :=
      (continuous_const).intervalIntegrable 0 b
    have hi2 : IntervalIntegrable (fun s : ℝ => p * s ^ (p - 1)) MeasureTheory.volume 0 b := by
      have : Continuous fun s : ℝ => p * s ^ (p - 1) := by fun_prop
      exact this.intervalIntegrable 0 b
    have hsplit : ∫ s in (0:ℝ)..b, (p * a ^ (p - 1) + p * s ^ (p - 1))
        = (∫ _s in (0:ℝ)..b, p * a ^ (p - 1)) + ∫ s in (0:ℝ)..b, p * s ^ (p - 1) :=
      intervalIntegral.integral_add hi1 hi2
    rw [hsplit, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith))]
    have hz : (0 : ℝ) ^ (p - 1 + 1) = 0 := by
      rw [Real.zero_rpow (by linarith)]
    rw [hz]
    have hpp : p - 1 + 1 = p := by ring
    rw [hpp]
    field_simp
    simp only [smul_eq_mul, sub_zero]
    ring
  have hz2 : (a + 0 : ℝ) = a := by ring
  rw [hz2] at hfd
  linarith [hfd, hbound, hval]


theorem sub_rpow_le_of_le {p a c : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : 0 ≤ c) (hca : c ≤ a) :
    (a - c) ^ p ≤ a ^ p - p * a ^ (p - 1) * c + 2 * c ^ p := by
  have ha : 0 ≤ a := le_trans hc hca
  have hac : 0 ≤ a - c := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ p - 1 := by linarith
  have hq1 : p - 1 ≤ 1 := by linarith
  -- the mean value bound
  have hderiv : ∀ s : ℝ, HasDerivAt (fun v : ℝ => v ^ p) (p * s ^ (p - 1)) s :=
    fun s => Real.hasDerivAt_rpow_const (Or.inr hp1)
  have hcont : Continuous fun s : ℝ => p * s ^ (p - 1) := by fun_prop
  have hfd : a ^ p - (a - c) ^ p = ∫ s in (a - c)..a, p * s ^ (p - 1) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
      (hcont.intervalIntegrable _ _)).symm
  have hlow : ∫ _s in (a - c)..a, p * (a - c) ^ (p - 1)
      ≤ ∫ s in (a - c)..a, p * s ^ (p - 1) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const).intervalIntegrable _ _) (hcont.intervalIntegrable _ _) ?_
    intro s hs
    have hs1 : a - c ≤ s := hs.1
    have := Real.rpow_le_rpow hac hs1 hq0
    nlinarith [this, hp0.le]
  have hconst : ∫ _s in (a - c)..a, p * (a - c) ^ (p - 1)
      = c * (p * (a - c) ^ (p - 1)) := by
    rw [intervalIntegral.integral_const]
    have : a - (a - c) = c := by ring
    rw [this, smul_eq_mul]
  -- the subadditivity bound
  have hsub : a ^ (p - 1) ≤ (a - c) ^ (p - 1) + c ^ (p - 1) := by
    have h := Real.rpow_add_le_add_rpow hac hc hq0 hq1
    have he : a - c + c = a := by ring
    rwa [he] at h
  have hcc : c * c ^ (p - 1) = c ^ p := by
    rcases eq_or_lt_of_le hc with hc0 | hc0
    · rw [← hc0, Real.zero_rpow (by linarith : p ≠ 0)]
      ring
    · have h := Real.rpow_add hc0 1 (p - 1)
      rw [Real.rpow_one] at h
      have he : (1 : ℝ) + (p - 1) = p := by ring
      rw [he] at h
      exact h.symm
  have hcpnn : (0 : ℝ) ≤ c ^ p := Real.rpow_nonneg hc p
  have hlow2 : c * (p * (a - c) ^ (p - 1)) ≤ a ^ p - (a - c) ^ p := by
    rw [hfd, ← hconst]
    exact hlow
  have hmul : p * c * a ^ (p - 1) ≤ p * c * ((a - c) ^ (p - 1) + c ^ (p - 1)) :=
    mul_le_mul_of_nonneg_left hsub (by positivity)
  have hexp : p * c * ((a - c) ^ (p - 1) + c ^ (p - 1))
      = c * (p * (a - c) ^ (p - 1)) + p * (c * c ^ (p - 1)) := by ring
  rw [hexp, hcc] at hmul
  have hpc : p * c ^ p ≤ 2 * c ^ p := by nlinarith [hcpnn, hp2]
  have hcomm : p * a ^ (p - 1) * c = p * c * a ^ (p - 1) := by ring
  linarith [hlow2, hmul, hpc, hcomm.le, hcomm.ge]


theorem abs_add_rpow_le_of_nonneg {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) :
    |a + b| ^ p ≤ a ^ p + p * a ^ (p - 1) * b + 2 * |b| ^ p := by
  rcases le_or_gt 0 b with hb | hb
  · have hab : |a + b| = a + b := abs_of_nonneg (by linarith)
    have habs : |b| = b := abs_of_nonneg hb
    have h := add_rpow_le_of_le_two hp1 hp2 ha hb
    have hbp : (0 : ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
    rw [hab, habs]
    linarith
  · have hc : (0 : ℝ) < -b := by linarith
    have habs : |b| = -b := abs_of_neg hb
    have hab' : a + b = a - -b := by ring
    rcases le_or_gt (-b) a with hca | hca
    · have hab : |a + b| = a - -b := by
        rw [hab']
        exact abs_of_nonneg (by linarith)
      have h := sub_rpow_le_of_le hp1 hp2 hc.le hca
      rw [hab, habs]
      linarith
    · have hab : |a + b| = -b - a := by
        rw [hab', abs_of_nonpos (by linarith)]
        ring
      have h1 : (-b - a) ^ p ≤ (-b) ^ p :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      have h2 := rpow_mul_le_add_rpow hp1 hp2 ha hc.le
      rw [hab, habs]
      linarith

/-- **The pointwise von Bahr-Esseen inequality** for `1 ≤ p ≤ 2`:

    | |a+b|^p - |a|^p - p sgn(a) |a|^{p-1} b | is at most `2|b|^p`

in the one-sided form the moment inequality uses. -/
theorem abs_add_rpow_le {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (a b : ℝ) :
    |a + b| ^ p
      ≤ |a| ^ p + p * (if 0 ≤ a then (1 : ℝ) else -1) * |a| ^ (p - 1) * b + 2 * |b| ^ p := by
  rcases le_or_gt 0 a with ha | ha
  · rw [if_pos ha, abs_of_nonneg ha]
    have h := abs_add_rpow_le_of_nonneg hp1 hp2 ha b
    linarith
  · rw [if_neg (by linarith), abs_of_neg ha]
    have hna : (0 : ℝ) ≤ -a := by linarith
    have h := abs_add_rpow_le_of_nonneg hp1 hp2 hna (-b)
    have e1 : |(-a) + (-b)| = |a + b| := by
      rw [show (-a) + (-b) = -(a + b) from by ring, abs_neg]
    have e2 : |(-b)| = |b| := abs_neg b
    rw [e1, e2] at h
    linarith

end LatticeProb
