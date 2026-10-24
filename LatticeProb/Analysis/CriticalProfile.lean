import LatticeProb.External.ChenKimKumagaiWang
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Critical logarithmic heat profile

The critical profile is positive and strictly decreasing on positive times.
Uniform comparison estimates preserve constants independent of time.
-/

namespace LatticeProb

open Filter
open scoped Topology

noncomputable section

/-- The critical logarithmic on-diagonal profile in dimension `d`. -/
def criticalProfile (d : ℕ) (t : ℝ) : ℝ :=
  (t * (1 + Real.log (1 + t))) ^ (-((d : ℝ) / 2))

/-- The logarithmic factor is positive at every positive time. -/
lemma criticalProfile_log_pos {t : ℝ} (ht : 0 < t) : 0 < 1 + Real.log (1 + t) := by
  have := Real.log_nonneg (show 1 ≤ 1 + t by linarith)
  linarith

/-- The critical profile is positive at every positive time. -/
theorem criticalProfile_pos (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < criticalProfile d t :=
  Real.rpow_pos_of_pos (mul_pos ht (criticalProfile_log_pos ht)) _

/-- Positive dimension makes the critical profile strictly decreasing. -/
theorem criticalProfile_strictAntiOn {d : ℕ} (hd : 1 ≤ d) :
    StrictAntiOn (criticalProfile d) (Set.Ioi 0) := by
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  have hlog := Real.log_le_log (by linarith : 0 < 1 + s) (by linarith : 1 + s ≤ 1 + t)
  have hbase : s * (1 + Real.log (1 + s)) < t * (1 + Real.log (1 + t)) :=
    (mul_lt_mul_of_pos_right hst (criticalProfile_log_pos hs)).trans_le
      (mul_le_mul_of_nonneg_left (by linarith) ht.le)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  exact Real.rpow_lt_rpow_of_neg (mul_pos hs (criticalProfile_log_pos hs)) hbase
    (by linarith)

/-- The profile is continuously differentiable on the positive half-line. -/
theorem criticalProfile_contDiffOn (d : ℕ) :
    ContDiffOn ℝ 1 (criticalProfile d) (Set.Ioi 0) := by
  apply ContDiffOn.rpow_const_of_ne
    (contDiffOn_id.mul (contDiffOn_const.add
      ((contDiffOn_const.add contDiffOn_id).log (by
        intro t ht
        exact ne_of_gt (by simpa using add_pos zero_lt_one ht)))))
  intro t ht
  exact ne_of_gt (mul_pos ht (criticalProfile_log_pos ht))

/-- The base of the critical profile is controlled by the usual on-diagonal base. -/
lemma criticalProfile_base_le {t : ℝ} (ht : 0 < t) :
    t * (1 + Real.log (1 + t)) ≤ 3 * (1 + t * Real.log (2 + t)) := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (2 + t) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog := Real.log_le_log (by linarith : 0 < 1 + t) (by linarith : 1 + t ≤ 2 + t)
  have hmul := mul_le_mul_of_nonneg_left hlog ht.le
  have htime := mul_le_mul_of_nonneg_left hhalf ht.le
  nlinarith

/-- The usual on-diagonal profile is bounded by the critical profile uniformly in time. -/
theorem criticalProfile_comparison (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t > 0,
      (1 + t * Real.log (2 + t)) ^ (-((d : ℝ) / 2)) ≤ B * criticalProfile d t := by
  refine ⟨(3 : ℝ) ^ ((d : ℝ) / 2), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro t ht
  have hp := mul_pos ht (criticalProfile_log_pos ht)
  have hbase := criticalProfile_base_le ht
  have hpow := Real.rpow_le_rpow_of_nonpos
    (y := 1 + t * Real.log (2 + t)) (div_pos hp (by norm_num))
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by nlinarith [hbase]))
    (neg_nonpos.mpr (by positivity : 0 ≤ (d : ℝ) / 2))
  simpa only [Real.div_rpow hp.le (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_inv_eq_mul, criticalProfile,
    mul_comm] using hpow

/-- Scaling the time base costs at most a logarithmic multiple of the scale. -/
lemma criticalProfile_base_scale {s t k : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hk : 1 ≤ k) (hst : s ≤ k * t) :
    s * (1 + Real.log (1 + s)) ≤
      (k * (1 + Real.log k)) * (t * (1 + Real.log (1 + t))) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hlogk := Real.log_nonneg hk
  have hlogt := Real.log_nonneg (show 1 ≤ 1 + t by linarith)
  have hlog : Real.log (1 + s) ≤ Real.log k + Real.log (1 + t) := by
    rw [← Real.log_mul hkpos.ne' (by linarith : 1 + t ≠ 0)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  calc
    s * (1 + Real.log (1 + s)) ≤
        s * ((1 + Real.log k) * (1 + Real.log (1 + t))) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      nlinarith [mul_nonneg hlogk hlogt]
    _ ≤ (k * t) * ((1 + Real.log k) * (1 + Real.log (1 + t))) :=
      mul_le_mul_of_nonneg_right hst (by positivity)
    _ = _ := by ring

/-- Every positive time dilation has a comparison constant depending only on it and `d`. -/
theorem criticalProfile_scale (d : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ B : ℝ, 0 < B ∧ ∀ t > 0, criticalProfile d (b * t) ≤ B * criticalProfile d t := by
  let k := max 1 b⁻¹
  have hk : 1 ≤ k := le_max_left _ _
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkb : 1 ≤ k * b := by
    have := mul_le_mul_of_nonneg_right (le_max_right 1 b⁻¹) hb.le
    simpa only [inv_mul_cancel₀ hb.ne'] using this
  let K := k * (1 + Real.log k)
  have hK : 0 < K := mul_pos hkpos (by have := Real.log_nonneg hk; linarith)
  refine ⟨K ^ ((d : ℝ) / 2), Real.rpow_pos_of_pos hK _, ?_⟩
  intro t ht
  have hbase := criticalProfile_base_scale ht (mul_pos hb ht) hk
    (show t ≤ k * (b * t) by nlinarith [mul_le_mul_of_nonneg_right hkb ht.le])
  have hp := mul_pos ht (criticalProfile_log_pos ht)
  have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hp hK)
    ((div_le_iff₀ hK).2 (by simpa only [K, mul_comm] using hbase))
    (neg_nonpos.mpr (by positivity : 0 ≤ (d : ℝ) / 2))
  rw [mul_comm (K ^ ((d : ℝ) / 2))]
  simpa only [Real.div_rpow hp.le hK.le, Real.rpow_neg hK.le, div_inv_eq_mul,
    criticalProfile] using hpow

/-- A factor-two change in time costs at most `2^d` in the profile. -/
theorem criticalProfile_doubling (d : ℕ) {t : ℝ} (ht : 0 < t) :
    criticalProfile d t ≤ (2 : ℝ) ^ d * criticalProfile d (2 * t) := by
  have hbase := criticalProfile_base_scale (mul_pos (by norm_num : (0 : ℝ) < 2) ht)
    ht (by norm_num : (1 : ℝ) ≤ 2) (le_refl (2 * t))
  have hlog : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hpos := mul_pos ht (criticalProfile_log_pos ht)
  have hbound : (2 * t) * (1 + Real.log (1 + 2 * t)) / 4 ≤
      t * (1 + Real.log (1 + t)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hfactor : 2 * (1 + Real.log 2) ≤ (4 : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hfactor hpos.le
    exact hbase.trans (by simpa only [mul_comm] using hmul)
  have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht)
    (criticalProfile_log_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ht))
  have hpow := Real.rpow_le_rpow_of_nonpos (div_pos hp (by norm_num)) hbound
    (neg_nonpos.mpr (by positivity : 0 ≤ (d : ℝ) / 2))
  have hfour : (4 : ℝ) ^ ((d : ℝ) / 2) = (2 : ℝ) ^ d := by
    calc
      (4 : ℝ) ^ ((d : ℝ) / 2) = ((2 : ℝ) ^ (2 : ℝ)) ^ ((d : ℝ) / 2) := by norm_num
      _ = (2 : ℝ) ^ (2 * ((d : ℝ) / 2)) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = (2 : ℝ) ^ (d : ℝ) := by congr 1; ring
      _ = (2 : ℝ) ^ d := Real.rpow_natCast _ _
  rw [mul_comm ((2 : ℝ) ^ d)]
  simpa only [Real.div_rpow hp.le (by norm_num : (0 : ℝ) ≤ 4),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul, hfour,
    criticalProfile] using hpow

/-- The negative logarithm has the explicit critical logarithmic derivative. -/
theorem criticalProfile_log_hasDerivAt (d : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u ↦ -Real.log (criticalProfile d u))
      (((d : ℝ) / 2) * (1 / t + 1 / ((1 + t) * (1 + Real.log (1 + t))))) t := by
  have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have h2 := (criticalProfile_log_pos ht).ne'
  have hlog := ((hasDerivAt_id t).const_add 1).log h1
  have hsum := (Real.hasDerivAt_log ht.ne').add ((hlog.const_add 1).log h2)
  have hder := hsum.const_mul ((d : ℝ) / 2)
  have heq : (fun u ↦ -Real.log (criticalProfile d u)) =ᶠ[nhds t]
      (fun u ↦ ((d : ℝ) / 2) * (Real.log u + Real.log (1 + Real.log (1 + u)))) := by
    filter_upwards [eventually_gt_nhds ht] with u hu
    rw [criticalProfile, Real.log_rpow (mul_pos hu (criticalProfile_log_pos hu)),
      Real.log_mul hu.ne' (criticalProfile_log_pos hu).ne']
    ring
  apply (hder.congr_of_eventuallyEq heq).congr_deriv
  dsimp
  field_simp

/-- The critical logarithmic derivative is between `d/(2t)` and `d/t`. -/
theorem criticalProfile_log_deriv_bounds (d : ℕ) {t : ℝ} (ht : 0 < t) :
    ((d : ℝ) / 2) / t ≤ deriv (fun u ↦ -Real.log (criticalProfile d u)) t ∧
      deriv (fun u ↦ -Real.log (criticalProfile d u)) t ≤ (d : ℝ) / t := by
  rw [(criticalProfile_log_hasDerivAt d ht).deriv]
  have hlog := Real.log_nonneg (show 1 ≤ 1 + t by linarith)
  have hfactor := criticalProfile_log_pos ht
  have hden : t ≤ (1 + t) * (1 + Real.log (1 + t)) := by nlinarith
  have hinv := one_div_le_one_div_of_le ht hden
  have hnonneg : 0 ≤ 1 / ((1 + t) * (1 + Real.log (1 + t))) := by positivity
  constructor
  · calc
      ((d : ℝ) / 2) / t = ((d : ℝ) / 2) * (1 / t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnonneg)
        (by positivity)
  · calc
      _ ≤ ((d : ℝ) / 2) * (1 / t + 1 / t) :=
        mul_le_mul_of_nonneg_left
          (show 1 / t + 1 / ((1 + t) * (1 + Real.log (1 + t))) ≤ 1 / t + 1 / t
            from add_le_add (le_refl (1 / t)) hinv) (by positivity)
      _ = (d : ℝ) / t := by ring

/-- At large times the critical profile tends to zero in positive dimension. -/
theorem criticalProfile_tendsto_atTop {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (criticalProfile d) atTop (𝓝 0) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  apply (tendsto_rpow_neg_atTop (by positivity : 0 < (d : ℝ) / 2)).comp
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have := Real.log_nonneg (show 1 ≤ 1 + t by linarith)
  change t ≤ t * (1 + Real.log (1 + t))
  nlinarith

/-- At zero from the right the critical profile diverges in positive dimension. -/
theorem criticalProfile_tendsto_zero {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (criticalProfile d) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  apply (tendsto_rpow_neg_nhdsGT_zero (by linarith : -((d : ℝ) / 2) < 0)).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hlog : ContinuousAt (fun t : ℝ ↦ Real.log (1 + t)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    have hbase : ContinuousAt (fun t : ℝ ↦ t * (1 + Real.log (1 + t))) 0 :=
      continuousAt_id.mul (continuousAt_const.add hlog)
    simpa only [zero_mul] using hbase.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos ht (criticalProfile_log_pos ht)

/-- The logarithmic derivative satisfies the scale comparison with constant four. -/
theorem criticalProfile_log_deriv_scale (d : ℕ) {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Set.Icc (1 : ℝ) 2) :
    deriv (fun u ↦ -Real.log (criticalProfile d u)) t ≤
      4 * deriv (fun u ↦ -Real.log (criticalProfile d u)) (a * t) := by
  have ha' : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
  have hupper := (criticalProfile_log_deriv_bounds d ht).2
  have hlower := (criticalProfile_log_deriv_bounds d (mul_pos ha' ht)).1
  have hcompare : (d : ℝ) / t ≤ 4 * (((d : ℝ) / 2) / (a * t)) := by
    apply (div_le_iff₀ ht).2
    field_simp
    nlinarith [show (0 : ℝ) ≤ d by positivity, ha.2]
  exact hupper.trans (hcompare.trans (mul_le_mul_of_nonneg_left hlower (by norm_num)))

/-- The derivative comparison clause of CKKW regularity holds with `N(t) = 1/t`. -/
theorem criticalProfile_derivative_comparison {d : ℕ} (hd : 1 ≤ d) :
    ∃ c c₀ : ℝ, 1 ≤ c ∧ 0 < c₀ ∧
      (∀ t > 0, 0 < (1 / t : ℝ)) ∧
      AntitoneOn (fun t : ℝ ↦ 1 / t) (Set.Ioi 0) ∧
      (∀ t > 0, c⁻¹ * (1 / t) ≤ deriv (fun u ↦ -Real.log (criticalProfile d u)) t ∧
        deriv (fun u ↦ -Real.log (criticalProfile d u)) t ≤ c * (1 / t)) ∧
      ∀ t > 0, ∀ a ∈ Set.Icc (1 : ℝ) 2,
        deriv (fun u ↦ -Real.log (criticalProfile d u)) t ≤
          c₀ * deriv (fun u ↦ -Real.log (criticalProfile d u)) (a * t) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  let c : ℝ := max 1 (max d (2 / d))
  have hc : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hdc : (d : ℝ) ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hdivc : 2 / (d : ℝ) ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hinvc : c⁻¹ ≤ (d : ℝ) / 2 := by
    have hmul := (div_le_iff₀ hd').1 hdivc
    apply (inv_le_iff_one_le_mul₀ hcpos).2
    nlinarith
  refine ⟨c, 4, hc, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact one_div_pos.mpr ht
  · intro s hs t ht hst
    exact one_div_le_one_div_of_le hs hst
  · intro t ht
    obtain ⟨hlo, hhi⟩ := criticalProfile_log_deriv_bounds d ht
    constructor
    · calc
        c⁻¹ * (1 / t) ≤ ((d : ℝ) / 2) * (1 / t) :=
          mul_le_mul_of_nonneg_right hinvc (by positivity)
        _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using hlo
    · calc
        _ ≤ (d : ℝ) / t := hhi
        _ ≤ c * (1 / t) := by
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_right hdc (inv_nonneg.mpr ht.le)
  · intro t ht a ha
    exact criticalProfile_log_deriv_scale d ht ha

/-- Shrinking positive time by `σ ≤ 1` costs at most `σ⁻ᵈ`. -/
theorem criticalProfile_shrink (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (ht : 0 < t) :
    criticalProfile d (σ * t) ≤ σ ^ (-(d : ℝ)) * criticalProfile d t := by
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 + t ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith)
    (show 0 ≤ 1 - σ by linarith) hσ.le (by ring : 1 - σ + σ = 1)
  have hlog : σ * Real.log (1 + t) ≤ Real.log (1 + σ * t) := by
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add,
      show (1 - σ) * 1 + σ * (1 + t) = 1 + σ * t by ring] using hconc
  have hb : σ ^ 2 * (t * (1 + Real.log (1 + t))) ≤
      (σ * t) * (1 + Real.log (1 + σ * t)) := by
    have := mul_le_mul_of_nonneg_left (show σ * (1 + Real.log (1 + t)) ≤
      1 + Real.log (1 + σ * t) by nlinarith) (mul_pos hσ ht).le
    nlinarith only [this]
  have hp := mul_pos ht (criticalProfile_log_pos ht)
  have hr := Real.rpow_le_rpow_of_nonpos (mul_pos (sq_pos_of_pos hσ) hp) hb
    (neg_nonpos.mpr (by positivity : 0 ≤ (d : ℝ) / 2))
  have he : (σ ^ 2) ^ (-((d : ℝ) / 2)) = σ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ.le]
    congr 1
    ring
  simpa only [Real.mul_rpow (sq_nonneg σ) hp.le, he, criticalProfile] using hr

/-- The dyadic product weights have total mass one and first shifted moment three. -/
lemma criticalProfile_product_weights :
    HasSum (fun n : ℕ ↦ (2 : ℝ) ^ (-(n + 1 : ℤ))) 1 ∧
      HasSum (fun n : ℕ ↦ (2 : ℝ) ^ (-(n + 1 : ℤ)) * ((n : ℝ) + 2)) 3 := by
  have hw (n : ℕ) : (2 : ℝ) ^ (-(n + 1 : ℤ)) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
    simp only [zpow_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      zpow_natCast, zpow_one, mul_inv_rev, one_div, inv_pow]
  have hg := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  constructor
  · simpa only [hw] using (show HasSum (fun n : ℕ ↦
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n) 1 by
        convert! hg.mul_left (1 / 2 : ℝ) using 1
        norm_num)
  · have h := (hn.add (hg.mul_left 2)).mul_left (1 / 2 : ℝ)
    convert! h using 1
    · ext n
      rw [hw]
      ring
    · norm_num

/-- Every geometric time factor in the CKKW product lies in `(0,1]`. -/
lemma criticalProfile_product_scale {l : ℝ} (hl : 2 < l) (n : ℕ) :
    0 < (l - 1) * l ^ (-(n + 2 : ℤ)) ∧ (l - 1) * l ^ (-(n + 2 : ℤ)) ≤ 1 := by
  have hl₀ : 0 < l := by linarith
  constructor
  · exact mul_pos (by linarith) (zpow_pos hl₀ _)
  · have hp : l ^ (-(n + 2 : ℤ)) ≤ l ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by linarith) (by omega)
    calc
      (l - 1) * l ^ (-(n + 2 : ℤ)) ≤ (l - 1) * l ^ (-1 : ℤ) :=
        mul_le_mul_of_nonneg_left hp (by linarith)
      _ ≤ 1 := by rw [zpow_neg_one]; exact (mul_inv_le_iff₀ hl₀).2 (by linarith)

/-- The profile logarithm at each product time has an affine upper bound in the index. -/
lemma criticalProfile_product_log_bounds {d : ℕ} (hd : 1 ≤ d) {l t : ℝ}
    (hl : 2 < l) (ht : 0 < t) (n : ℕ) :
    0 ≤ Real.log (criticalProfile d ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)) -
        Real.log (criticalProfile d t) ∧
      Real.log (criticalProfile d ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)) -
        Real.log (criticalProfile d t) ≤
          (d : ℝ) * (((n : ℝ) + 2) * Real.log l - Real.log (l - 1)) := by
  obtain ⟨hσ, hσ₁⟩ := criticalProfile_product_scale hl n
  have hp := criticalProfile_pos d (mul_pos hσ ht)
  have htφ := criticalProfile_pos d ht
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log htφ
      ((criticalProfile_strictAntiOn hd).antitoneOn (mul_pos hσ ht) ht
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ₁ ht.le)))
  · have hb := Real.log_le_log hp (criticalProfile_shrink d hσ hσ₁ ht)
    rw [Real.log_mul (Real.rpow_pos_of_pos hσ _).ne' htφ.ne',
      Real.log_rpow hσ, Real.log_mul (by linarith : l - 1 ≠ 0)
        (zpow_ne_zero _ (by linarith : l ≠ 0)), Real.log_zpow] at hb
    push_cast at hb
    nlinarith only [hb]

/-- The critical profile satisfies the CKKW infinite product estimate. -/
theorem criticalProfile_productBound {d : ℕ} (hd : 1 ≤ d) {l : ℝ} (hl : 2 < l) :
    External.ckkwProductBound (criticalProfile d) l 1 ((l ^ 3 / (l - 1)) ^ d) := by
  intro t ht
  let w := fun n : ℕ ↦ (2 : ℝ) ^ (-(n + 1 : ℤ))
  let a := Real.log (criticalProfile d t)
  let g := fun n : ℕ ↦ w n *
    (Real.log (criticalProfile d ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)) - a)
  let u := fun n : ℕ ↦ w n *
    ((d : ℝ) * (((n : ℝ) + 2) * Real.log l - Real.log (l - 1)))
  obtain ⟨hw, hm⟩ := criticalProfile_product_weights
  have hu : HasSum u ((d : ℝ) * (3 * Real.log l - Real.log (l - 1))) := by
    convert! ((hm.mul_right (Real.log l)).sub
      (hw.mul_right (Real.log (l - 1)))).mul_right (d : ℝ) using 1
    · ext n
      dsimp [u, w]
      ring
    · ring
  have hg₀ (n : ℕ) : 0 ≤ g n :=
    mul_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
      (criticalProfile_product_log_bounds hd hl ht n).1
  have hgu (n : ℕ) : g n ≤ u n :=
    mul_le_mul_of_nonneg_left (criticalProfile_product_log_bounds hd hl ht n).2
      (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hg : Summable g := Summable.of_nonneg_of_le hg₀ hgu hu.summable
  have hsum : (∑' n, g n) ≤ (d : ℝ) * (3 * Real.log l - Real.log (l - 1)) := by
    rw [← hu.tsum_eq]
    exact hg.tsum_le_tsum hgu hu.summable
  have hf : HasSum (fun n : ℕ ↦ w n *
      Real.log (criticalProfile d ((l - 1) * l ^ (-(n + 2 : ℤ)) * t)))
      ((∑' n, g n) + a) := by
    convert! hg.hasSum.add (hw.mul_right a) using 1
    · ext n
      dsimp [g]
      ring
    · ring
  refine ⟨Real.exp ((∑' n, g n) + a), ?_, ?_⟩
  · convert! hf.rexp using 1
    ext n
    dsimp [Function.comp_def, w]
    rw [Real.rpow_def_of_pos
      (criticalProfile_pos d (mul_pos (criticalProfile_product_scale hl n).1 ht))]
    congr 1
    ring
  · rw [one_mul]
    have hl₀ : 0 < l := by linarith
    have hl₁ : 0 < l - 1 := by linarith
    have hc : 0 < (l ^ 3 / (l - 1)) ^ d := pow_pos (div_pos (pow_pos hl₀ _) hl₁) _
    have hexp : Real.exp ((∑' n, g n) + a) ≤
        Real.exp ((d : ℝ) * (3 * Real.log l - Real.log (l - 1)) + a) :=
      Real.exp_le_exp.mpr (by linarith only [hsum])
    apply hexp.trans
    apply le_of_eq
    rw [← Real.exp_log (mul_pos hc (criticalProfile_pos d ht))]
    congr 1
    rw [Real.log_mul hc.ne' (criticalProfile_pos d ht).ne', Real.log_pow,
      Real.log_div (pow_pos hl₀ _).ne' hl₁.ne', Real.log_pow]
    rfl

/-- Explicit positive witnesses give the product-profile clause of CKKW regularity. -/
theorem criticalProfile_productProfile {d : ℕ} (hd : 1 ≤ d) :
    External.ckkwProductData (fun _ ↦ 1) (fun l ↦ (l ^ 3 / (l - 1)) ^ d) ∧
      External.ckkwProductProfile (criticalProfile d) (fun _ ↦ 1)
        (fun l ↦ (l ^ 3 / (l - 1)) ^ d) := by
  constructor
  · refine ⟨3, by norm_num, ?_⟩
    intro l hl
    exact ⟨zero_lt_one, pow_pos (div_pos (pow_pos (by linarith) _) (by linarith)) _⟩
  · intro l hl _ _
    exact criticalProfile_productBound hd hl

/-- In positive dimension the critical logarithmic profile is CKKW regular. -/
theorem criticalProfile_ckkwRegular {d : ℕ} (hd : 1 ≤ d) :
    External.ckkwRegular (criticalProfile d) := by
  obtain ⟨c, c₀, hc, hc₀, hpos, hanti, hcompare, hscale⟩ :=
    criticalProfile_derivative_comparison hd
  exact ⟨fun _ ht ↦ criticalProfile_pos d ht, criticalProfile_strictAntiOn hd,
    criticalProfile_contDiffOn d, criticalProfile_tendsto_zero hd,
    criticalProfile_tendsto_atTop hd,
    ⟨c, c₀, fun t ↦ 1 / t, hc, hc₀, hpos, hanti, hcompare, hscale⟩,
    ⟨fun _ ↦ 1, fun l ↦ (l ^ 3 / (l - 1)) ^ d, criticalProfile_productProfile hd⟩⟩

end

end LatticeProb
