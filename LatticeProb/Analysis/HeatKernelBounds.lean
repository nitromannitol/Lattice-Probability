import LatticeProb.Analysis.HeatKernel
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Regularity of the heat kernel away from the spatial origin

The heat kernel extends smoothly through time zero away from the spatial origin,
and all its derivatives are bounded away from the origin on bounded time intervals.
-/

open Filter Set Topology
open scoped ContDiff BigOperators

namespace LatticeProb.Heat

private noncomputable def flatGaussian (a x : ℝ) : ℝ := x ^ a * expNegInvGlue x

private lemma flatGaussian_tendsto (a : ℝ) : Tendsto (flatGaussian a) (𝓝 0) (𝓝 0) := by
  unfold flatGaussian
  simp only [expNegInvGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) 1 zero_lt_one).comp
    tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [neg_one_mul]
  dsimp only [Function.comp_apply]
  rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]

private lemma flatGaussian_hasDerivAt (a x : ℝ) :
    HasDerivAt (flatGaussian a) (a * flatGaussian (a - 1) x + flatGaussian (a - 2) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hzero : ∀ᶠ y : ℝ in 𝓝 x, flatGaussian a y = 0 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [flatGaussian, expNegInvGlue.zero_of_nonpos hy.le]
    have hxzero : flatGaussian (a - 1) x = 0 ∧ flatGaussian (a - 2) x = 0 := by
      simp [flatGaussian, expNegInvGlue.zero_of_nonpos hx.le]
    rw [hxzero.1, hxzero.2, mul_zero, add_zero]
    exact (hasDerivAt_const x 0).congr_of_eventuallyEq hzero
  · have hzero : flatGaussian (a - 1) 0 = 0 ∧ flatGaussian (a - 2) 0 = 0 := by
      simp [flatGaussian, expNegInvGlue.zero]
    rw [hzero.1, hzero.2, mul_zero, add_zero, hasDerivAt_iff_tendsto_slope]
    refine ((flatGaussian_tendsto (a - 1)).mono_left inf_le_left).congr ?_
    intro y
    by_cases hy : 0 < y
    · simp only [slope_def_field, flatGaussian, expNegInvGlue.zero, mul_zero, sub_zero]
      rw [div_eq_mul_inv, Real.rpow_sub_one hy.ne']
      ring
    · have hy' : y ≤ 0 := le_of_not_gt hy
      simp [slope_def_field, flatGaussian, expNegInvGlue.zero_of_nonpos hy']
  · have hpow := Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hx.ne')
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y⁻¹))
        (x⁻¹ ^ 2 * Real.exp (-x⁻¹)) x := by
      convert ((hasDerivAt_inv hx.ne').neg.exp) using 1
      simp [Pi.neg_apply]
      ring
    have h := hpow.mul hexp
    have heq : (fun y : ℝ => y ^ a * Real.exp (-y⁻¹)) =ᶠ[𝓝 x] flatGaussian a := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [flatGaussian, expNegInvGlue, not_le_of_gt hy]
    refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
    simp only [flatGaussian, expNegInvGlue, not_le_of_gt hx, ite_false]
    rw [Real.rpow_sub hx, Real.rpow_sub hx]
    simp only [Real.rpow_one, Real.rpow_ofNat]
    field_simp

private lemma flatGaussian_contDiff (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (flatGaussian a) := by
  apply contDiff_all_iff_nat.2 (fun m => ?_) ⊤
  induction m generalizing a with
  | zero => exact contDiff_zero.2 (continuous_iff_continuousAt.mpr (fun x => (flatGaussian_hasDerivAt a x).continuousAt))
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
    refine contDiff_succ_iff_deriv.2 ⟨fun x => (flatGaussian_hasDerivAt a x).differentiableAt,
      by simp, ?_⟩
    have hd : deriv (flatGaussian a) = fun x => a * flatGaussian (a - 1) x + flatGaussian (a - 2) x := by
      funext x
      exact (flatGaussian_hasDerivAt a x).deriv
    rw [hd]
    exact (contDiff_const.mul (ih (a - 1))).add (ih (a - 2))

private noncomputable def energy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, (x i)^2

private lemma energy_pos {d : ℕ} {x : Fin d → ℝ} (hx : x ≠ 0) : 0 < energy x := by
  have h : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext fun i => h i)
  obtain ⟨i, hi⟩ := h
  unfold energy
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

private lemma kernel_factor {d : ℕ} (hd : 1 ≤ d) (t : ℝ) (x : Fin d → ℝ) (hx : x ≠ 0) :
    heatKernel d t x =
      ((2 * Real.pi / d) ^ (-(1 : ℝ) / 2)) ^ d *
      ((d : ℝ) * energy x / 2) ^ (-((d : ℝ) / 2)) *
      flatGaussian (-((d : ℝ) / 2)) (t / ((d : ℝ) * energy x / 2)) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he0 := energy_pos hx
  have he : 0 < (d : ℝ) * energy x / 2 := by positivity
  by_cases ht : 0 < t
  · rw [heatKernel_of_pos ht]
    simp only [heatKernel1, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
    unfold flatGaussian expNegInvGlue
    have htx : 0 < t / ((d : ℝ) * energy x / 2) := div_pos ht he
    simp only [not_le_of_gt htx, ite_false]
    rw [Real.div_rpow ht.le he.le]
    rw [Real.rpow_neg he.le]
    have hc : (2 * Real.pi * t / d) = (2 * Real.pi / d) * t := by ring
    rw [hc, Real.mul_rpow (by positivity) ht.le, mul_pow]
    rw [← Real.rpow_mul_natCast ht.le]
    have hsum : ∑ i : Fin d, (-(d : ℝ) * (x i)^2 / (2*t)) =
        -((d : ℝ) * energy x / 2) / t := by
      unfold energy
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    have hneg : -(t / ((d : ℝ) * energy x / 2))⁻¹ =
        -((d : ℝ) * energy x / 2) / t := by field_simp
    rw [hneg]
    field_simp
  · rw [heatKernel_of_nonpos (le_of_not_gt ht)]
    have ht' : t / ((d : ℝ) * energy x / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt ht) he.le
    simp [flatGaussian, expNegInvGlue.zero_of_nonpos ht']

/-- The heat kernel is smooth away from the spatial origin. -/
theorem contDiffOn_heatKernel_off_origin {d : ℕ} (hd : 1 ≤ d) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => heatKernel d p.1 p.2) {p | p.2 ≠ 0} := by
  have he : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => (d : ℝ) * energy p.2 / 2) := by
    unfold energy
    fun_prop
  have hpos (p : ℝ × (Fin d → ℝ)) (hp : p.2 ≠ 0) :
      0 < (d : ℝ) * energy p.2 / 2 := by
    have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hp' := energy_pos hp
    positivity
  have hr : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => p.1 / ((d : ℝ) * energy p.2 / 2)) {p | p.2 ≠ 0} :=
    contDiff_fst.contDiffOn.div he.contDiffOn (fun p hp => (hpos p hp).ne')
  have hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) => ((d : ℝ) * energy p.2 / 2) ^ (-((d : ℝ) / 2)))
      {p | p.2 ≠ 0} := he.contDiffOn.rpow_const_of_ne (fun p hp => (hpos p hp).ne')
  have hf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin d → ℝ) =>
        ((2 * Real.pi / d) ^ (-(1 : ℝ) / 2)) ^ d *
          ((d : ℝ) * energy p.2 / 2) ^ (-((d : ℝ) / 2)) *
          flatGaussian (-((d : ℝ) / 2)) (p.1 / ((d : ℝ) * energy p.2 / 2))) {p | p.2 ≠ 0} :=
    (contDiffOn_const.mul hp).mul ((flatGaussian_contDiff (-((d : ℝ) / 2))).comp_contDiffOn hr)
  apply hf.congr
  intro p hp
  exact kernel_factor hd p.1 p.2 hp

/-- Every derivative of the heat kernel is bounded on a compact set away from the origin. -/
theorem iteratedFDeriv_heatKernel_bdd_on_compact {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hKx : ∀ p ∈ K, p.2 ≠ 0) :
    ∃ C : ℝ, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤ C := by
  have hopen : IsOpen {p : ℝ × (Fin d → ℝ) | p.2 ≠ 0} :=
    isOpen_ne.preimage continuous_snd
  have hcont := ContinuousOn.continuousOn_iteratedFDeriv (k := n)
    (contDiffOn_heatKernel_off_origin hd) hopen (by simp)
  have hbound := hK.bddAbove_image ((hcont.mono hKx).norm)
  obtain ⟨C, hC⟩ := hbound
  exact ⟨C, fun p hp => hC ⟨p, hp, rfl⟩⟩

private noncomputable def scaleMap (d : ℕ) (s : ℝ) : (ℝ × (Fin d → ℝ)) →L[ℝ] (ℝ × (Fin d → ℝ)) :=
  ((s ^ 2) • ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ)).prod
    (s • ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))

private lemma scaleMap_norm_le (d : ℕ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖scaleMap d s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  simp only [one_mul, scaleMap, ContinuousLinearMap.prod_apply, smul_apply, Prod.norm_def]
  change max ‖s ^ 2 * p.1‖ ‖s • p.2‖ ≤ max ‖p.1‖ ‖p.2‖
  rw [norm_mul, norm_smul]
  simp only [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg (sq_nonneg s)]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right (by nlinarith : s ^ 2 ≤ 1)
      (norm_nonneg p.1)).trans (by simp only [one_mul]; exact (le_max_left ‖p.1‖ ‖p.2‖))
  · exact (mul_le_mul_of_nonneg_right hs1 (norm_nonneg p.2)).trans
      (by simp only [one_mul]; exact (le_max_right ‖p.1‖ ‖p.2‖))

private lemma heatKernel1_parabolic_scale {d : ℕ} (hd : 1 ≤ d) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    heatKernel1 d (s ^ 2 * t) (s * x) = s⁻¹ * heatKernel1 d t x := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  unfold heatKernel1
  have hbase : 2 * Real.pi * (s ^ 2 * t) / d = s ^ 2 * (2 * Real.pi * t / d) := by ring
  rw [hbase, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (s ^ 2) ^ (-(1 : ℝ) / 2) = s⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    exact Real.rpow_neg_one s
  rw [hp]
  have hexp : -(d : ℝ) * (s * x) ^ 2 / (2 * (s ^ 2 * t)) =
      -(d : ℝ) * x ^ 2 / (2 * t) := by field_simp
  rw [hexp]
  ring

private lemma heatKernel_parabolic_scale {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s)
    (p : ℝ × (Fin d → ℝ)) :
    heatKernel d (s ^ 2 * p.1) (s • p.2) = (s⁻¹) ^ d * heatKernel d p.1 p.2 := by
  by_cases ht : 0 < p.1
  · rw [heatKernel_of_pos (mul_pos (sq_pos_of_pos hs) ht), heatKernel_of_pos ht]
    simp_rw [Pi.smul_apply, smul_eq_mul, heatKernel1_parabolic_scale hd hs ht]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have ht' : s ^ 2 * p.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) (le_of_not_gt ht)
    simp [heatKernel_of_nonpos ht', heatKernel_of_nonpos (le_of_not_gt ht)]

private lemma derivative_parabolic_scale {d n : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s)
    (p : ℝ × (Fin d → ℝ)) (hp : p.2 ≠ 0) :
    iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p =
      (s ^ d) • ((iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) =>
        heatKernel d q.1 q.2) (scaleMap d s p)).compContinuousLinearMap fun _ => scaleMap d s) := by
  let U : Set (ℝ × (Fin d → ℝ)) := {q | q.2 ≠ 0}
  let f : ℝ × (Fin d → ℝ) → ℝ := fun q => heatKernel d q.1 q.2
  let A := scaleMap d s
  have hU : IsOpen U := isOpen_ne.preimage continuous_snd
  have hAU : IsOpen (A ⁻¹' U) := hU.preimage A.continuous
  have hpU : A p ∈ U := by
    change s • p.2 ≠ 0
    exact smul_ne_zero hs.ne' hp
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := contDiffOn_heatKernel_off_origin hd
  have hcomp : ContDiffAt ℝ (n : ℕ∞) (f ∘ A) p := by
    exact (((hf.comp_continuousLinearMap A).contDiffAt (hAU.mem_nhds hpU)).of_le (by simp))
  have hfun : f = fun q => (s ^ d) • (f ∘ A) q := by
    funext q
    have h := heatKernel_parabolic_scale hd hs q
    change heatKernel d q.1 q.2 = s ^ d * heatKernel d (s ^ 2 * q.1) (s • q.2)
    rw [h, inv_pow]
    field_simp
  have hderiv := A.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hAU.uniqueDiffOn hpU
    (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hAU hpU,
    iteratedFDerivWithin_of_isOpen n hU hpU] at hderiv
  change iteratedFDeriv ℝ n f p = (s ^ d) •
    ((iteratedFDeriv ℝ n f (A p)).compContinuousLinearMap fun _ => A)
  calc
    _ = iteratedFDeriv ℝ n (fun q => (s ^ d) • (f ∘ A) q) p := by rw [← hfun]
    _ = _ := by rw [iteratedFDeriv_const_smul_apply' hcomp, hderiv]

private lemma derivative_parabolic_bound {d n : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (p : ℝ × (Fin d → ℝ)) (hp : p.2 ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤
      ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) (scaleMap d s p)‖ := by
  rw [derivative_parabolic_scale hd hs p hp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hs.le _)]
  have hscale : ‖scaleMap d s‖ ≤ 1 := scaleMap_norm_le d hs.le hs1
  have hp1 : s ^ d ≤ 1 := pow_le_one₀ hs.le hs1
  have hnorm := (iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) =>
    heatKernel d q.1 q.2) (scaleMap d s p)).norm_compContinuousLinearMap_le
      (fun _ => scaleMap d s)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hnorm
  calc
    _ ≤ s ^ d * (‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) =>
      heatKernel d q.1 q.2) (scaleMap d s p)‖ * ‖scaleMap d s‖ ^ n) :=
      mul_le_mul_of_nonneg_left hnorm (pow_nonneg hs.le _)
    _ ≤ _ := by
      have hsN : ‖scaleMap d s‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hscale
      calc
        _ ≤ 1 * (‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) =>
          heatKernel d q.1 q.2) (scaleMap d s p)‖ * 1) := by
            gcongr
        _ = _ := by ring

/-- All derivatives of the heat kernel are bounded away from the spatial origin on bounded time intervals. -/
theorem iteratedFDeriv_heatKernel_bound (d n : ℕ) (ρ T : ℝ)
    (hd : 1 ≤ d) (hρ : 0 < ρ) (_hT : 0 < T) :
    ∃ C : ℝ, ∀ p : ℝ × (Fin d → ℝ), 0 < p.1 → p.1 ≤ T → ρ ≤ ‖p.2‖ →
      ‖iteratedFDeriv ℝ n (fun q : ℝ × (Fin d → ℝ) => heatKernel d q.1 q.2) p‖ ≤ C := by
  let K : Set (ℝ × (Fin d → ℝ)) := Metric.closedBall 0 (max T 1) ∩
    {p | min ρ 1 ≤ ‖p.2‖}
  have hKclosed : IsClosed {p : ℝ × (Fin d → ℝ) | min ρ 1 ≤ ‖p.2‖} :=
    isClosed_le continuous_const continuous_snd.norm
  have hK : IsCompact K := (isCompact_closedBall 0 (max T 1)).of_isClosed_subset
    (Metric.isClosed_closedBall.inter hKclosed) inter_subset_left
  have hKx : ∀ p ∈ K, p.2 ≠ 0 := by
    intro p hp heq
    have hm : 0 < min ρ 1 := lt_min hρ zero_lt_one
    have hx : min ρ 1 ≤ ‖p.2‖ := hp.2
    rw [heq, norm_zero] at hx
    linarith
  obtain ⟨C, hC⟩ := iteratedFDeriv_heatKernel_bdd_on_compact hd n hK hKx
  refine ⟨C, fun p ht htT hp => ?_⟩
  have hp0 : p.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hp
    linarith
  by_cases hx : ‖p.2‖ ≤ 1
  · have hpK : p ∈ K := by
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        apply max_le
        · rw [Real.norm_eq_abs, abs_of_nonneg ht.le]
          exact htT.trans (le_max_left _ _)
        · exact hx.trans (le_max_right _ _)
      · exact (min_le_left ρ 1).trans hp
    exact hC p hpK
  · have hx1 : 1 < ‖p.2‖ := lt_of_not_ge hx
    let s : ℝ := ‖p.2‖⁻¹
    have hs : 0 < s := inv_pos.mpr (by linarith)
    have hs1 : s ≤ 1 := by
      dsimp [s]
      exact inv_le_one_of_one_le₀ hx1.le
    have hy : ‖(scaleMap d s p).2‖ = 1 := by
      change ‖s • p.2‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      dsimp [s]
      exact inv_mul_cancel₀ (by linarith)
    have hyT : 0 ≤ (scaleMap d s p).1 ∧ (scaleMap d s p).1 ≤ T := by
      change 0 ≤ s ^ 2 * p.1 ∧ s ^ 2 * p.1 ≤ T
      constructor
      · positivity
      · have hs2 : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
        calc
          _ ≤ 1 * p.1 := mul_le_mul_of_nonneg_right hs2 ht.le
          _ ≤ T := by simpa using htT
    have hpK : scaleMap d s p ∈ K := by
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        apply max_le
        · rw [Real.norm_eq_abs, abs_of_nonneg hyT.1]
          exact hyT.2.trans (le_max_left _ _)
        · rw [hy]
          exact le_max_right _ _
      · change min ρ 1 ≤ ‖(scaleMap d s p).2‖
        rw [hy]
        exact min_le_right _ _
    exact (derivative_parabolic_bound hd hs hs1 p hp0).trans (hC _ hpK)

end LatticeProb.Heat
