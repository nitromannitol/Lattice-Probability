import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTDirectRel
import LatticeProb.Gauss.UncorrelatedIndependence
import LatticeProb.Prob.BrownianAbsMoments
import LatticeProb.Prob.BrownianSurvivalUpper
import LatticeProb.Prob.BoxCountingFinite

/-!
# Cone times of the correlated Brownian pair are countable for `γ ≤ √2`

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` of the mating-of-trees
encoding (`IsCorrelatedBM2 γ μ`), with correlation `ρ = lrCov γ 0 1 = -cos(πγ²/4)`. A **forward
cone time** is a time `s` with a forward direct `L`-partner and a forward direct `R`-partner (both
coordinates stay strictly above their values at `s` until they return to them); a **backward cone
time** is defined with backward partners. For `0 < γ ≤ √2` (that is `-1 < ρ ≤ 0`) both sets are
countable almost surely.

The proof is a box-counting argument. Fix a rational `r` and the direction `d = ±1`. Every cone
time `s` lies in a set `C(r)` of times such that both coordinates stay strictly above their values
at `s` between `s` and `r` (on `(s, r]` for `d = 1`, on `[r, s)` for `d = -1`). Partition an
interval `[p, q)` not containing `r` into `n` boxes of length `h`. If a box contains a point of
`C(r)`, then, at the end `c` of the box facing `r`, the future increments `L̃ v = L (c + d v) - L c`
and `R̃ v = R (c + d v) - R c` stay above `-Δ_L` and `-Δ_R` until time `T = d (r - c)`, where `Δ_L`,
`Δ_R` are the drops of `L`, `R` inside the box measured from `c`. Writing `R̃ = ρ L̃ + σ W̃` with
`σ = √(1 - ρ²)` and `W̃` a Brownian motion independent of `L̃`, the condition `ρ ≤ 0` gives
`σ W̃ ≥ -(Δ_R - ρ Δ_L)`. The drops are independent of the future increments, so two applications of
the survival bound `P (B ≥ -x on [0, T]) ≤ 3 x / √T` give
`μ E ≤ 9 E[Δ_L (Δ_R - ρ Δ_L)] / (σ T) ≤ C h`, using Lévy's reflection inequality for the second
moments of the drops. The box-counting criterion `LatticeProb.ae_finite_inter_Ico_of_box_bound`
then shows that `C(r) ∩ [p, q)` is finite almost surely.

## Main statements

* `LatticeProb.CorrelatedBM.measure_coneBoxEvent_le`: the bound `μ E ≤ C h / T` for the box event.
* `LatticeProb.CorrelatedBM.ae_countable_dirConeTimes`: `C(r)` is countable almost surely.
* `LatticeProb.CorrelatedBM.ae_countable_coneTimes_of_le_sqrt_two`: the forward and backward cone
  times are countable almost surely, for `0 < γ ≤ √2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-! ### The correlation for `γ ≤ √2` -/

/-- For `0 < γ ≤ √2` the correlation `ρ = lrCov γ 0 1 = -cos(πγ²/4)` of the pair lies in `(-1, 0]`. -/
theorem lrCov_zero_one_mem_Ioc {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2) :
    -1 < lrCov γ 0 1 ∧ lrCov γ 0 1 ≤ 0 := by
  have e : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := by simp [lrCov]
  have hx0 : 0 < Real.pi * γ ^ 2 / 4 := by positivity
  have hγ2 : γ ^ 2 ≤ 2 := by
    have h := mul_le_mul hγ hγ hγ0.le (Real.sqrt_nonneg 2)
    rw [Real.mul_self_sqrt (by norm_num)] at h
    nlinarith
  have hx1 : Real.pi * γ ^ 2 / 4 ≤ Real.pi / 2 := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hγ2)]
  have hcos : 0 ≤ Real.cos (Real.pi * γ ^ 2 / 4) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hx1
  have hsin : 0 < Real.sin (Real.pi * γ ^ 2 / 4) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hcos1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have h := Real.sin_sq_add_cos_sq (Real.pi * γ ^ 2 / 4)
    nlinarith [mul_pos hsin hsin]
  rw [e]
  exact ⟨by linarith, by linarith⟩

/-! ### Increments of the pair -/

/-- The increment `X x - X c` of the coordinate `i` of the pair (`X = L` for `i = 0`, `X = R` for
`i = 1`). -/
def coneIncr (i : Fin 2) (x c : ℝ) (ω : Path2) : ℝ := lrCoord i x ω - lrCoord i c ω

private lemma measurable_lrCoord_cone (i : Fin 2) (t : ℝ) :
    Measurable (fun ω : Path2 => lrCoord i t ω) := by
  unfold lrCoord
  split_ifs
  · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval t)

private lemma continuous_lrCoord_cone (i : Fin 2) (ω : Path2) :
    Continuous fun t => lrCoord i t ω := by
  by_cases hi : i = 0
  · subst hi
    simp only [lrCoord, ↓reduceIte]
    exact continuous_fst.comp ω.continuous
  · simp only [lrCoord, hi, ↓reduceIte]
    exact continuous_snd.comp ω.continuous

/-- The two-sided Brownian covariance kernel in terms of absolute values. -/
private lemma twoSidedMin_eq_abs_cone (x y : ℝ) :
    twoSidedMin x y = (|x| + |y| - |x - y|) / 2 := by
  unfold twoSidedMin
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [max_eq_left hx, max_eq_left hy, max_eq_right (neg_nonpos.2 hx),
      max_eq_right (neg_nonpos.2 hy), min_self, add_zero, abs_of_nonneg hx, abs_of_nonneg hy]
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]
      ring
  · rw [max_eq_left hx, max_eq_right hy, max_eq_right (neg_nonpos.2 hx),
      max_eq_left (neg_nonneg.2 hy), min_eq_right hx, min_eq_left (neg_nonneg.2 hy),
      abs_of_nonneg hx, abs_of_nonpos hy, abs_of_nonneg (by linarith : 0 ≤ x - y)]
    ring
  · rw [max_eq_right hx, max_eq_left hy, max_eq_left (neg_nonneg.2 hx),
      max_eq_right (neg_nonpos.2 hy), min_eq_left hy, min_eq_right (neg_nonneg.2 hx),
      abs_of_nonpos hx, abs_of_nonneg hy, abs_of_nonpos (by linarith : x - y ≤ 0)]
    ring
  · rw [max_eq_right hx, max_eq_right hy, max_eq_left (neg_nonneg.2 hx),
      max_eq_left (neg_nonneg.2 hy), min_self, zero_add, abs_of_nonpos hx, abs_of_nonpos hy]
    rcases le_total x y with h | h
    · rw [min_eq_right (neg_le_neg h), abs_of_nonpos (sub_nonpos.2 h)]
      ring
    · rw [min_eq_left (neg_le_neg h), abs_of_nonneg (sub_nonneg.2 h)]
      ring

theorem measurable_coneIncr (i : Fin 2) (x c : ℝ) : Measurable (coneIncr i x c) :=
  (measurable_lrCoord_cone i x).sub (measurable_lrCoord_cone i c)

private lemma continuous_coneIncr_affine (i : Fin 2) (c e : ℝ) (ω : Path2) :
    Continuous fun u : ℝ≥0 => coneIncr i (c + e * u) c ω :=
  ((continuous_lrCoord_cone i ω).comp
    (continuous_const.add (continuous_const.mul NNReal.continuous_coe))).sub continuous_const

theorem coneIncr_mem_span (i : Fin 2) (x c : ℝ) :
    coneIncr i x c ∈ Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) := by
  have e : coneIncr i x c = lrCoord i x - lrCoord i c := rfl
  rw [e]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨(i, x), rfl⟩)
    (Submodule.subset_span ⟨(i, c), rfl⟩)

/-- Covariance of two increments from the same time `c`:
`Cov(X x - X c, Y y - Y c) = lrCov γ i j (|x - c| + |y - c| - |x - y|) / 2`. -/
theorem cov_coneIncr {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (i j : Fin 2)
    (x y c : ℝ) :
    cov[coneIncr i x c, coneIncr j y c; μ] =
      lrCov γ i j * ((|x - c| + |y - c| - |x - y|) / 2) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 : ∀ (k : Fin 2) (t : ℝ), MemLp (lrCoord k t) 2 μ := fun k t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (k, t)).memLp_two
  change cov[fun ω => lrCoord i x ω - lrCoord i c ω, fun ω => lrCoord j y ω - lrCoord j c ω; μ] = _
  rw [covariance_fun_sub_fun_sub (hL2 i x) (hL2 i c) (hL2 j y) (hL2 j c),
    hμ.covariance_eq i j x y, hμ.covariance_eq i j x c, hμ.covariance_eq i j c y,
    hμ.covariance_eq i j c c]
  simp only [twoSidedMin_eq_abs_cone, sub_self, abs_zero]
  rw [abs_sub_comm c y]
  ring

/-! ### Linear combinations of the increments -/

/-- The combination `α (L x - L c) + β (R x - R c)` of the increments from time `c`. -/
def coneComb (α β x c : ℝ) (ω : Path2) : ℝ := α * coneIncr 0 x c ω + β * coneIncr 1 x c ω

theorem measurable_coneComb (α β x c : ℝ) : Measurable (coneComb α β x c) :=
  ((measurable_coneIncr 0 x c).const_mul α).add ((measurable_coneIncr 1 x c).const_mul β)

theorem continuous_coneComb_apply (α β c e : ℝ) (ω : Path2) :
    Continuous fun v : ℝ≥0 => coneComb α β (c + e * v) c ω :=
  (continuous_const.mul (continuous_coneIncr_affine 0 c e ω)).add
    (continuous_const.mul (continuous_coneIncr_affine 1 c e ω))

theorem coneComb_mem_span (α β x c : ℝ) :
    coneComb α β x c ∈ Submodule.span ℝ (Set.range fun p : Fin 2 × ℝ => lrCoord p.1 p.2) := by
  have e : coneComb α β x c = α • coneIncr 0 x c + β • coneIncr 1 x c := by
    funext ω
    simp [coneComb, smul_eq_mul]
  rw [e]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (coneIncr_mem_span 0 x c))
    (Submodule.smul_mem _ _ (coneIncr_mem_span 1 x c))

/-- Covariance of two combinations of increments from the same time `c`. -/
theorem cov_coneComb {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (α β α' β' x y c : ℝ) :
    cov[coneComb α β x c, coneComb α' β' y c; μ] =
      (α * α' + β * β' + (α * β' + β * α') * lrCov γ 0 1) *
        ((|x - c| + |y - c| - |x - y|) / 2) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 : ∀ (k : Fin 2) (t : ℝ), MemLp (lrCoord k t) 2 μ := fun k t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (k, t)).memLp_two
  have hI : ∀ (k : Fin 2) (t : ℝ), MemLp (coneIncr k t c) 2 μ := fun k t =>
    (hL2 k t).sub (hL2 k c)
  have e : ∀ a b t, coneComb a b t c =
      (fun ω => a * coneIncr 0 t c ω) + fun ω => b * coneIncr 1 t c ω := fun _ _ _ => rfl
  have h10 : lrCov γ 1 0 = lrCov γ 0 1 := by simp [lrCov]
  have h00 : lrCov γ 0 0 = 1 := by simp [lrCov]
  have h11 : lrCov γ 1 1 = 1 := by simp [lrCov]
  rw [e α β x, e α' β' y,
    covariance_add_left ((hI 0 x).const_mul α) ((hI 1 x).const_mul β)
      (((hI 0 y).const_mul α').add ((hI 1 y).const_mul β')),
    covariance_add_right ((hI 0 x).const_mul α) ((hI 0 y).const_mul α') ((hI 1 y).const_mul β'),
    covariance_add_right ((hI 1 x).const_mul β) ((hI 0 y).const_mul α') ((hI 1 y).const_mul β')]
  simp only [covariance_const_mul_left, covariance_const_mul_right, cov_coneIncr hμ, h10, h00, h11]
  ring

/-- **Brownian combinations.** If `|e| = 1` and `α² + β² + 2 α β ρ = 1`, the combination
`v ↦ α (L (c + e v) - L c) + β (R (c + e v) - R c)` is a standard Brownian motion. -/
theorem isBrownianReal_coneComb {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {α β e : ℝ} (he : |e| = 1) (hαβ : α * α + β * β + (α * β + β * α) * lrCov γ 0 1 = 1)
    (c : ℝ) : IsBrownianReal (fun v : ℝ≥0 => coneComb α β (c + e * v) c) μ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 : ∀ (k : Fin 2) (t : ℝ), MemLp (lrCoord k t) 2 μ := fun k t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (k, t)).memLp_two
  have hGP : IsGaussianProcess (fun v : ℝ≥0 => coneComb α β (c + e * v) c) μ :=
    GaussIndep.isGaussianProcess_of_mem_span hμ.isGaussianProcess fun v => coneComb_mem_span _ _ _ _
  have hmean : ∀ v : ℝ≥0, ∫ ω, coneComb α β (c + e * v) c ω ∂μ = 0 := by
    intro v
    have hint : ∀ (k : Fin 2) (t : ℝ), Integrable (lrCoord k t) μ := fun k t =>
      (hL2 k t).integrable (by norm_num)
    have i0 : Integrable (fun ω => α * (lrCoord 0 (c + e * v) ω - lrCoord 0 c ω)) μ :=
      ((hint 0 _).sub (hint 0 c)).const_mul α
    have i1 : Integrable (fun ω => β * (lrCoord 1 (c + e * v) ω - lrCoord 1 c ω)) μ :=
      ((hint 1 _).sub (hint 1 c)).const_mul β
    simp only [coneComb, coneIncr]
    rw [integral_add i0 i1, integral_const_mul, integral_const_mul,
      integral_sub (hint 0 _) (hint 0 c), integral_sub (hint 1 _) (hint 1 c),
      hμ.integral_eq_zero 0 (c + e * v), hμ.integral_eq_zero 0 c,
      hμ.integral_eq_zero 1 (c + e * v), hμ.integral_eq_zero 1 c]
    ring
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[coneComb α β (c + e * s) c, coneComb α β (c + e * t) c; μ] = s := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := NNReal.coe_le_coe.2 hst
    have hK : (|c + e * (s : ℝ) - c| + |c + e * (t : ℝ) - c| - |c + e * (s : ℝ) - (c + e * t)|) / 2
        = s := by
      rw [show c + e * (s : ℝ) - c = e * s by ring, show c + e * (t : ℝ) - c = e * t by ring,
        show c + e * (s : ℝ) - (c + e * t) = e * (s - t) by ring, abs_mul, abs_mul, abs_mul, he,
        abs_of_nonneg (NNReal.coe_nonneg s), abs_of_nonneg (NNReal.coe_nonneg t),
        abs_of_nonpos (sub_nonpos.2 hst')]
      ring
    rw [cov_coneComb hμ, hαβ, one_mul, hK]
  refine ⟨hGP.isPreBrownianReal_of_covariance hmean hcov, ae_of_all _ fun ω => ?_⟩
  exact continuous_coneComb_apply α β c e ω

/-- The negated increment `u ↦ -(X (c + e u) - X c)` of either coordinate is a standard Brownian
motion when `|e| = 1`. -/
theorem isBrownianReal_neg_coneIncr {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {e : ℝ} (he : |e| = 1) (c : ℝ) :
    IsBrownianReal (fun u : ℝ≥0 => fun ω => -coneIncr i (c + e * u) c ω) μ := by
  revert i
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · have h := isBrownianReal_coneComb hμ (α := -1) (β := 0) he (by ring) c
    have hfun : (fun v : ℝ≥0 => coneComb (-1) 0 (c + e * v) c) =
        fun u : ℝ≥0 => fun ω => -coneIncr 0 (c + e * u) c ω := by
      funext u ω
      simp only [coneComb]
      ring
    rwa [hfun] at h
  · have h := isBrownianReal_coneComb hμ (α := 0) (β := -1) he (by ring) c
    have hfun : (fun v : ℝ≥0 => coneComb 0 (-1) (c + e * v) c) =
        fun u : ℝ≥0 => fun ω => -coneIncr 1 (c + e * u) c ω := by
      funext u ω
      simp only [coneComb]
      ring
    rwa [hfun] at h

/-! ### Rational times and the survival and second-moment bounds -/

/-- The rational time `q` clamped to `[0, h]`, as a nonnegative real. -/
def ratClamp (h : ℝ) (q : ℚ) : ℝ≥0 := Real.toNNReal (min (q : ℝ) h)

theorem ratClamp_le {h : ℝ} (hh : 0 ≤ h) (q : ℚ) : (ratClamp h q : ℝ) ≤ h := by
  simp only [ratClamp, Real.coe_toNNReal', max_le_iff]
  exact ⟨min_le_right _ _, hh⟩

theorem ratClamp_zero (h : ℝ) : ratClamp h 0 = 0 := by
  rw [ratClamp, Rat.cast_zero]
  exact Real.toNNReal_of_nonpos (min_le_left _ _)

/-- A continuous function of time which takes values in a closed set at the rational times clamped
to `[0, T]` takes values in that set on `[0, T]`. -/
theorem mem_of_forall_rat_clamp {f : ℝ≥0 → ℝ} (hf : Continuous f) {S : Set ℝ} (hS : IsClosed S)
    {T : ℝ} (h : ∀ q : ℚ, f (Real.toNNReal (min (q : ℝ) T)) ∈ S) {s : ℝ≥0} (hs : (s : ℝ) ≤ T) :
    f s ∈ S := by
  have hg : Continuous fun x : ℝ => f (Real.toNNReal (min x T)) :=
    hf.comp (continuous_real_toNNReal.comp (continuous_id.min continuous_const))
  have hall : ∀ x : ℝ, f (Real.toNNReal (min x T)) ∈ S := fun x =>
    Rat.denseRange_cast.induction_on x (hS.preimage hg) h
  have := hall (s : ℝ)
  rwa [min_eq_left hs, Real.toNNReal_coe] at this

/-- **Survival bound at rational times.** For a Brownian motion `B` with `B 0 = 0` and continuous
paths, the probability that `B ≥ -x` at all rational times clamped to `[0, T]` is at most
`3 x / √T`. -/
theorem measure_forall_rat_ge_neg_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) (hcont : ∀ ω, Continuous fun t => B t ω)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    P {ω | ∀ q : ℚ, -x ≤ B (ratClamp T q) ω} ≤ ENNReal.ofReal (3 * x / Real.sqrt T) := by
  by_cases hx : 0 ≤ x
  · have hT' : (0 : ℝ≥0) < T.toNNReal := Real.toNNReal_pos.2 hT
    calc P {ω | ∀ q : ℚ, -x ≤ B (ratClamp T q) ω}
        ≤ P {ω | ∀ s ≤ T.toNNReal, -x ≤ B s ω - B 0 ω} := by
          refine measure_mono fun ω hω s hs => ?_
          rw [hB0, sub_zero]
          have hs' : (s : ℝ) ≤ T := by
            have := NNReal.coe_le_coe.2 hs
            rwa [Real.coe_toNNReal _ hT.le] at this
          exact mem_of_forall_rat_clamp (hcont ω) (S := Set.Ici (-x)) (T := T) isClosed_Ici hω hs'
      _ ≤ ENNReal.ofReal (3 * x / Real.sqrt (T.toNNReal : ℝ)) :=
          measure_forall_ge_neg_le hB hm hT' hx
      _ = ENNReal.ofReal (3 * x / Real.sqrt T) := by rw [Real.coe_toNNReal _ hT.le]
  · calc P {ω | ∀ q : ℚ, -x ≤ B (ratClamp T q) ω} ≤ P ∅ := by
          refine measure_mono fun ω hω => ?_
          have h0 := hω 0
          rw [ratClamp_zero, hB0] at h0
          exact absurd h0 (not_le.2 (by linarith [not_le.1 hx]))
      _ = 0 := measure_empty
      _ ≤ _ := bot_le

/-- **Second moment of a running maximum.** Let `B` be a Brownian motion with `B 0 = 0` and let
`M ≥ 0` be such that `t < M` forces `B s > t` for some `s ≤ T`. Then
`E[M²] ≤ 2 E|B T|² = 2 g₂ T`, with `g₂ = gaussianAbsMoment 2`, by the layer-cake formula and Lévy's
reflection inequality. -/
theorem lintegral_sq_le_of_lt_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) (T : ℝ≥0) {M : Ω → ℝ}
    (hM0 : ∀ ω, 0 ≤ M ω) (hMm : Measurable M)
    (hMlt : ∀ ω (t : ℝ), 0 < t → t < M ω → ∃ s ≤ T, t < B s ω - B 0 ω) :
    ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂P ≤ 2 * ENNReal.ofReal (gaussianAbsMoment 2 * T) := by
  set X : Ω → ℝ := fun ω => max (B T ω) 0 with hX
  have hXm : Measurable X := (hm T).max measurable_const
  have hp := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := P) (ae_of_all _ fun ω => hM0 ω)
    hMm.aemeasurable (p := 2) two_pos
  have hq := lintegral_rpow_eq_lintegral_meas_le_mul (μ := P)
    (ae_of_all _ fun ω => le_max_right (B T ω) 0) hXm.aemeasurable (p := 2) two_pos
  simp only [Real.rpow_two] at hp hq
  have htail : ∀ t : ℝ, 0 < t → P {a | t < M a} ≤ 2 * P {a | t ≤ X a} := by
    intro t ht
    calc P {a | t < M a} ≤ P {ω | ∃ s ≤ T, t < B s ω - B 0 ω} :=
          measure_mono fun ω hω => hMlt ω t ht hω
      _ ≤ 2 * P {ω | t ≤ B T ω - B 0 ω} := measure_exists_lt_le_two_mul hB hm T t
      _ = 2 * P {a | t ≤ X a} := by
          congr 2
          ext ω
          simp only [Set.mem_ofPred_eq, hB0, sub_zero, hX, le_max_iff]
          exact ⟨Or.inl, fun h => h.resolve_right (not_le.2 ht)⟩
  have hint : Integrable (fun ω => |B T ω| ^ 2) P :=
    brownian_integrable_abs_pow hB.toIsPreBrownianReal T 2
  calc ∫⁻ ω, ENNReal.ofReal (M ω ^ 2) ∂P
      = ENNReal.ofReal 2 * ∫⁻ t in Ioi 0, P {a | t < M a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1)) :=
        hp
    _ ≤ ENNReal.ofReal 2 *
          ∫⁻ t in Ioi 0, 2 * (P {a | t ≤ X a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        rw [← mul_assoc]
        exact mul_le_mul' (htail t ht) le_rfl
    _ = 2 * (ENNReal.ofReal 2 *
          ∫⁻ t in Ioi 0, P {a | t ≤ X a} * ENNReal.ofReal (t ^ ((2 : ℝ) - 1))) := by
        rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
        ring
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P := by rw [hq]
    _ ≤ 2 * ∫⁻ ω, ENNReal.ofReal (|B T ω| ^ 2) ∂P := by
        refine mul_le_mul' le_rfl (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
        have h1 : 0 ≤ X ω := le_max_right _ _
        have h2 : X ω ≤ |B T ω| := max_le (le_abs_self _) (abs_nonneg _)
        nlinarith
    _ = 2 * ENNReal.ofReal (∫ ω, |B T ω| ^ 2 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
    _ = 2 * ENNReal.ofReal (gaussianAbsMoment 2 * T) := by
        rw [brownian_integral_abs_pow_eq hB.toIsPreBrownianReal T 2]
        norm_num

/-! ### Drops inside a box -/

/-- The drop `sup_{u ∈ [0, h]} (X c - X (c + e u))` of the coordinate `i` inside the box of length
`h` next to `c` (on the side of `e`), read at the clamped rational times. -/
def pastDrop (i : Fin 2) (e c h : ℝ) (ω : Path2) : ℝ :=
  ⨆ q : ℚ, -coneIncr i (c + e * ratClamp h q) c ω

theorem measurable_pastDrop (i : Fin 2) (e c h : ℝ) : Measurable (pastDrop i e c h) := by
  show Measurable fun ω => ⨆ q : ℚ, -coneIncr i (c + e * ratClamp h q) c ω
  exact Measurable.iSup fun q => (measurable_coneIncr i _ c).neg

theorem bddAbove_pastDrop (i : Fin 2) (e c h : ℝ) (ω : Path2) :
    BddAbove (Set.range fun q : ℚ => -coneIncr i (c + e * ratClamp h q) c ω) := by
  refine ((isCompact_Icc (a := (0 : ℝ≥0)) (b := h.toNNReal)).image
    (continuous_coneIncr_affine i c e ω).neg).bddAbove.mono ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨ratClamp h q, ⟨(ratClamp h q).2, Real.toNNReal_le_toNNReal (min_le_right _ _)⟩, rfl⟩

theorem pastDrop_nonneg (i : Fin 2) (e c h : ℝ) (ω : Path2) : 0 ≤ pastDrop i e c h ω := by
  have h0 : -coneIncr i (c + e * ratClamp h 0) c ω = 0 := by
    rw [ratClamp_zero]
    simp [coneIncr]
  calc (0 : ℝ) = -coneIncr i (c + e * ratClamp h 0) c ω := h0.symm
    _ ≤ pastDrop i e c h ω := le_ciSup (bddAbove_pastDrop i e c h ω) (0 : ℚ)

/-- The drop dominates `X c - X (c + e u)` for every real `u ∈ [0, h]`. -/
theorem neg_coneIncr_le_pastDrop (i : Fin 2) (e c h : ℝ) (ω : Path2) {u : ℝ≥0}
    (hu : (u : ℝ) ≤ h) : -coneIncr i (c + e * u) c ω ≤ pastDrop i e c h ω :=
  mem_of_forall_rat_clamp (continuous_coneIncr_affine i c e ω).neg
    (S := Set.Iic (pastDrop i e c h ω)) (T := h) isClosed_Iic
    (fun q => le_ciSup (bddAbove_pastDrop i e c h ω) q) hu

/-- **Second moment of the drop.** `E[Δ²] ≤ 2 g₂ h` for the drop over a box of length `h`. -/
theorem lintegral_pastDrop_sq_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) {e : ℝ} (he : |e| = 1) (c : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ ω, ENNReal.ofReal (pastDrop i e c h ω ^ 2) ∂μ ≤
      2 * ENNReal.ofReal (gaussianAbsMoment 2 * h) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hMlt : ∀ ω (t : ℝ), 0 < t → t < pastDrop i e c h ω →
      ∃ s ≤ h.toNNReal, t < -coneIncr i (c + e * s) c ω -
        -coneIncr i (c + e * ((0 : ℝ≥0) : ℝ)) c ω := by
    intro ω t _ hlt
    obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup hlt
    refine ⟨ratClamp h q, Real.toNNReal_le_toNNReal (min_le_right _ _), ?_⟩
    have h0 : coneIncr i (c + e * ((0 : ℝ≥0) : ℝ)) c ω = 0 := by simp [coneIncr]
    rw [h0, neg_zero, sub_zero]
    exact hq
  have key := lintegral_sq_le_of_lt_exists
    (B := fun u : ℝ≥0 => fun ω => -coneIncr i (c + e * u) c ω)
    (isBrownianReal_neg_coneIncr hμ i he c) (fun u => (measurable_coneIncr i _ c).neg)
    (fun ω => by simp [coneIncr]) h.toNNReal (pastDrop_nonneg i e c h)
    (measurable_pastDrop i e c h) hMlt
  rwa [Real.coe_toNNReal _ hh] at key

/-! ### The box event -/

/-- The increments inside the box, from its end `c`, at the clamped rational times. -/
def conePast (d c h : ℝ) (ω : Path2) : Fin 2 × ℚ → ℝ :=
  fun s => coneIncr s.1 (c + -d * (ratClamp h s.2 : ℝ)) c ω

/-- The future increments `(X (c + d v) - X c)` after the end `c` of the box. -/
def coneFuture (d c : ℝ) (ω : Path2) : Fin 2 × ℝ≥0 → ℝ :=
  fun t => coneIncr t.1 (c + d * (t.2 : ℝ)) c ω

/-- The two drops read off the increments inside the box. -/
def dropsOf (f : Fin 2 × ℚ → ℝ) : ℝ × ℝ := (⨆ q : ℚ, -f (0, q), ⨆ q : ℚ, -f (1, q))

/-- The pairs (drops, future increments) such that `L̃ ≥ -Δ_L` and `R̃ - ρ L̃ ≥ -(Δ_R - ρ Δ_L)` at
the clamped rational times. -/
def coneFutureSet (ρ T : ℝ) : Set ((ℝ × ℝ) × (Fin 2 × ℝ≥0 → ℝ)) :=
  {z | ∀ q : ℚ, -z.1.1 ≤ z.2 (0, ratClamp T q) ∧
    -(z.1.2 - ρ * z.1.1) ≤ z.2 (1, ratClamp T q) - ρ * z.2 (0, ratClamp T q)}

/-- **The box event** of the box of length `h` with end `c` facing the direction `d`, with horizon
`T`. -/
def coneBoxEvent (ρ d c h T : ℝ) : Set Path2 :=
  (fun ω => (dropsOf (conePast d c h ω), coneFuture d c ω)) ⁻¹' coneFutureSet ρ T

theorem measurable_conePast (d c h : ℝ) : Measurable (conePast d c h) :=
  measurable_pi_iff.2 fun s : Fin 2 × ℚ =>
    measurable_coneIncr s.1 (c + -d * (ratClamp h s.2 : ℝ)) c

theorem measurable_coneFuture (d c : ℝ) : Measurable (coneFuture d c) :=
  measurable_pi_iff.2 fun t : Fin 2 × ℝ≥0 => measurable_coneIncr t.1 (c + d * (t.2 : ℝ)) c

theorem measurable_dropsOf : Measurable dropsOf := by
  have h0 : Measurable fun f : Fin 2 × ℚ → ℝ => ⨆ q : ℚ, -f (0, q) :=
    Measurable.iSup fun q => (measurable_pi_apply (0, q)).neg
  have h1 : Measurable fun f : Fin 2 × ℚ → ℝ => ⨆ q : ℚ, -f (1, q) :=
    Measurable.iSup fun q => (measurable_pi_apply (1, q)).neg
  exact h0.prodMk h1

theorem measurableSet_coneFutureSet (ρ T : ℝ) : MeasurableSet (coneFutureSet ρ T) := by
  have h0 : ∀ v : ℝ≥0, Measurable fun z : (ℝ × ℝ) × (Fin 2 × ℝ≥0 → ℝ) => z.2 (0, v) := fun v =>
    (measurable_pi_apply (0, v)).comp measurable_snd
  have h1 : ∀ v : ℝ≥0, Measurable fun z : (ℝ × ℝ) × (Fin 2 × ℝ≥0 → ℝ) => z.2 (1, v) := fun v =>
    (measurable_pi_apply (1, v)).comp measurable_snd
  have hx1 : Measurable fun z : (ℝ × ℝ) × (Fin 2 × ℝ≥0 → ℝ) => z.1.1 :=
    measurable_fst.comp measurable_fst
  have hx2 : Measurable fun z : (ℝ × ℝ) × (Fin 2 × ℝ≥0 → ℝ) => z.1.2 :=
    measurable_snd.comp measurable_fst
  simp only [coneFutureSet, Set.ofPred_forall, Set.ofPred_and]
  exact MeasurableSet.iInter fun q => (measurableSet_le hx1.neg (h0 _)).inter
    (measurableSet_le (hx2.sub (hx1.const_mul ρ)).neg ((h1 _).sub ((h0 _).const_mul ρ)))

theorem measurableSet_coneBoxEvent (ρ d c h T : ℝ) : MeasurableSet (coneBoxEvent ρ d c h T) :=
  ((measurable_dropsOf.comp (measurable_conePast d c h)).prodMk (measurable_coneFuture d c))
    (measurableSet_coneFutureSet ρ T)

/-- The increments inside the box are independent of the future increments. -/
theorem indepFun_conePast_coneFuture {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {d : ℝ} (hd : |d| = 1) (c h : ℝ) : IndepFun (conePast d c h) (coneFuture d c) μ := by
  refine GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := fun s : Fin 2 × ℚ => coneIncr s.1 (c + -d * (ratClamp h s.2 : ℝ)) c)
    (B := fun t : Fin 2 × ℝ≥0 => coneIncr t.1 (c + d * (t.2 : ℝ)) c)
    (fun s => coneIncr_mem_span _ _ _) (fun t => coneIncr_mem_span _ _ _) fun s t => ?_
  rw [cov_coneIncr hμ]
  have hu := NNReal.coe_nonneg (ratClamp h s.2)
  have hv := NNReal.coe_nonneg t.2
  have e1 : |c + -d * (ratClamp h s.2 : ℝ) - c| = ratClamp h s.2 := by
    rw [show c + -d * (ratClamp h s.2 : ℝ) - c = -d * ratClamp h s.2 by ring, abs_mul, abs_neg,
      hd, one_mul, abs_of_nonneg hu]
  have e2 : |c + d * (t.2 : ℝ) - c| = t.2 := by
    rw [show c + d * (t.2 : ℝ) - c = d * t.2 by ring, abs_mul, hd, one_mul, abs_of_nonneg hv]
  have e3 : |c + -d * (ratClamp h s.2 : ℝ) - (c + d * t.2)| = ratClamp h s.2 + t.2 := by
    rw [show c + -d * (ratClamp h s.2 : ℝ) - (c + d * t.2) = -d * (ratClamp h s.2 + t.2) by ring,
      abs_mul, abs_neg, hd, one_mul, abs_of_nonneg (add_nonneg hu hv)]
  rw [e1, e2, e3]
  ring

/-- The future increment of `L` and the whitened future increment `W̃ = (R̃ - ρ L̃) / σ` are
independent. -/
theorem indepFun_coneComb_future {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (d c σ : ℝ) :
    IndepFun (fun ω (v : ℝ≥0) => coneComb 1 0 (c + d * v) c ω)
      (fun ω (v : ℝ≥0) => coneComb (-lrCov γ 0 1 / σ) (1 / σ) (c + d * v) c ω) μ := by
  refine GaussIndep.indepFun_of_mem_span_of_covariance_eq_zero hμ.isGaussianProcess
    (A := fun v : ℝ≥0 => coneComb 1 0 (c + d * v) c)
    (B := fun v : ℝ≥0 => coneComb (-lrCov γ 0 1 / σ) (1 / σ) (c + d * v) c)
    (fun v => coneComb_mem_span _ _ _ _) (fun v => coneComb_mem_span _ _ _ _) fun s t => ?_
  rw [cov_coneComb hμ]
  ring

/-- `3 x / √T · 3 ((y - ρ x) / σ) / √T ≤ 18 (x² + y²) / (σ T)` for `-1 ≤ ρ`. -/
private lemma prod_bound_aux {x y ρ σ T : ℝ} (hρ1 : -1 ≤ ρ) (hσ : 0 < σ) (hT : 0 < T) :
    3 * x / Real.sqrt T * (3 * ((y - ρ * x) / σ) / Real.sqrt T) ≤
      18 / (σ * T) * (x ^ 2 + y ^ 2) := by
  have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have key : x * (y - ρ * x) ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y), mul_nonneg (show (0 : ℝ) ≤ 1 + ρ by linarith) (sq_nonneg x),
      sq_nonneg x, sq_nonneg y]
  rw [div_mul_div_comm, hss]
  have e : 3 * x * (3 * ((y - ρ * x) / σ)) / T = 9 / (σ * T) * (x * (y - ρ * x)) := by ring
  rw [e]
  have h9 : 0 ≤ 9 / (σ * T) := div_nonneg (by norm_num) (mul_pos hσ hT).le
  calc 9 / (σ * T) * (x * (y - ρ * x)) ≤ 9 / (σ * T) * (2 * (x ^ 2 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left key h9
    _ = 18 / (σ * T) * (x ^ 2 + y ^ 2) := by ring

/-- **The box bound.** For `-1 < ρ ≤ 0`, `|d| = 1`, a box of length `h ≥ 0` and a horizon `T > 0`,
`μ E ≤ 18 / (σ T) · 4 g₂ h` with `σ = √(1 - ρ²)` and `g₂ = gaussianAbsMoment 2`. -/
theorem measure_coneBoxEvent_le {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (hρ0 : lrCov γ 0 1 ≤ 0) (hρ1 : -1 < lrCov γ 0 1) {d : ℝ} (hd : |d| = 1) (c : ℝ) {h T : ℝ}
    (hh : 0 ≤ h) (hT : 0 < T) :
    μ (coneBoxEvent (lrCov γ 0 1) d c h T) ≤
      ENNReal.ofReal (18 / (Real.sqrt (1 - lrCov γ 0 1 ^ 2) * T)) *
        (4 * ENNReal.ofReal (gaussianAbsMoment 2 * h)) := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  set ρ := lrCov γ 0 1
  set σ := Real.sqrt (1 - ρ ^ 2)
  have h1ρ : 0 < 1 - ρ ^ 2 := by
    nlinarith [mul_pos (show 0 < ρ + 1 by linarith) (show 0 < 1 - ρ by linarith)]
  have hσ0 : 0 < σ := Real.sqrt_pos.2 h1ρ
  have hσ2 : σ * σ = 1 - ρ ^ 2 := Real.mul_self_sqrt h1ρ.le
  have hnd : |-d| = 1 := by rw [abs_neg, hd]
  have hDm : Measurable fun ω => dropsOf (conePast d c h ω) :=
    measurable_dropsOf.comp (measurable_conePast d c h)
  have hFm : Measurable (coneFuture d c) := measurable_coneFuture d c
  have hind : IndepFun (fun ω => dropsOf (conePast d c h ω)) (coneFuture d c) μ :=
    (indepFun_conePast_coneFuture hμ hd c h).comp measurable_dropsOf measurable_id
  have hG := measurableSet_coneFutureSet ρ T
  have hZ : Measurable fun ω => (dropsOf (conePast d c h ω), coneFuture d c ω) := hDm.prodMk hFm
  have hmap : μ.map (fun ω => (dropsOf (conePast d c h ω), coneFuture d c ω)) =
      (μ.map fun ω => dropsOf (conePast d c h ω)).prod (μ.map (coneFuture d c)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hDm.aemeasurable hFm.aemeasurable).1 hind
  -- the two Brownian motions of the future
  have hαβW : -ρ / σ * (-ρ / σ) + 1 / σ * (1 / σ) + (-ρ / σ * (1 / σ) + 1 / σ * (-ρ / σ)) * ρ
      = 1 := by
    rw [show -ρ / σ * (-ρ / σ) + 1 / σ * (1 / σ) + (-ρ / σ * (1 / σ) + 1 / σ * (-ρ / σ)) * ρ
        = (1 - ρ ^ 2) / (σ * σ) by ring, ← hσ2]
    exact div_self (mul_pos hσ0 hσ0).ne'
  have hBL := isBrownianReal_coneComb hμ (α := 1) (β := 0) hd (by ring) c
  have hBW := isBrownianReal_coneComb hμ (α := -ρ / σ) (β := 1 / σ) hd hαβW c
  have hindLW := indepFun_coneComb_future hμ d c σ
  -- the bound on the sections
  have hsec : ∀ x : ℝ × ℝ, μ.map (coneFuture d c) (Prod.mk x ⁻¹' coneFutureSet ρ T) ≤
      ENNReal.ofReal (3 * x.1 / Real.sqrt T) *
        ENNReal.ofReal (3 * ((x.2 - ρ * x.1) / σ) / Real.sqrt T) := by
    intro x
    rw [Measure.map_apply hFm (hG.preimage measurable_prodMk_left)]
    have hSL : MeasurableSet {f : ℝ≥0 → ℝ | ∀ q : ℚ, -x.1 ≤ f (ratClamp T q)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun q => measurableSet_le measurable_const (measurable_pi_apply _)
    have hSW : MeasurableSet
        {f : ℝ≥0 → ℝ | ∀ q : ℚ, -((x.2 - ρ * x.1) / σ) ≤ f (ratClamp T q)} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun q => measurableSet_le measurable_const (measurable_pi_apply _)
    have hsub : coneFuture d c ⁻¹' (Prod.mk x ⁻¹' coneFutureSet ρ T) ⊆
        (fun ω (v : ℝ≥0) => coneComb 1 0 (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -x.1 ≤ f (ratClamp T q)} ∩
          (fun ω (v : ℝ≥0) => coneComb (-ρ / σ) (1 / σ) (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -((x.2 - ρ * x.1) / σ) ≤ f (ratClamp T q)} := by
      intro ω hω
      have hω' : ∀ q : ℚ, -x.1 ≤ coneIncr 0 (c + d * ratClamp T q) c ω ∧
          -(x.2 - ρ * x.1) ≤ coneIncr 1 (c + d * ratClamp T q) c ω -
            ρ * coneIncr 0 (c + d * ratClamp T q) c ω := hω
      refine ⟨show ∀ q : ℚ, -x.1 ≤ coneComb 1 0 (c + d * ratClamp T q) c ω from fun q => ?_,
        show ∀ q : ℚ, -((x.2 - ρ * x.1) / σ) ≤ coneComb (-ρ / σ) (1 / σ) (c + d * ratClamp T q) c ω
          from fun q => ?_⟩
      · simp only [coneComb, one_mul, zero_mul, add_zero]
        exact (hω' q).1
      · have e : coneComb (-ρ / σ) (1 / σ) (c + d * ratClamp T q) c ω =
            (coneIncr 1 (c + d * ratClamp T q) c ω - ρ * coneIncr 0 (c + d * ratClamp T q) c ω) /
              σ := by
          simp only [coneComb]
          ring
        rw [e, ← neg_div]
        exact (div_le_div_iff_of_pos_right hσ0).2 (hω' q).2
    calc μ (coneFuture d c ⁻¹' (Prod.mk x ⁻¹' coneFutureSet ρ T))
        ≤ μ ((fun ω (v : ℝ≥0) => coneComb 1 0 (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -x.1 ≤ f (ratClamp T q)} ∩
          (fun ω (v : ℝ≥0) => coneComb (-ρ / σ) (1 / σ) (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -((x.2 - ρ * x.1) / σ) ≤ f (ratClamp T q)}) :=
          measure_mono hsub
      _ = μ ((fun ω (v : ℝ≥0) => coneComb 1 0 (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -x.1 ≤ f (ratClamp T q)}) *
          μ ((fun ω (v : ℝ≥0) => coneComb (-ρ / σ) (1 / σ) (c + d * v) c ω) ⁻¹'
            {f : ℝ≥0 → ℝ | ∀ q : ℚ, -((x.2 - ρ * x.1) / σ) ≤ f (ratClamp T q)}) :=
          (indepFun_iff_measure_inter_preimage_eq_mul.1 hindLW) _ _ hSL hSW
      _ ≤ _ := mul_le_mul'
          (measure_forall_rat_ge_neg_le hBL (fun v => measurable_coneComb _ _ _ _)
            (fun ω => by simp [coneComb, coneIncr]) (fun ω => continuous_coneComb_apply _ _ _ _ ω)
            hT x.1)
          (measure_forall_rat_ge_neg_le hBW (fun v => measurable_coneComb _ _ _ _)
            (fun ω => by simp [coneComb, coneIncr]) (fun ω => continuous_coneComb_apply _ _ _ _ ω)
            hT ((x.2 - ρ * x.1) / σ))
  have hfm : Measurable fun x : ℝ × ℝ => ENNReal.ofReal (3 * x.1 / Real.sqrt T) *
      ENNReal.ofReal (3 * ((x.2 - ρ * x.1) / σ) / Real.sqrt T) :=
    (Measurable.ennreal_ofReal (by fun_prop)).mul (Measurable.ennreal_ofReal (by fun_prop))
  have hm0 : Measurable fun ω => ENNReal.ofReal (pastDrop 0 (-d) c h ω ^ 2) :=
    ((measurable_pastDrop 0 (-d) c h).pow_const 2).ennreal_ofReal
  calc μ (coneBoxEvent ρ d c h T)
      = μ.map (fun ω => (dropsOf (conePast d c h ω), coneFuture d c ω)) (coneFutureSet ρ T) :=
        (Measure.map_apply hZ hG).symm
    _ = ∫⁻ x, μ.map (coneFuture d c) (Prod.mk x ⁻¹' coneFutureSet ρ T)
          ∂(μ.map fun ω => dropsOf (conePast d c h ω)) := by
        rw [hmap, Measure.prod_apply hG]
    _ ≤ ∫⁻ x, ENNReal.ofReal (3 * x.1 / Real.sqrt T) *
          ENNReal.ofReal (3 * ((x.2 - ρ * x.1) / σ) / Real.sqrt T)
          ∂(μ.map fun ω => dropsOf (conePast d c h ω)) := lintegral_mono fun x => hsec x
    _ = ∫⁻ ω, ENNReal.ofReal (3 * pastDrop 0 (-d) c h ω / Real.sqrt T) *
          ENNReal.ofReal (3 * ((pastDrop 1 (-d) c h ω - ρ * pastDrop 0 (-d) c h ω) / σ) /
            Real.sqrt T) ∂μ := lintegral_map hfm hDm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (18 / (σ * T) *
          (pastDrop 0 (-d) c h ω ^ 2 + pastDrop 1 (-d) c h ω ^ 2)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        have h0 := pastDrop_nonneg 0 (-d) c h ω
        rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by norm_num) h0) (Real.sqrt_nonneg _))]
        exact ENNReal.ofReal_le_ofReal (prod_bound_aux hρ1.le hσ0 hT)
    _ = ENNReal.ofReal (18 / (σ * T)) * (∫⁻ ω, ENNReal.ofReal (pastDrop 0 (-d) c h ω ^ 2) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (pastDrop 1 (-d) c h ω ^ 2) ∂μ) := by
        rw [← lintegral_add_left hm0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul (div_nonneg (by norm_num) (mul_pos hσ0 hT).le),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ ≤ ENNReal.ofReal (18 / (σ * T)) * (2 * ENNReal.ofReal (gaussianAbsMoment 2 * h) +
          2 * ENNReal.ofReal (gaussianAbsMoment 2 * h)) :=
        mul_le_mul' le_rfl (add_le_add (lintegral_pastDrop_sq_le hμ 0 hnd c hh)
          (lintegral_pastDrop_sq_le hμ 1 hnd c hh))
    _ = ENNReal.ofReal (18 / (σ * T)) * (4 * ENNReal.ofReal (gaussianAbsMoment 2 * h)) := by
        ring

/-! ### Times beyond which both coordinates stay above -/

/-- The times `s` such that both coordinates stay strictly above their values at `s` between `s`
and `r`, in the direction `d` (`d = 1`: on `(s, r]`; `d = -1`: on `[r, s)`). -/
def dirConeTimes (d r : ℝ) (ω : Path2) : Set ℝ :=
  {s | d * s < d * r ∧ ∀ u, d * s < d * u → d * u ≤ d * r →
    lrCoord 0 s ω < lrCoord 0 u ω ∧ lrCoord 1 s ω < lrCoord 1 u ω}

theorem mem_dirConeTimes_iff {d r s : ℝ} {ω : Path2} :
    s ∈ dirConeTimes d r ω ↔ d * s < d * r ∧ ∀ u, d * s < d * u → d * u ≤ d * r →
      lrCoord 0 s ω < lrCoord 0 u ω ∧ lrCoord 1 s ω < lrCoord 1 u ω :=
  Iff.rfl

/-- **Covering by the box event.** If `s ∈ C(r)` lies in the box `{s : 0 ≤ d (c - s) ≤ h}` with end
`c` facing `r`, and `T = d (r - c) ≥ 0`, then the box event holds. -/
theorem mem_coneBoxEvent_of_mem {ρ : ℝ} (hρ0 : ρ ≤ 0) {d : ℝ} (hd : |d| = 1) {r c h T s : ℝ}
    {ω : Path2} (hs : s ∈ dirConeTimes d r ω) (hu0 : 0 ≤ d * (c - s)) (hu1 : d * (c - s) ≤ h)
    (hT : T = d * (r - c)) (hT0 : 0 ≤ T) : ω ∈ coneBoxEvent ρ d c h T := by
  obtain ⟨-, hs2⟩ := hs
  have hdd : d * d = 1 := by rw [← abs_mul_abs_self, hd, one_mul]
  obtain ⟨u, hu'⟩ : ∃ u : ℝ≥0, (u : ℝ) = d * (c - s) :=
    ⟨Real.toNNReal (d * (c - s)), Real.coe_toNNReal _ hu0⟩
  have hsu : c + -d * (u : ℝ) = s := by
    rw [hu']
    linear_combination (s - c) * hdd
  have hdrop : ∀ i : Fin 2, lrCoord i c ω - lrCoord i s ω ≤ pastDrop i (-d) c h ω := by
    intro i
    have := neg_coneIncr_le_pastDrop i (-d) c h ω (u := u) (by rw [hu']; exact hu1)
    rwa [hsu, coneIncr, neg_sub] at this
  have hfut : ∀ v : ℝ≥0, (v : ℝ) ≤ T →
      lrCoord 0 s ω ≤ lrCoord 0 (c + d * v) ω ∧ lrCoord 1 s ω ≤ lrCoord 1 (c + d * v) ω := by
    intro v hv
    by_cases heq : c + d * (v : ℝ) = s
    · rw [heq]
      exact ⟨le_rfl, le_rfl⟩
    · have e : d * (c + d * v) = d * c + v := by linear_combination (v : ℝ) * hdd
      have hle : d * s ≤ d * (c + d * v) := by
        linarith [NNReal.coe_nonneg v]
      have hlt : d * s < d * (c + d * v) := by
        refine lt_of_le_of_ne hle fun hEq => heq ?_
        calc c + d * v = (d * d) * (c + d * v) := by rw [hdd, one_mul]
          _ = d * (d * (c + d * v)) := by ring
          _ = d * (d * s) := by rw [hEq]
          _ = (d * d) * s := by ring
          _ = s := by rw [hdd, one_mul]
      have hler : d * (c + d * v) ≤ d * r := by
        rw [e]
        linarith
      exact ⟨(hs2 _ hlt hler).1.le, (hs2 _ hlt hler).2.le⟩
  show ∀ q : ℚ, -pastDrop 0 (-d) c h ω ≤ coneIncr 0 (c + d * ratClamp T q) c ω ∧
    -(pastDrop 1 (-d) c h ω - ρ * pastDrop 0 (-d) c h ω) ≤
      coneIncr 1 (c + d * ratClamp T q) c ω - ρ * coneIncr 0 (c + d * ratClamp T q) c ω
  intro q
  obtain ⟨hL, hR⟩ := hfut (ratClamp T q) (ratClamp_le hT0 q)
  have hdL := hdrop 0
  have hdR := hdrop 1
  simp only [coneIncr]
  constructor
  · linarith
  · nlinarith [mul_nonneg (neg_nonneg.2 hρ0)
      (show 0 ≤ lrCoord 0 (c + d * ratClamp T q) ω - lrCoord 0 c ω + pastDrop 0 (-d) c h ω by
        linarith)]

/-! ### Box counting -/

/-- **Finiteness in an interval, for given box ends.** Let `-1 < ρ ≤ 0` (that is `0 < γ ≤ √2`),
`|d| = 1` and `p < q`. Partition `[p, q)` into `n` boxes and choose for each box an end `anc n k`
with `0 ≤ d (anc n k - s) ≤ (q - p) / n` for `s` in the box and `d (r - anc n k) ≥ T₀ > 0`. Then
`C(r) ∩ [p, q)` is finite almost surely. -/
theorem ae_finite_dirConeTimes_inter_Ico_of_anchor {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {d : ℝ} (hd : |d| = 1) (r : ℝ) {p q T₀ : ℝ}
    (hpq : p < q) (hT₀ : 0 < T₀) (anc : ℕ → ℕ → ℝ)
    (hanc : ∀ n k : ℕ, k < n → ∀ s, p + k * ((q - p) / n) ≤ s → s < p + (k + 1) * ((q - p) / n) →
      0 ≤ d * (anc n k - s) ∧ d * (anc n k - s) ≤ (q - p) / n)
    (hT : ∀ n k : ℕ, k < n → T₀ ≤ d * (r - anc n k)) :
    ∀ᵐ ω ∂μ, (dirConeTimes d r ω ∩ Set.Ico p q).Finite := by
  obtain ⟨hρ1, hρ0⟩ := lrCov_zero_one_mem_Ioc hγ0 hγ
  set σ := Real.sqrt (1 - lrCov γ 0 1 ^ 2)
  have hσ0 : 0 < σ := Real.sqrt_pos.2 (by nlinarith)
  refine ae_finite_inter_Ico_of_box_bound (μ := μ) (fun ω => dirConeTimes d r ω) hpq
    (fun n k => coneBoxEvent (lrCov γ 0 1) d (anc n k) ((q - p) / n) (d * (r - anc n k)))
    (fun n k => measurableSet_coneBoxEvent _ _ _ _ _) ?_
    (C := ENNReal.ofReal (18 / (σ * T₀)) *
      (4 * ENNReal.ofReal (gaussianAbsMoment 2 * (q - p))))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)) ?_
  · rintro n k hkn ω ⟨s, hs, hs1, hs2⟩
    obtain ⟨hu0, hu1⟩ := hanc n k hkn s hs1 hs2
    exact mem_coneBoxEvent_of_mem hρ0 hd hs hu0 hu1 rfl (hT₀.le.trans (hT n k hkn))
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hw : 0 ≤ (q - p) / n := div_nonneg (sub_pos.2 hpq).le hn'.le
    calc ∑ k ∈ Finset.range n,
          μ (coneBoxEvent (lrCov γ 0 1) d (anc n k) ((q - p) / n) (d * (r - anc n k)))
        ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (18 / (σ * T₀)) *
            (4 * ENNReal.ofReal (gaussianAbsMoment 2 * ((q - p) / n))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hTk := hT n k (Finset.mem_range.1 hk)
          have hTk0 : 0 < d * (r - anc n k) := hT₀.trans_le hTk
          refine (measure_coneBoxEvent_le hμ hρ0 hρ1 hd (anc n k) hw hTk0).trans ?_
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          rw [div_le_div_iff₀ (mul_pos hσ0 hTk0) (mul_pos hσ0 hT₀)]
          nlinarith [mul_le_mul_of_nonneg_left hTk hσ0.le]
      _ = ENNReal.ofReal (18 / (σ * T₀)) *
            (4 * ENNReal.ofReal (gaussianAbsMoment 2 * (q - p))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hsplit : ENNReal.ofReal (gaussianAbsMoment 2 * (q - p)) =
              (n : ℝ≥0∞) * ENNReal.ofReal (gaussianAbsMoment 2 * ((q - p) / n)) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
            congr 1
            field_simp
          rw [hsplit]
          ring

/-- **Finiteness in an interval.** For `0 < γ ≤ √2`, `d = ±1` and an interval `[p, q)` lying on the
side `-d` of `r`, the set `C(r) ∩ [p, q)` is finite almost surely. -/
theorem ae_finite_dirConeTimes_inter_Ico {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {d : ℝ} (hd : d = 1 ∨ d = -1) (r : ℝ)
    {p q : ℝ} (hpq : p < q) (hp : 0 < d * (r - p)) (hq : 0 < d * (r - q)) :
    ∀ᵐ ω ∂μ, (dirConeTimes d r ω ∩ Set.Ico p q).Finite := by
  rcases hd with rfl | rfl
  · refine ae_finite_dirConeTimes_inter_Ico_of_anchor hγ0 hγ hμ (by simp) r hpq (T₀ := r - q)
      (by linarith) (fun n k => p + (k + 1) * ((q - p) / n)) ?_ ?_
    · intro n k _ s hs1 hs2
      constructor <;> linarith
    · intro n k hkn
      have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hkn
      have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      have hw : 0 < (q - p) / n := div_pos (by linarith) hn
      have hnw : (n : ℝ) * ((q - p) / n) = q - p := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right hkn' hw.le]
  · refine ae_finite_dirConeTimes_inter_Ico_of_anchor hγ0 hγ hμ (by simp) r hpq (T₀ := p - r)
      (by linarith) (fun n k => p + k * ((q - p) / n)) ?_ ?_
    · intro n k _ s hs1 hs2
      constructor <;> linarith
    · intro n k hkn
      have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hkn
      have hw : 0 < (q - p) / n := div_pos (by linarith) hn
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hw.le]

/-- **`C(r)` is countable almost surely**, for `0 < γ ≤ √2` and `d = ±1`. -/
theorem ae_countable_dirConeTimes {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {d : ℝ} (hd : d = 1 ∨ d = -1) (r : ℝ) :
    ∀ᵐ ω ∂μ, (dirConeTimes d r ω).Countable := by
  have hfin : ∀ a b : ℚ, ∀ᵐ ω ∂μ, (a : ℝ) < b → 0 < d * (r - a) → 0 < d * (r - b) →
      (dirConeTimes d r ω ∩ Set.Ico (a : ℝ) b).Finite := by
    intro a b
    by_cases hab : (a : ℝ) < b ∧ 0 < d * (r - a) ∧ 0 < d * (r - b)
    · filter_upwards [ae_finite_dirConeTimes_inter_Ico hγ0 hγ hμ hd r hab.1 hab.2.1 hab.2.2]
        with ω hω _ _ _ using hω
    · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hab
  filter_upwards [ae_all_iff.2 fun a => ae_all_iff.2 (hfin a)] with ω hω
  have hsub : dirConeTimes d r ω ⊆ ⋃ ab ∈ {ab : ℚ × ℚ | (ab.1 : ℝ) < ab.2 ∧
      0 < d * (r - ab.1) ∧ 0 < d * (r - ab.2)}, dirConeTimes d r ω ∩ Set.Ico (ab.1 : ℝ) ab.2 := by
    intro s hs
    have hlt := (mem_dirConeTimes_iff.1 hs).1
    obtain ⟨a, b, hab, has, hsb, ha, hb⟩ : ∃ a b : ℚ, (a : ℝ) < b ∧ (a : ℝ) ≤ s ∧ s < b ∧
        0 < d * (r - a) ∧ 0 < d * (r - b) := by
      rcases hd with rfl | rfl
      · have hlt' : s < r := by linarith
        obtain ⟨a, ha⟩ := exists_rat_lt s
        obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hlt'
        exact ⟨a, b, by linarith, ha.le, hb1, by linarith, by linarith⟩
      · have hlt' : r < s := by linarith
        obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt'
        obtain ⟨b, hb⟩ := exists_rat_gt s
        exact ⟨a, b, by linarith, ha2.le, hb, by linarith, by linarith⟩
    exact Set.mem_biUnion (x := (a, b)) ⟨hab, ha, hb⟩ ⟨hs, has, hsb⟩
  refine Set.Countable.mono hsub (Set.Countable.biUnion (Set.to_countable _) fun ab hab => ?_)
  exact (hω ab.1 ab.2 hab.1 hab.2.1 hab.2.2).countable

/-! ### Cone times -/

/-- **Cone times are countable for `γ ≤ √2`.** For `0 < γ ≤ √2`, almost surely the forward cone
times of the correlated Brownian pair `(L, R)` (times `s` with forward direct `L`- and `R`-partners
`t₁ ≠ t₂`) and its backward cone times form countable sets. -/
theorem ae_countable_coneTimes_of_le_sqrt_two {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ Real.sqrt 2)
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ,
      {s | ∃ t₁ t₂, t₁ ≠ t₂ ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 0 u ω) s t₁ ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 1 u ω) s t₂}.Countable ∧
      {s | ∃ t₁ t₂, t₁ ≠ t₂ ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 0 u ω) t₁ s ∧
          MatedCRTHarmonic.MatedCRT.DirectRel (fun u => lrCoord 1 u ω) t₂ s}.Countable := by
  have hF : ∀ᵐ ω ∂μ, ∀ r : ℚ, (dirConeTimes 1 r ω).Countable :=
    ae_all_iff.2 fun r => ae_countable_dirConeTimes hγ0 hγ hμ (Or.inl rfl) r
  have hB : ∀ᵐ ω ∂μ, ∀ r : ℚ, (dirConeTimes (-1) r ω).Countable :=
    ae_all_iff.2 fun r => ae_countable_dirConeTimes hγ0 hγ hμ (Or.inr rfl) r
  filter_upwards [hF, hB] with ω hωF hωB
  constructor
  · refine (Set.countable_iUnion hωF).mono ?_
    rintro s ⟨t₁, t₂, -, ⟨hst₁, -, h₁⟩, ⟨hst₂, -, h₂⟩⟩
    obtain ⟨r, hsr, hr⟩ := exists_rat_btwn (lt_min hst₁ hst₂)
    refine Set.mem_iUnion.2 ⟨r, mem_dirConeTimes_iff.2 ⟨by linarith, fun u hsu hur => ?_⟩⟩
    have hu1 : s < u := by linarith
    have hu2 : u ≤ r := by linarith
    have hm1 := min_le_left t₁ t₂
    have hm2 := min_le_right t₁ t₂
    exact ⟨h₁ u ⟨hu1, by linarith⟩, h₂ u ⟨hu1, by linarith⟩⟩
  · refine (Set.countable_iUnion hωB).mono ?_
    rintro s ⟨t₁, t₂, -, ⟨hst₁, he₁, h₁⟩, ⟨hst₂, he₂, h₂⟩⟩
    obtain ⟨r, hr, hrs⟩ := exists_rat_btwn (max_lt hst₁ hst₂)
    refine Set.mem_iUnion.2 ⟨r, mem_dirConeTimes_iff.2 ⟨by linarith, fun u hsu hur => ?_⟩⟩
    have hu1 : u < s := by linarith
    have hu2 : (r : ℝ) ≤ u := by linarith
    have hm1 := le_max_left t₁ t₂
    have hm2 := le_max_right t₁ t₂
    have k₁ : lrCoord 0 t₁ ω < lrCoord 0 u ω := h₁ u ⟨by linarith, hu1⟩
    have k₂ : lrCoord 1 t₂ ω < lrCoord 1 u ω := h₂ u ⟨by linarith, hu1⟩
    have e₁ : lrCoord 0 t₁ ω = lrCoord 0 s ω := he₁
    have e₂ : lrCoord 1 t₂ ω = lrCoord 1 s ω := he₂
    exact ⟨by linarith, by linarith⟩

end LatticeProb.CorrelatedBM
