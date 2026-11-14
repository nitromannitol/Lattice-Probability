import Mathlib
import LatticeProb.Prob.BrownianFrequentPositivity
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0

/-!
# Immediate descent of the correlated Brownian pair at rational times

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` of the mating-of-trees
encoding (`IsCorrelatedBM2 γ μ`, paths in `Path2 = C(ℝ, ℝ × ℝ)`). Almost surely, for every
rational time `q` and both coordinates `X ∈ {L, R}`, the path takes values strictly below `X q` at
times arbitrarily close to `q`, both before and after `q`.

After `q`, the recentred increments `X (q + t) - X q` form a standard Brownian motion
(`shiftedCoordinate_isBrownianReal`); before `q`, so do the time-reversed increments
`X (q - t) - X q` (`reversedCoordinate_isBrownianReal`; the covariance kernel
`twoSidedMin x y = (|x| + |y| - |x - y|) / 2` is invariant under these changes of origin and
orientation). A standard Brownian motion takes negative values at arbitrarily small positive times,
by Blumenthal's zero-one law (`ae_frequently_pos_of_isBrownianReal_blumenthal` applied to `-B`).

* `ae_rat_descends`: the statement for a fixed coordinate and a fixed rational time.
* `ae_forall_rat_descends`: the same almost surely for all coordinates and rational times at once.

No condition on `γ` is needed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- The two-sided Brownian covariance kernel in terms of absolute values. -/
lemma twoSidedMin_eq_abs (x y : ℝ) : twoSidedMin x y = (|x| + |y| - |x - y|) / 2 := by
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

/-- A standard real Brownian motion takes negative values at arbitrarily small positive times,
almost surely (Blumenthal's zero-one law applied to `-B`). -/
theorem ae_forall_pos_exists_lt_zero {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, 0 < (t : ℝ) ∧ (t : ℝ) < ε ∧ B t ω < 0 := by
  have h := LatticeProb.ae_frequently_pos_of_isBrownianReal_blumenthal hB.neg
    (fun t => (hBm t).neg)
  filter_upwards [h] with ω hω ε hε
  have hU : ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), t ∈ Ioo 0 (Real.toNNReal ε) :=
    Ioo_mem_nhdsGT (Real.toNNReal_pos.2 hε)
  obtain ⟨t, hpos, ht⟩ := (hω.and_eventually hU).exists
  refine ⟨t, NNReal.coe_pos.2 ht.1, ?_, ?_⟩
  · have h2 := NNReal.coe_lt_coe.2 ht.2
    rwa [Real.coe_toNNReal _ hε.le] at h2
  · simpa using hpos

/-- A deterministic-time reversal of a correlated coordinate, recentred at the reversal time. -/
def reversedCoordinate (i : Fin 2) (a : ℝ) : ℝ≥0 → Path2 → ℝ :=
  fun t ω => lrCoord i (a - (t : ℝ)) ω - lrCoord i a ω

/-- Recentred past increments, read backwards in time, of either correlated coordinate form a
standard Brownian motion. -/
theorem reversedCoordinate_isBrownianReal {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (a : ℝ) :
    IsBrownianReal (reversedCoordinate i a) μ := by
  have : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hL2 : ∀ t : ℝ, MemLp (lrCoord i t) 2 μ := fun t =>
    (hμ.isGaussianProcess.hasGaussianLaw_eval (i, t)).memLp_two
  have hX : IsGaussianProcess (fun t : ℝ => lrCoord i (a - t)) μ :=
    hμ.isGaussianProcess.comp_right (fun t : ℝ => (i, a - t))
  have hGP : IsGaussianProcess (reversedCoordinate i a) μ := by
    have h : IsGaussianProcess
        (fun t : ℝ≥0 => fun ω => lrCoord i (a - (0 + (t : ℝ))) ω - lrCoord i (a - 0) ω) μ :=
      (hX.shift 0).comp_right (fun t : ℝ≥0 => (t : ℝ))
    have hfun : (fun t : ℝ≥0 => fun ω => lrCoord i (a - (0 + (t : ℝ))) ω - lrCoord i (a - 0) ω) =
        reversedCoordinate i a := by
      funext t ω
      simp [reversedCoordinate]
    rw [hfun] at h
    exact h
  have hmean : ∀ t : ℝ≥0, ∫ ω, reversedCoordinate i a t ω ∂μ = 0 := by
    intro t
    simp only [reversedCoordinate]
    rw [integral_sub ((hL2 _).integrable (by norm_num)) ((hL2 a).integrable (by norm_num)),
      hμ.integral_eq_zero i (a - (t : ℝ)), hμ.integral_eq_zero i a, sub_self]
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[reversedCoordinate i a s, reversedCoordinate i a t; μ] = s := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hc : lrCov γ i i = 1 := by simp [lrCov]
    have e1 : a - (s : ℝ) - (a - t) = t - s := by ring
    have e2 : a - (s : ℝ) - a = -s := by ring
    have e3 : a - (a - (t : ℝ)) = t := by ring
    change cov[fun ω => lrCoord i (a - (s : ℝ)) ω - lrCoord i a ω,
      fun ω => lrCoord i (a - (t : ℝ)) ω - lrCoord i a ω; μ] = (s : ℝ)
    rw [covariance_fun_sub_fun_sub (hL2 _) (hL2 a) (hL2 _) (hL2 a),
      hμ.covariance_eq i i (a - (s : ℝ)) (a - (t : ℝ)), hμ.covariance_eq i i (a - (s : ℝ)) a,
      hμ.covariance_eq i i a (a - (t : ℝ)), hμ.covariance_eq i i a a, hc]
    simp only [one_mul, twoSidedMin_eq_abs, e1, e2, e3, sub_self, abs_zero, abs_neg,
      abs_of_nonneg (NNReal.coe_nonneg s), abs_of_nonneg (NNReal.coe_nonneg t),
      abs_of_nonneg (sub_nonneg.2 hst')]
    ring
  have hpre : IsPreBrownianReal (reversedCoordinate i a) μ :=
    hGP.isPreBrownianReal_of_covariance hmean hcov
  refine ⟨hpre, ?_⟩
  apply ae_of_all
  intro ω
  have hx : Continuous (fun t : ℝ => lrCoord i t ω) := by
    by_cases hi : i = 0
    · subst hi
      simp only [lrCoord, ↓reduceIte]
      exact continuous_fst.comp ω.continuous
    · simp only [lrCoord, hi, ↓reduceIte]
      exact continuous_snd.comp ω.continuous
  change Continuous (fun t : ℝ≥0 => lrCoord i (a - (t : ℝ)) ω - lrCoord i a ω)
  exact (hx.comp (continuous_const.sub continuous_subtype_val)).sub continuous_const

/-- **Immediate descent at a fixed rational time.** For a fixed coordinate `i` and a fixed
rational time `q`, almost surely the coordinate path takes values strictly below its value at `q`
at times arbitrarily close to `q`, both before and after `q`. -/
theorem ae_rat_descends {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    (i : Fin 2) (q : ℚ) :
    ∀ᵐ ω ∂μ, (∀ u < (q : ℝ), ∃ w ∈ Set.Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
      ∀ u, (q : ℝ) < u → ∃ w ∈ Set.Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω := by
  have hL := ae_forall_pos_exists_lt_zero (reversedCoordinate_isBrownianReal hμ i (q : ℝ))
    (fun t => (measurable_lrCoord (i, (q : ℝ) - (t : ℝ))).sub (measurable_lrCoord (i, (q : ℝ))))
  have hR := ae_forall_pos_exists_lt_zero (shiftedCoordinate_isBrownianReal hμ i (q : ℝ))
    (fun t => (measurable_lrCoord (i, (q : ℝ) + (t : ℝ))).sub (measurable_lrCoord (i, (q : ℝ))))
  filter_upwards [hL, hR] with ω hωL hωR
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨t, ht0, htε, hneg⟩ := hωL ((q : ℝ) - u) (sub_pos.2 hu)
    refine ⟨(q : ℝ) - t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i ((q : ℝ) - t) ω - lrCoord i q ω < 0 := hneg
    linarith
  · obtain ⟨t, ht0, htε, hneg⟩ := hωR (u - (q : ℝ)) (sub_pos.2 hu)
    refine ⟨(q : ℝ) + t, ⟨by linarith, by linarith⟩, ?_⟩
    have h' : lrCoord i ((q : ℝ) + t) ω - lrCoord i q ω < 0 := hneg
    linarith

/-- **Immediate descent at every rational time.** Almost surely, for both coordinates and every
rational time `q`, the coordinate path takes values strictly below its value at `q` at times
arbitrarily close to `q`, both before and after `q`. -/
theorem ae_forall_rat_descends {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ q : ℚ,
      (∀ u < (q : ℝ), ∃ w ∈ Set.Ioo u (q : ℝ), lrCoord i w ω < lrCoord i q ω) ∧
      (∀ u, (q : ℝ) < u → ∃ w ∈ Set.Ioo (q : ℝ) u, lrCoord i w ω < lrCoord i q ω) :=
  ae_all_iff.2 fun i => ae_all_iff.2 fun q => ae_rat_descends hμ i q

end LatticeProb.CorrelatedBM

end LatticeProb.CorrelatedBM
