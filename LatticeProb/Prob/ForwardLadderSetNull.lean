import LatticeProb.Prob.BrownianFirstPassageStrict
import LatticeProb.Analysis.ExcursionCountLadderRational

/-!
# The forward ladder set of a Brownian motion is Lebesgue-null

For a real Brownian motion `B` with continuous paths, the forward ladder set from `0` of the path `t ↦ B t`
(extended to `ℝ` by `nnExtend`), that is the set of times `t ≥ 0` at which `B t = min_{[0, t]} B`, has Lebesgue
measure zero almost surely.

* `isBrownianReal_timeReversal`: for `t₀ ≥ 0`, the process `s ↦ B (t₀ - s) - B (max s t₀)` (truncated subtraction)
  is a Brownian motion: on `[0, t₀]` it is the time reversal `B (t₀ - s) - B t₀` of `B` from `t₀`, and after `t₀` it
  continues with the increments `B 0 - B s`;
* `ae_notMem_forwardLadderSet`: for a fixed `t > 0`, almost surely `t` is not a ladder time, because the reversed
  motion takes negative values at arbitrarily small times, i.e. `B (t - ε) < B t` for arbitrarily small `ε > 0`;
* `mem_forwardLadderSet_zero_iff_rat`: for a continuous path, the ladder condition can be tested at rational times;
* `measurableSet_forwardLadderSet_prod`: the set of pairs `(t, ω)` with `t` a ladder time of the path of `ω` is
  measurable for the product σ-algebra;
* `ae_volume_forwardLadderSet_eq_zero`: by Fubini, almost surely the ladder set is Lebesgue-null.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

open QuantumZipper.GermZeroOne MatedCRTHarmonic.MatedCRT

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Time reversal of a Brownian motion.** For `t₀ ≥ 0`, the process `s ↦ B (t₀ - s) - B (max s t₀)`
(truncated subtraction on `ℝ≥0`) is a Brownian motion. On `[0, t₀]` it equals `B (t₀ - s) - B t₀`. -/
theorem isBrownianReal_timeReversal (hB : IsBrownianReal B P) (t₀ : ℝ≥0) :
    IsBrownianReal (fun s ω => B (t₀ - s) ω - B (max s t₀) ω) P := by
  classical
  have hpre := hB.toIsPreBrownianReal
  have : IsProbabilityMeasure P := hpre.isGaussianProcess.isProbabilityMeasure
  have hGP : IsGaussianProcess (fun s ω => B (t₀ - s) ω - B (max s t₀) ω) P :=
    hpre.isGaussianProcess.of_isGaussianProcess fun s => ⟨{t₀ - s, max s t₀},
      { toFun x := x ⟨t₀ - s, by simp⟩ - x ⟨max s t₀, by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
      by simp⟩
  have hL2 : ∀ t : ℝ≥0, MemLp (B t) 2 P := fun t =>
    (hpre.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hmean : ∀ s : ℝ≥0, P[fun ω => B (t₀ - s) ω - B (max s t₀) ω] = 0 := by
    intro s
    rw [integral_sub (hpre.integrable_eval _) (hpre.integrable_eval _), hpre.integral_eval,
      hpre.integral_eval, sub_zero]
  have hcov : ∀ s t : ℝ≥0, s ≤ t →
      cov[fun ω => B (t₀ - s) ω - B (max s t₀) ω, fun ω => B (t₀ - t) ω - B (max t t₀) ω; P] = s := by
    intro s t hst
    rw [covariance_fun_sub_fun_sub (hL2 _) (hL2 _) (hL2 _) (hL2 _), hpre.covariance_eval,
      hpre.covariance_eval, hpre.covariance_eval, hpre.covariance_eval]
    have h1 : t₀ - t ≤ t₀ - s := tsub_le_tsub_left hst t₀
    have h2 : t₀ - s ≤ max t t₀ := tsub_le_self.trans (le_max_right _ _)
    have h3 : t₀ - t ≤ max s t₀ := tsub_le_self.trans (le_max_right _ _)
    have h4 : max s t₀ ≤ max t t₀ := max_le_max hst le_rfl
    simp only [min_eq_right h1, min_eq_left h2, min_eq_right h3, min_eq_left h4]
    rcases le_total s t₀ with hs | hs
    · rw [max_eq_right hs, NNReal.coe_sub hs]
      ring
    · rw [max_eq_left hs, tsub_eq_zero_of_le hs]
      simp
  refine ⟨hGP.isPreBrownianReal_of_covariance hmean hcov, ?_⟩
  filter_upwards [hB.cont] with ω h
  exact (h.comp (continuous_const.sub continuous_id)).sub (h.comp (continuous_id.max continuous_const))

/-- **A fixed positive time is almost surely not a ladder time.** For `t > 0`, almost surely `t` is not a forward
ladder time from `0` of the Brownian path: the time-reversed motion from `t` is negative at arbitrarily small
times, so `B (t - ε) < B t` for some small `ε > 0`. -/
theorem ae_notMem_forwardLadderSet [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, t ∉ forwardLadderSet (nnExtend fun s => B s ω) 0 := by
  have ht₀ : 0 < t.toNNReal := Real.toNNReal_pos.2 ht
  obtain ⟨n, hn⟩ := (tendsto_epsSeq.eventually (gt_mem_nhds ht₀)).exists
  have hW := isBrownianReal_timeReversal hB t.toNNReal
  have hWm : ∀ s, Measurable (fun ω => B (t.toNNReal - s) ω - B (max s t.toNNReal) ω) :=
    fun s => (hm _).sub (hm _)
  filter_upwards [ae_mem_negNearZeroSet hW hWm] with ω hω hmem
  obtain ⟨k, hk, hlt⟩ := (mem_negNearZeroSet.1 hω) n
  have hεk : epsSeq k ≤ t.toNNReal := (epsSeq_antitone hk).trans hn.le
  have hs : ((t.toNNReal - epsSeq k : ℝ≥0) : ℝ) ∈ Icc 0 t := by
    refine ⟨NNReal.coe_nonneg _, ?_⟩
    have : ((t.toNNReal - epsSeq k : ℝ≥0) : ℝ) ≤ (t.toNNReal : ℝ) := by exact_mod_cast tsub_le_self
    rwa [Real.coe_toNNReal _ ht.le] at this
  have hle := hmem.2 _ hs
  simp only [nnExtend, Real.toNNReal_coe] at hle
  simp only [max_eq_right hεk] at hlt
  linarith

/-- **Ladder times at rational times.** For a continuous path `X`, `t` is a forward ladder time from `0` iff
`t ≥ 0` and `X t ≤ X q` for every rational `q ∈ [0, t]`. -/
theorem mem_forwardLadderSet_zero_iff_rat {X : ℝ → ℝ} (hX : Continuous X) {t : ℝ} :
    t ∈ forwardLadderSet X 0 ↔ 0 ≤ t ∧ ∀ q : ℚ, (q : ℝ) < 0 ∨ t < q ∨ X t ≤ X q := by
  constructor
  · intro h
    refine ⟨h.1, fun q => ?_⟩
    rcases lt_or_ge (q : ℝ) 0 with hq | hq
    · exact Or.inl hq
    rcases lt_or_ge t q with hqt | hqt
    · exact Or.inr (Or.inl hqt)
    · exact Or.inr (Or.inr (h.2 q ⟨hq, hqt⟩))
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun s hs => ?_⟩
    rcases h0.eq_or_lt with h0t | h0t
    · have : s = t := le_antisymm (h0t ▸ hs.2) (h0t ▸ hs.1)
      rw [this]
    · refine le_of_forall_rat_mem_Icc hX.continuousOn h0t (fun q hq => ?_) s hs
      rcases h q with hq' | hq' | hq'
      · exact absurd hq.1 (not_le.2 hq')
      · exact absurd hq.2 (not_le.2 hq')
      · exact hq'

/-- **Joint measurability of the ladder set.** For a process with measurable coordinates and continuous paths,
the set of pairs `(t, ω)` such that `t` is a forward ladder time from `0` of the path of `ω` is measurable. -/
theorem measurableSet_forwardLadderSet_prod (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) :
    MeasurableSet {x : ℝ × Ω | x.1 ∈ forwardLadderSet (nnExtend fun t => B t x.2) 0} := by
  set u : ℝ → Ω → ℝ := fun t ω => nnExtend (fun s => B s ω) t with hu
  have hF : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_nnExtend (hcont ω))
      (fun t => hm _)
  have hset : {x : ℝ × Ω | x.1 ∈ forwardLadderSet (nnExtend fun t => B t x.2) 0} =
      {x | 0 ≤ x.1} ∩ ⋂ q : ℚ, ({_x | (q : ℝ) < 0} ∪ {x | x.1 < (q : ℝ)} ∪
        {x | Function.uncurry u x ≤ u (q : ℝ) x.2}) := by
    ext x
    rw [mem_ofPred_eq, mem_forwardLadderSet_zero_iff_rat (continuous_nnExtend (hcont x.2))]
    simp only [mem_inter_iff, mem_iInter, mem_union, mem_ofPred_eq, Function.uncurry, hu, or_assoc]
  rw [hset]
  refine (measurableSet_le measurable_const measurable_fst).inter (MeasurableSet.iInter fun q => ?_)
  refine ((MeasurableSet.const _).union (measurableSet_lt measurable_fst measurable_const)).union ?_
  exact measurableSet_le hF ((hm _).comp measurable_snd)

/-- **The ladder set of a Brownian motion is Lebesgue-null.** For a real Brownian motion with measurable
coordinates and continuous paths, almost surely the forward ladder set from `0` of the path has Lebesgue measure
zero. -/
theorem ae_volume_forwardLadderSet_eq_zero [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) :
    ∀ᵐ ω ∂P, volume (forwardLadderSet (nnExtend fun t => B t ω) 0) = 0 := by
  have hmeas : MeasurableSet
      {x : ℝ × Ω | (fun t ω => t ∉ forwardLadderSet (nnExtend fun s => B s ω) 0) x.1 x.2} :=
    (measurableSet_forwardLadderSet_prod hm hcont).compl
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ ω ∂P, t ∉ forwardLadderSet (nnExtend fun s => B s ω) 0 := by
    filter_upwards [h0] with t ht
    rcases lt_or_gt_of_ne ht with hlt | hpos
    · exact ae_of_all _ fun ω hω => (not_le.2 hlt) hω.1
    · exact ae_notMem_forwardLadderSet hB hm hpos
  filter_upwards [(Measure.ae_ae_comm hmeas).1 h1] with ω hω
  exact measure_eq_zero_iff_ae_notMem.2 hω

end LatticeProb.LadderSet
