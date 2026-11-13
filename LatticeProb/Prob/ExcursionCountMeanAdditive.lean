import LatticeProb.Analysis.ExcursionCountShift
import LatticeProb.Prob.BrownianFirstPassageStrict

/-!
# Additivity of the mean excursion count of Brownian motion

For a path `f : ℝ≥0 → ℝ`, `pathExcursionCount f b ε` is the number of excursions of `f` above its running minimum,
of length larger than `ε`, completed before the first passage of `f` strictly below `f 0 - b`. For a real Brownian
motion `B` with continuous paths and levels `a, b ≥ 0`,

  `E [pathExcursionCount B (a + b) ε] = E [pathExcursionCount B a ε] + E [pathExcursionCount B b ε]`.

The proof splits the path at the first passage `T` below `B 0 - a`. Almost surely `T` is the hitting time of
`{B ≤ -a}`, a stopping time; the excursions completed before the first passage below `B 0 - (a + b)` are those
completed before `T` and those of the restarted motion `B (T + ·) - B T` completed before its first passage below
`-b`. By the strong Markov property the latter count is independent of the past at `T` and has the law of the count
of `B` at level `b`. To work with finite stopping times the hitting time is truncated at a horizon `N`, on the event
that it is smaller than `N`, and `N → ∞` by monotone convergence.

* `tsum_ite_succ_le`: a natural number as the sum of the indicators of `k + 1 ≤ n`;
* `exists_measurable_pathExcursionCount`: a measurable path functional equal to the excursion count on continuous
  paths;
* `isStoppingTime_hitDriftTrunc_neg_natFiltration`: the truncated hitting time of `{B ≤ -a}` is a stopping time;
* `setLIntegral_restart_pathExcursionCount`: the mean count of the restarted motion on an event of the past;
* `ae_pathExcursionCount_add_restart`: the pathwise splitting of the count at the hitting time;
* `lintegral_pathExcursionCount_add`: the additivity of the mean count.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- A natural number `n` is the number of `k` with `k + 1 ≤ n`. -/
theorem tsum_ite_succ_le (n : ℕ) : ∑' k : ℕ, (if k + 1 ≤ n then (1 : ℝ≥0∞) else 0) = n := by
  rw [tsum_eq_sum (s := Finset.range n) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [ite_eq_right (by omega)]]
  rw [Finset.sum_congr rfl fun k hk => ite_eq_left (by rw [Finset.mem_range] at hk; omega)]
  simp

/-- **A measurable version of the excursion count.** For `ε > 0` there is a measurable path functional
`Φ : (ℝ≥0 → ℝ) → ℝ≥0∞` equal to `pathExcursionCount f b ε` at every continuous path `f`. -/
theorem exists_measurable_pathExcursionCount (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable Φ ∧
      ∀ f : ℝ≥0 → ℝ, Continuous f → Φ f = (pathExcursionCount f b ε : ℝ≥0∞) := by
  choose Γ hΓ hΓP using fun k : ℕ => exists_measurableSet_le_pathExcursionCount b hε k
  refine ⟨fun f => ∑' k : ℕ, (Γ (k + 1)).indicator 1 f, ?_, fun f hf => ?_⟩
  · exact Measurable.tsum fun k => measurable_one.indicator (hΓ (k + 1))
  · rw [← tsum_ite_succ_le (pathExcursionCount f b ε)]
    refine tsum_congr fun k => ?_
    by_cases h : k + 1 ≤ pathExcursionCount f b ε
    · rw [ite_eq_left h, indicator_of_mem ((hΓP (k + 1) f hf).2 h), Pi.one_apply]
    · rw [ite_eq_right h, indicator_of_notMem fun h' => h ((hΓP (k + 1) f hf).1 h')]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The hitting time of `{B ≤ -a}`, truncated at the horizon `N`, is a stopping time of the natural filtration of
the lift of `B`. -/
theorem isStoppingTime_hitDriftTrunc_neg_natFiltration (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (a : ℝ) (N : ℝ≥0) :
    IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞) := by
  have h := (isStoppingTime_hitDrift_neg_natFiltration hm hcont 0 a).min_const (i := N)
  rw [neg_zero] at h
  have hfun : (fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞))
      = fun ω => min (hitDrift (fun t ω => -B t ω) 0 a ω) (N : ℝ≥0∞) := by
    funext ω
    exact coe_hitDriftTrunc _ _ a N ω
  rw [hfun]
  exact h

/-- **The mean excursion count of the restarted motion.** For a real Brownian motion `B` with continuous paths, a
finite stopping time `τ` of the natural filtration and an event `E` of the past at `τ`, the mean on `E` of the
excursion count of `B (τ + ·) - B τ` is `P E` times the mean excursion count of `B`. -/
theorem setLIntegral_restart_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω in E, (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞) ∂P
      = P E * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
  obtain ⟨Φ, hΦ, hΦJ⟩ := exists_measurable_pathExcursionCount b hε
  have h := lintegral_restrict_driftIncr hB hm hcont 0 τ hτ hE hΦ
  have h1 : ∀ ω, driftIncr B 0 τ ω = fun t => B (τ ω + t) ω - B (τ ω) ω := by
    intro ω
    funext t
    simp [driftIncr]
  have h2 : ∀ ω, (fun t : ℝ≥0 => B t ω + 0 * (t : ℝ)) = fun t => B t ω := by
    intro ω
    funext t
    simp
  calc ∫⁻ ω in E, (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞) ∂P
      = ∫⁻ ω in E, Φ (driftIncr B 0 τ ω) ∂P := by
        refine lintegral_congr fun ω => ?_
        have hc : Continuous fun t => B (τ ω + t) ω - B (τ ω) ω :=
          ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
        rw [h1, hΦJ _ hc]
    _ = P E * ∫⁻ ω, Φ (fun t : ℝ≥0 => B t ω + 0 * (t : ℝ)) ∂P := h
    _ = P E * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [h2, hΦJ _ (hcont ω)]

/-- **Splitting the excursion count at the hitting time.** For a real Brownian motion `B` with continuous paths,
levels `a, b ≥ 0` and a horizon `N`, almost surely on the event that `B` reaches `{B ≤ -a}` by time `N`, the count
at level `a + b` is the count at level `a` plus the count at level `b` of the motion restarted at the (truncated)
hitting time `σ` of `{B ≤ -a}`, `B (σ + ·) - B σ`. -/
theorem ae_pathExcursionCount_add_restart [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, hitDrift (fun t ω => -B t ω) 0 a ω ≤ (N : ℝ≥0∞) →
      pathExcursionCount (fun t => B t ω) (a + b) ε =
        pathExcursionCount (fun t => B t ω) a ε +
          pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
            B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε := by
  filter_upwards [ae_firstPassageBelow_eq_hitDriftTrunc hB hm hcont a N,
    ae_firstPassageBelow_eq_hitDrift hB hm hcont (a + b)] with ω h1 h2 hle
  obtain ⟨hT, -⟩ := h1 hle
  generalize hitDriftTrunc (fun t ω => -B t ω) 0 a N ω = σ at hT ⊢
  unfold pathExcursionCount
  refine excursionCount_firstPassageBelow_add_restart (c := -B σ ω) (continuous_nnExtend (hcont ω)) ha hb hε
    h2.2.2 fun u hu => ?_
  rw [hT]
  simp only [nnExtend]
  rw [Real.toNNReal_add σ.coe_nonneg hu, Real.toNNReal_coe]
  ring

/-- **Additivity of the mean excursion count.** For a real Brownian motion `B` with continuous paths, levels
`a, b ≥ 0` and `ε > 0`, the mean number of excursions above the running minimum of length larger than `ε` completed
before the first passage below `B 0 - (a + b)` is the sum of the means for the levels `a` and `b`. -/
theorem lintegral_pathExcursionCount_add [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ∂P =
      ∫⁻ ω, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P +
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
  set A : ℕ → Set Ω := fun N => {ω | hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞)}
  have hτ := fun N : ℕ => isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a (N : ℝ≥0)
  have hA : ∀ N : ℕ, MeasurableSet[(hτ N).measurableSpace] (A N) := by
    intro N
    have h := (hτ N).measurableSet_lt' (N : ℝ≥0)
    convert h using 1
    ext ω
    change hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞) ↔ ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞)
    rw [coe_hitDriftTrunc, inf_lt_iff, lt_self_iff_false, or_false]
  have hAm : ∀ N : ℕ, MeasurableSet (A N) := fun N => (hτ N).measurableSpace_le _ (hA N)
  have hmono : Monotone A := by
    intro N M hNM ω hω
    exact lt_of_lt_of_le (show hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞) from hω)
      (by exact_mod_cast hNM)
  have hunion : (⋃ N, A N) =ᵐ[P] (univ : Set Ω) := by
    refine ae_eq_univ.2 (measure_mono_null (fun ω hω => ?_) (ae_iff.1 (ae_hitDrift_neg_lt_top hB hm hcont a)))
    intro hlt
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hlt.ne
    refine hω (mem_iUnion.2 ⟨N, ?_⟩)
    show hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞)
    rwa [ENNReal.coe_natCast]
  have hlim : ∀ f : Ω → ℝ≥0∞, ⨆ N, ∫⁻ ω in A N, f ω ∂P = ∫⁻ ω, f ω ∂P := by
    intro f
    rw [← setLIntegral_iUnion_of_directed f hmono.directed_le, setLIntegral_congr hunion, setLIntegral_univ]
  have hP1 : ⨆ N, P (A N) = 1 := by
    have h := hlim fun _ => 1
    simp only [lintegral_one, Measure.restrict_apply_univ] at h
    rw [measure_univ] at h
    exact h
  have hmeas : ∀ c : ℝ, Measurable fun ω => (pathExcursionCount (fun t => B t ω) c ε : ℝ≥0∞) := fun c =>
    measurable_from_nat.comp (measurable_pathExcursionCount hm hcont c hε)
  have hN : ∀ N : ℕ, ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ∂P =
      ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P +
        P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
    intro N
    rw [← setLIntegral_restart_pathExcursionCount hB hm hcont _ (hτ N) (hA N) b hε,
      ← lintegral_add_left (hmeas a)]
    refine setLIntegral_congr_fun_ae (hAm N) ?_
    filter_upwards [ae_pathExcursionCount_add_restart hB hm hcont ha hb hε (N : ℝ≥0)] with ω hω hωA
    rw [hω hωA.le, Nat.cast_add]
  calc ∫⁻ ω, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ∂P
      = ⨆ N, ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ∂P := (hlim _).symm
    _ = ⨆ N, (∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P +
          P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) := iSup_congr hN
    _ = (⨆ N, ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) +
          ⨆ N, P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
        refine (ENNReal.iSup_add_iSup_of_monotone (fun N M hNM => lintegral_mono_set (hmono hNM))
          fun N M hNM => mul_le_mul_of_nonneg_right (measure_mono (hmono hNM)) zero_le).symm
    _ = ∫⁻ ω, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P +
          ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
        rw [hlim, ← ENNReal.iSup_mul, hP1, one_mul]

end LatticeProb.LadderSet
