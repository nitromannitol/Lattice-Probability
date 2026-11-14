import LatticeProb.Prob.ExcursionCountMeanAdditive
import LatticeProb.Prob.ExcursionCountStopped

/-!
# The second moment of the excursion count of Brownian motion

For a path `f : ℝ≥0 → ℝ`, `pathExcursionCount f b ε` is the number of excursions of `f` above its running minimum,
of length larger than `ε`, completed before the first passage of `f` strictly below `f 0 - b`. For a real Brownian
motion `B` with continuous paths, levels `a, b ≥ 0` and `ε > 0`, writing `J(c)` for the count at level `c`,

  `E [J(a + b)²] = E [J(a)²] + 2 E [J(a)] E [J(b)] + E [J(b)²]`.

The path is split at the first passage `T` below `B 0 - a`: `J(a + b) = J(a) + J'(b)`, where `J'(b)` is the count of
the restarted motion `B (T + ·) - B T`. By the strong Markov property `J'(b)` is independent of the past at `T`, which
contains `J(a)`, and has the law of `J(b)`; so the mixed moment factorises. As for the mean, the hitting time is
truncated at a horizon `N`, on the event that it is smaller than `N`, and `N → ∞` by monotone convergence.

* `lintegral_natCast_mul_eq_tsum`: `∫⁻ X f = ∑ₖ ∫⁻_{k + 1 ≤ X} f` for a natural-number-valued `X`;
* `measurable_restart_pathExcursionCount`: the count of the restarted motion is measurable;
* `setLIntegral_restart_pathExcursionCount_sq`: the second moment of the restarted count on an event of the past;
* `setLIntegral_mul_restart_pathExcursionCount`: the factorisation of the mixed moment;
* `lintegral_pathExcursionCount_add_sq`: the splitting of the second moment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Layer-cake formula for a mixed moment.** For a natural-number-valued `X` with measurable upper level sets and
a measurable `f ≥ 0`, `∫⁻ X f = ∑ₖ ∫⁻_{k + 1 ≤ X} f`. -/
theorem lintegral_natCast_mul_eq_tsum {μ : Measure Ω} {X : Ω → ℕ} (hX : ∀ k, MeasurableSet {ω | k ≤ X ω})
    {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, (X ω : ℝ≥0∞) * f ω ∂μ = ∑' k : ℕ, ∫⁻ ω in {ω | k + 1 ≤ X ω}, f ω ∂μ := by
  calc ∫⁻ ω, (X ω : ℝ≥0∞) * f ω ∂μ
      = ∫⁻ ω, ∑' k : ℕ, {ω | k + 1 ≤ X ω}.indicator f ω ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [← tsum_ite_succ_le (X ω), ← ENNReal.tsum_mul_right]
        refine tsum_congr fun k => ?_
        by_cases h : k + 1 ≤ X ω
        · simp only [h, ↓reduceIte, one_mul]
          exact (indicator_of_mem (show ω ∈ {ω | k + 1 ≤ X ω} from h) f).symm
        · simp only [h, ↓reduceIte, zero_mul]
          exact (indicator_of_notMem (show ω ∉ {ω | k + 1 ≤ X ω} from h) f).symm
    _ = ∑' k : ℕ, ∫⁻ ω, {ω | k + 1 ≤ X ω}.indicator f ω ∂μ :=
        lintegral_tsum fun k => (hf.indicator (hX (k + 1))).aemeasurable
    _ = ∑' k : ℕ, ∫⁻ ω in {ω | k + 1 ≤ X ω}, f ω ∂μ :=
        tsum_congr fun k => lintegral_indicator (hX (k + 1)) f

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The increments of `B` after `τ` are the restarted path `B (τ + ·) - B τ`. -/
theorem driftIncr_zero (τ : Ω → ℝ≥0) (ω : Ω) :
    driftIncr B 0 τ ω = fun t => B (τ ω + t) ω - B (τ ω) ω := by
  funext t
  simp [driftIncr]

/-- For a measurable time `τ`, the excursion count of the restarted motion `B (τ + ·) - B τ` is measurable. -/
theorem measurable_restart_pathExcursionCount (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {τ : Ω → ℝ≥0} (hτ : Measurable τ) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun ω => (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞) := by
  obtain ⟨Φ, hΦ, hΦJ⟩ := exists_measurable_pathExcursionCount b hε
  have h : (fun ω => (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞))
      = Φ ∘ driftIncr B 0 τ := by
    funext ω
    have hc : Continuous fun t => B (τ ω + t) ω - B (τ ω) ω :=
      ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
    rw [Function.comp_apply, driftIncr_zero, hΦJ _ hc]
  rw [h]
  exact hΦ.comp (measurable_driftIncr hm hcont 0 hτ)

/-- **The second moment of the restarted count.** For a real Brownian motion `B` with continuous paths, a finite
stopping time `τ` of the natural filtration and an event `E` of the past at `τ`, the second moment on `E` of the
excursion count of `B (τ + ·) - B τ` is `P E` times the second moment of the excursion count of `B`. -/
theorem setLIntegral_restart_pathExcursionCount_sq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    {E : Set Ω} (hE : MeasurableSet[hτ.measurableSpace] E) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω in E, (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞) ^ 2 ∂P
      = P E * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
  obtain ⟨Φ, hΦ, hΦJ⟩ := exists_measurable_pathExcursionCount b hε
  have h := lintegral_restrict_driftIncr hB hm hcont 0 τ hτ hE (hΦ.pow_const 2)
  have h2 : ∀ ω, (fun t : ℝ≥0 => B t ω + 0 * (t : ℝ)) = fun t => B t ω := by
    intro ω
    funext t
    simp
  calc ∫⁻ ω in E, (pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω in E, Φ (driftIncr B 0 τ ω) ^ 2 ∂P := by
        refine lintegral_congr fun ω => ?_
        have hc : Continuous fun t => B (τ ω + t) ω - B (τ ω) ω :=
          ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
        rw [driftIncr_zero, hΦJ _ hc]
    _ = P E * ∫⁻ ω, Φ (fun t : ℝ≥0 => B t ω + 0 * (t : ℝ)) ^ 2 ∂P := h
    _ = P E * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [h2, hΦJ _ (hcont ω)]

/-- **Factorisation of the mixed moment.** For a real Brownian motion `B` with continuous paths, levels `a, b`,
`ε > 0` and a horizon `N`, with `σ` the hitting time of `{B ≤ -a}` truncated at `N`: on the event `{σ < N}`, the
mixed moment of the count at level `a` and of the count at level `b` of the restarted motion `B (σ + ·) - B σ` is
the mean of the former on that event times the mean of the count of `B` at level `b`. -/
theorem setLIntegral_mul_restart_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a b : ℝ) {ε : ℝ} (hε : 0 < ε)
    (N : ℝ≥0) :
    ∫⁻ ω in {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞)},
        (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) *
          (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
            B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞) ∂P
      = (∫⁻ ω in {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞)},
          (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
  have hσ := isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a N
  have hJ' := measurable_restart_pathExcursionCount hm hcont (measurable_of_isStoppingTime_nnreal hm hσ) b hε
  have hX := measurableSet_le_pathExcursionCount hm hcont a hε
  have hterm : ∀ k : ℕ,
      ∫⁻ ω in {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) a ε},
          (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
            B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞)
            ∂(P.restrict {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞)})
        = (∫⁻ ω in {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) a ε}, 1
            ∂(P.restrict {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞)})) *
          ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P := by
    intro k
    obtain ⟨E, hE, hEeq⟩ := exists_measurableSet_hitDriftTrunc_le_pathExcursionCount hB hm hcont a hε N (k + 1)
    have hset : {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) a ε} ∩
        {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞)}
        = {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞) ∧
            k + 1 ≤ pathExcursionCount (fun t => B t ω) a ε} := by
      ext ω
      exact and_comm
    rw [Measure.restrict_restrict (hX (k + 1)), hset,
      setLIntegral_one, ← setLIntegral_congr hEeq, ← measure_congr hEeq]
    exact setLIntegral_restart_pathExcursionCount hB hm hcont _ hσ hE b hε
  rw [lintegral_natCast_mul_eq_tsum hX hJ', tsum_congr hterm, ENNReal.tsum_mul_right,
    ← lintegral_natCast_mul_eq_tsum hX measurable_const]
  simp only [mul_one]

/-- **Splitting of the second moment of the excursion count.** For a real Brownian motion `B` with continuous paths,
levels `a, b ≥ 0` and `ε > 0`, writing `J(c)` for the number of excursions above the running minimum of length larger
than `ε` completed before the first passage below `B 0 - c`,
`E [J(a + b)²] = E [J(a)²] + 2 E [J(a)] E [J(b)] + E [J(b)²]`. -/
theorem lintegral_pathExcursionCount_add_sq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 ∂P +
        2 * ((∫⁻ ω, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
          ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) +
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
  set A : ℕ → Set Ω := fun N => {ω | hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞)}
  have hτ := fun N : ℕ => isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a (N : ℝ≥0)
  have hA : ∀ N : ℕ, MeasurableSet[(hτ N).measurableSpace] (A N) := by
    intro N
    have h := (hτ N).measurableSet_lt' (N : ℝ≥0)
    convert h using 1
    ext ω
    change hitDrift (fun t ω => -B t ω) 0 a ω < ((N : ℝ≥0) : ℝ≥0∞) ↔
      ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞)
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
  have hN : ∀ N : ℕ, ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 ∂P +
        2 * ((∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
          ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) +
        P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
    intro N
    have hJ' := measurable_restart_pathExcursionCount (b := b) hm hcont
      (measurable_of_isStoppingTime_nnreal hm (hτ N)) hε
    have hX2 : Measurable fun ω => (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 := (hmeas a).pow_const 2
    have hprod : Measurable fun ω => (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) *
        (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
          B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞) := (hmeas a).mul hJ'
    have hsum : Measurable fun ω => (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 + 2 * ((pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) *
        (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
          B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞)) := hX2.add (hprod.const_mul 2)
    have e1 : ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ^ 2 ∂P =
        ∫⁻ ω in A N, ((pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 +
          2 * ((pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) *
            (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
              B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞))) +
          (pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
              B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
      refine setLIntegral_congr_fun_ae (hAm N) ?_
      filter_upwards [ae_pathExcursionCount_add_restart hB hm hcont ha hb hε (N : ℝ≥0)] with ω hω hωA
      rw [hω hωA.le, Nat.cast_add]
      ring
    rw [e1, lintegral_add_left hsum, lintegral_add_left hX2, lintegral_const_mul 2 hprod,
      setLIntegral_mul_restart_pathExcursionCount hB hm hcont a b hε (N : ℝ≥0),
      setLIntegral_restart_pathExcursionCount_sq hB hm hcont _ (hτ N) (hA N) b hε]
  have hXm : Monotone fun N : ℕ =>
      ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 ∂P :=
    fun N M hNM => lintegral_mono_set (hmono hNM)
  have hYm : Monotone fun N : ℕ =>
      2 * ((∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) :=
    fun N M hNM => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (lintegral_mono_set (hmono hNM)) zero_le) zero_le
  have hZm : Monotone fun N : ℕ =>
      P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P :=
    fun N M hNM => mul_le_mul_of_nonneg_right (measure_mono (hmono hNM)) zero_le
  have hY : ⨆ N : ℕ, 2 * ((∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) =
      2 * ((∫⁻ ω, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
        ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) := by
    rw [← ENNReal.mul_iSup, ← ENNReal.iSup_mul, hlim]
  have hZ : ⨆ N : ℕ, P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P := by
    rw [← ENNReal.iSup_mul, hP1, one_mul]
  calc ∫⁻ ω, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ^ 2 ∂P
      = ⨆ N, ∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) (a + b) ε : ℝ≥0∞) ^ 2 ∂P := (hlim _).symm
    _ = ⨆ N : ℕ, (∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 ∂P +
          2 * ((∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
            ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P) +
          P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P) := iSup_congr hN
    _ = (⨆ N : ℕ, (∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ^ 2 ∂P +
          2 * ((∫⁻ ω in A N, (pathExcursionCount (fun t => B t ω) a ε : ℝ≥0∞) ∂P) *
            ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ∂P))) +
          ⨆ N : ℕ, P (A N) * ∫⁻ ω, (pathExcursionCount (fun t => B t ω) b ε : ℝ≥0∞) ^ 2 ∂P :=
        (ENNReal.iSup_add_iSup_of_monotone (hXm.add hYm) hZm).symm
    _ = _ := by
        rw [← ENNReal.iSup_add_iSup_of_monotone hXm hYm, hlim, hY, hZ]

end LatticeProb.LadderSet
