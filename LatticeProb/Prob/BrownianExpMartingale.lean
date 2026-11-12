/-
The exponential martingale of Brownian motion with drift.

For a pre-Brownian motion `B` and a drift `c`, the process
`exp (-2 c (B t + c t))` is a martingale for the natural filtration of `B`:
the increment `B t - B s` is independent of the past (the weak Markov property)
and has the Gaussian law of variance `t - s`, whose exponential moment
cancels the drift.

Consequences used for gambler's-ruin estimates: Doob's maximal inequality on any
increasing sequence of times bounds the chance that `B t + c t` ever drops to `-δ`
by `exp (-2 c δ)`, and by path continuity along dyadic skeletons the same bound holds
for the whole half line.  No reflection principle and no continuous-time optional
stopping is used.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The natural filtration of a real process with measurable values. -/
def brownianFiltration (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t => (hm t).stronglyMeasurable)

/-- **Weak Markov property in filtration form.**  The increment of a pre-Brownian motion after
time `s` is independent of the natural σ-algebra at time `s`. -/
theorem brownian_indep_filtration_sub (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (brownianFiltration B hm s) (MeasurableSpace.comap (B t - B s) inferInstance) P := by
  have h := hB.indepFun_shift s
  rw [IndepFun_iff_Indep] at h
  have h1 : brownianFiltration B hm s =
      MeasurableSpace.comap (fun ω (j : Set.Iic s) => B j ω) inferInstance :=
    Filtration.natural_eq_comap _ _ s
  have hle : MeasurableSpace.comap (B t - B s) inferInstance ≤
      MeasurableSpace.comap (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω) inferInstance := by
    have heq : B t - B s =
        (fun f : ℝ≥0 → ℝ => f (t - s)) ∘ (fun ω (u : ℝ≥0) => B (s + u) ω - B s ω) := by
      ext ω
      simp [add_tsub_cancel_of_le hst]
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply (t - s)).comap_le
  rw [h1]
  exact (indep_of_indep_of_le_left h hle).symm


/-- The exponential moment of a pre-Brownian motion is finite. -/
theorem brownian_integrable_exp_mul (hB : IsPreBrownianReal B P) (a : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (a * B t ω)) P :=
  (hB.hasLaw_eval t).integrable_comp (integrable_exp_mul_gaussianReal a)

theorem brownian_integral_exp_mul (hB : IsPreBrownianReal B P) (a : ℝ) (t : ℝ≥0) :
    ∫ ω, Real.exp (a * B t ω) ∂P = Real.exp (t * a ^ 2 / 2) := by
  have h := mgf_gaussianReal (hB.hasLaw_eval t) a
  simp only [mgf] at h
  simpa using h

theorem brownian_integral_exp_mul_sub (hB : IsPreBrownianReal B P) (a : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, Real.exp (a * (B t ω - B s ω)) ∂P = Real.exp (((t : ℝ) - s) * a ^ 2 / 2) := by
  have h := mgf_gaussianReal (hB.hasLaw_sub t s) a
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (by exact_mod_cast hst)
  simp only [mgf] at h
  simpa [Real.dist_eq, abs_of_nonneg hts] using h

theorem brownian_integrable_exp_mul_sub (hB : IsPreBrownianReal B P) (a : ℝ)
    (s t : ℝ≥0) : Integrable (fun ω => Real.exp (a * (B t ω - B s ω))) P :=
  (hB.hasLaw_sub t s).integrable_comp (integrable_exp_mul_gaussianReal a)

/-- **The exponential martingale.**  For a pre-Brownian motion `B` with measurable values and any
real `c`, `exp (-2 c (B t + c t))` is a martingale for the natural filtration of `B`. -/
theorem martingale_exp_drift (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (c : ℝ) :
    Martingale (fun (t : ℝ≥0) ω => Real.exp (-(2 * c) * (B t ω + c * t)))
      (brownianFiltration B hm) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => ?_, fun s t hst => ?_⟩
  · exact (Real.continuous_exp.comp (by fun_prop :
      Continuous fun x : ℝ => -(2 * c) * (x + c * t))).comp_stronglyMeasurable
      (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) t)
  · -- decomposition `M t = M s * D`
    set D : Ω → ℝ := fun ω =>
      Real.exp (-(2 * c) * (B t ω - B s ω)) * Real.exp (-(2 * c ^ 2 * ((t : ℝ) - s))) with hD
    set M : ℝ≥0 → Ω → ℝ := fun t ω => Real.exp (-(2 * c) * (B t ω + c * t)) with hM
    have hsplit : M t = M s * D := by
      funext ω
      simp only [hM, hD, Pi.mul_apply, ← Real.exp_add]
      congr 1
      ring
    have hDint : Integrable D P :=
      (brownian_integrable_exp_mul_sub hB (-(2 * c)) s t).mul_const _
    have hDmean : ∫ ω, D ω ∂P = 1 := by
      simp only [hD]
      rw [integral_mul_const, brownian_integral_exp_mul_sub hB _ hst, ← Real.exp_add]
      rw [Real.exp_eq_one_iff]
      ring
    have hMs : StronglyMeasurable[brownianFiltration B hm s] (M s) :=
      (Real.continuous_exp.comp (by fun_prop :
        Continuous fun x : ℝ => -(2 * c) * (x + c * s))).comp_stronglyMeasurable
        (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) s)
    have hMt : Integrable (M t) P := by
      have : M t = fun ω => Real.exp (-(2 * c) * B t ω) * Real.exp (-(2 * c ^ 2 * t)) := by
        funext ω
        simp only [hM, ← Real.exp_add]
        congr 1
        ring
      rw [this]
      exact (brownian_integrable_exp_mul hB _ t).mul_const _
    have hDm : StronglyMeasurable[MeasurableSpace.comap (B t - B s) inferInstance] D := by
      have hmeas : Measurable[MeasurableSpace.comap (B t - B s) inferInstance] (B t - B s) :=
        comap_measurable _
      have : D = (fun x : ℝ => Real.exp (-(2 * c) * x) *
          Real.exp (-(2 * c ^ 2 * ((t : ℝ) - s)))) ∘ (B t - B s) := by
        funext ω
        simp [hD]
      rw [this]
      have hc : Continuous (fun x : ℝ => Real.exp (-(2 * c) * x) *
          Real.exp (-(2 * c ^ 2 * ((t : ℝ) - s)))) := by fun_prop
      exact hc.comp_stronglyMeasurable hmeas.stronglyMeasurable
    have hcond : (P)[D | brownianFiltration B hm s] =ᵐ[P] fun _ => ∫ ω, D ω ∂P :=
      condExp_indep_eq ((((hm t).sub (hm s))).comap_le) ((brownianFiltration B hm).le s) hDm
        (brownian_indep_filtration_sub hB hm hst).symm
    have hmul := condExp_mul_of_stronglyMeasurable_left hMs (hsplit ▸ hMt) hDint
    rw [hsplit]
    filter_upwards [hmul, hcond] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, hDmean, mul_one]


theorem integral_exp_drift (hB : IsPreBrownianReal B P) (c : ℝ) (t : ℝ≥0) :
    ∫ ω, Real.exp (-(2 * c) * (B t ω + c * t)) ∂P = 1 := by
  have : (fun ω => Real.exp (-(2 * c) * (B t ω + c * t))) =
      fun ω => Real.exp (-(2 * c) * B t ω) * Real.exp (-(2 * c ^ 2 * t)) := by
    funext ω
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [this, integral_mul_const, brownian_integral_exp_mul hB, ← Real.exp_add, Real.exp_eq_one_iff]
  ring

/-- **Doob's maximal inequality for Brownian motion with positive drift**, on an increasing
sequence of times: the chance that `B t + c t` is at most `-δ` at one of the times
`t 0, …, t n` is at most `exp (-2 c δ)`. -/
theorem measure_exists_drift_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    {c : ℝ} (hc : 0 < c) {t : ℕ → ℝ≥0} (ht : Monotone t) (n : ℕ) (δ : ℝ) :
    P {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ -δ} ≤ ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let 𝒢 : Filtration ℕ mΩ :=
    ⟨fun k => brownianFiltration B hm (t k), fun a b h => (brownianFiltration B hm).mono (ht h),
      fun k => (brownianFiltration B hm).le _⟩
  let f : ℕ → Ω → ℝ := fun k ω => Real.exp (-(2 * c) * (B (t k) ω + c * t k))
  have hmart : Martingale f 𝒢 P :=
    ⟨fun k => (martingale_exp_drift hB hm c).1 (t k),
      fun i j hij => (martingale_exp_drift hB hm c).2 (t i) (t j) (ht hij)⟩
  have hnn : 0 ≤ f := fun k ω => (Real.exp_pos _).le
  set ε : ℝ≥0 := (Real.exp (2 * c * δ)).toNNReal with hε
  have hεpos : (0 : ℝ) < ε := by
    rw [hε, Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_pos _
  have hmax := maximal_ineq hmart.submartingale hnn (ε := ε) n
  set S : Set Ω := {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => f k ω} with hS
  have hsub : {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ -δ} ⊆ S := by
    rintro ω ⟨k, hk, hX⟩
    have hk' : k ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω) hk')
    rw [hε, Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hint : ∫ ω in S, f n ω ∂P ≤ 1 := by
    calc ∫ ω in S, f n ω ∂P ≤ ∫ ω, f n ω ∂P :=
          setIntegral_le_integral
            (by
              have := (martingale_exp_drift hB hm c)
              exact ((hmart.integrable n))) (Filter.Eventually.of_forall (hnn n))
      _ = 1 := integral_exp_drift hB c (t n)
  have h1 : (ε : ℝ≥0∞) * P S ≤ 1 := by
    refine hmax.trans ?_
    calc ENNReal.ofReal (∫ ω in S, f n ω ∂P) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hint
      _ = 1 := ENNReal.ofReal_one
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := by
    have : (ε : ℝ≥0) ≠ 0 := by
      intro h
      rw [h] at hεpos
      simp at hεpos
    exact_mod_cast this
  have h2 : P S ≤ (ε : ℝ≥0∞)⁻¹ * 1 :=
    (ENNReal.mul_le_iff_le_inv hε0 ENNReal.coe_ne_top).1 h1
  have hεinv : (ε : ℝ≥0∞)⁻¹ = ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by
    rw [show (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (2 * c * δ)) from rfl,
      ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  calc P {ω | ∃ k ≤ n, B (t k) ω + c * t k ≤ -δ} ≤ P S := measure_mono hsub
    _ ≤ (ε : ℝ≥0∞)⁻¹ * 1 := h2
    _ = ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by rw [mul_one, hεinv]

/-- A continuous function which is below `a` at a point is below `a` at a dyadic point
`k / 2 ^ N` with `k ≤ N 2 ^ N`. -/
theorem exists_dyadic_lt_of_continuous {g : ℝ≥0 → ℝ} (hg : Continuous g) {a : ℝ} {t : ℝ≥0}
    (ht : g t < a) : ∃ N k : ℕ, k ≤ N * 2 ^ N ∧ g ((k : ℝ≥0) / 2 ^ N) < a := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt hg continuous_const) t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((t : ℝ) + 1) (1 / ε))
  have hN1 : (t : ℝ) + 1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 1 / ε < N := lt_of_le_of_lt (le_max_right _ _) hN
  have h2N : (N : ℝ) < 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self (n := N)
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN1
  refine ⟨N, ⌊(t : ℝ) * 2 ^ N⌋₊, ?_, hball ?_⟩
  · refine Nat.floor_le_of_le ?_
    have : (t : ℝ) ≤ N := by linarith
    calc (t : ℝ) * 2 ^ N ≤ N * 2 ^ N := by gcongr
      _ = ((N * 2 ^ N : ℕ) : ℝ) := by push_cast; ring
  · rw [Metric.mem_ball, NNReal.dist_eq]
    have hk1 : (⌊(t : ℝ) * 2 ^ N⌋₊ : ℝ) ≤ t * 2 ^ N := Nat.floor_le (by positivity)
    have hk2 : (t : ℝ) * 2 ^ N < ⌊(t : ℝ) * 2 ^ N⌋₊ + 1 := Nat.lt_floor_add_one _
    have hc : (((⌊(t : ℝ) * 2 ^ N⌋₊ : ℝ≥0) / 2 ^ N : ℝ≥0) : ℝ) = ⌊(t : ℝ) * 2 ^ N⌋₊ / 2 ^ N := by
      push_cast; rfl
    rw [hc, abs_sub_comm, abs_of_nonneg]
    · have : (t : ℝ) - ⌊(t : ℝ) * 2 ^ N⌋₊ / 2 ^ N < 1 / 2 ^ N := by
        rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hpos]
        linarith
      refine lt_of_lt_of_le this ?_
      have : 1 / (2 : ℝ) ^ N < ε := by
        rw [div_lt_iff₀ hpos]
        have : 1 / ε < 2 ^ N := hN2.trans h2N
        rw [div_lt_iff₀ hε] at this
        linarith
      exact this.le
    · rw [sub_nonneg, div_le_iff₀ hpos]
      exact hk1

/-- **Gambler's ruin, one half.**  If every path of `B` is continuous and `c > 0`, then the chance
that `B t + c t` ever goes below `-δ` is at most `exp (-2 c δ)`. -/
theorem measure_exists_drift_lt_le (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {c : ℝ} (hc : 0 < c) (δ : ℝ) :
    P {ω | ∃ t : ℝ≥0, B t ω + c * t < -δ} ≤ ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by
  let g : ℕ → ℕ → ℝ≥0 := fun N k => (k : ℝ≥0) / 2 ^ N
  have hg : ∀ N, Monotone (g N) := fun N a b h => by
    simp only [g]
    gcongr
  let A : ℕ → Set Ω := fun N => {ω | ∃ k ≤ N * 2 ^ N, B (g N k) ω + c * g N k ≤ -δ}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun N ω hω => ?_
    obtain ⟨k, hk, hX⟩ := hω
    refine ⟨2 * k, ?_, ?_⟩
    · calc 2 * k ≤ 2 * (N * 2 ^ N) := by omega
        _ ≤ (N + 1) * 2 ^ (N + 1) := by rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ N)]
    · have : g (N + 1) (2 * k) = g N k := by
        simp only [g]
        push_cast
        rw [pow_succ]
        field_simp
      rw [this]
      exact hX
  have hsub : {ω | ∃ t : ℝ≥0, B t ω + c * t < -δ} ⊆ ⋃ N, A N := by
    rintro ω ⟨t, ht⟩
    obtain ⟨N, k, hk, hlt⟩ := exists_dyadic_lt_of_continuous
      (g := fun u : ℝ≥0 => B u ω + c * u) (by have := hcont ω; fun_prop) ht
    exact Set.mem_iUnion.2 ⟨N, k, hk, hlt.le⟩
  calc P {ω | ∃ t : ℝ≥0, B t ω + c * t < -δ} ≤ P (⋃ N, A N) := measure_mono hsub
    _ = ⨆ N, P (A N) := hAmono.measure_iUnion
    _ ≤ _ := iSup_le fun N => measure_exists_drift_le hB hm hc (hg N) (N * 2 ^ N) δ

end LatticeProb
