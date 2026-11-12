import LatticeProb.Prob.RunningMinHits
import LatticeProb.Prob.BrownianLevyReflection
import LatticeProb.Prob.BrownianExpMartingale
import LatticeProb.Prob.RenewalCount

/-!
# Running-minimum hits of Brownian motion: the escape bound

Let `B` be a Brownian motion with continuous paths.  Call `k` a *hit* when the unit interval
`[k - 1, k]` contains a running-minimum time of `B` (`IsRunningMinHit`).  The hit event is an event
of the natural σ-algebra at time `k` (`measurableSet_runningMinHitSet`).  After time `k`, a hit at
some `j ≥ k + 2` forces the motion restarted at time `k` to come back, during `[1, n]`, below its
minimum over `[0, 1]`.  By the Markov property at the deterministic time `k` this has conditional
probability at most `1 - c₁ / (32 √n)` with `c₁ = P (N(0, 1) ≥ 1)`
(`measure_inter_iUnion_runningMinHitSet_le`).

The lower bound `c₁ / (32 √n)` for the escape probability (`measure_mem_returnSet_le`) comes from
the Markov property at time `1`: the motion gains `1` during `[0, 1]` with probability `c₁`, and
afterwards stays above `-1/2` during `[1, 1 + n]` with probability at least `1 / (32 √n)` by
Lévy's reflection inequality (`le_measure_forall_ge_neg`).

## Main results

* `measure_inter_shift_mem`: the weak Markov property at a deterministic time, for events of the
  natural filtration.
* `measure_mem_returnSet_le`: the escape bound.
* `measure_inter_iUnion_runningMinHitSet_le`: the conditional escape bound after a time `k`.
* `exists_measure_lt_card_runningMinHits_le`: the number of hits among `1, …, n` has an
  exponential tail on the scale `√n`: `P (m < #hits) ≤ C exp (-c m / √n)`.

The last bound is the running-minimum estimate of Berestycki and Gwynne (random walks on mated-CRT
maps, Lemma A.9) for a standard Brownian motion.  The proof uses only the Markov property at
deterministic integer times: by the conditional escape bound and the geometric tail for adapted
hit counts (`measure_two_mul_add_one_le_card_hits_le`), `2 j + 1` hits have probability at most
`(1 - c₁ / (32 √n)) ^ j`.
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

universe u

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### Paths staying above a level at dyadic times -/

/-- The paths staying above `-a` at the dyadic times of `[0, T]`. -/
def dyadicStaySet (T : ℝ≥0) (a : ℝ) : Set (ℝ≥0 → ℝ) :=
  {w | ∀ N i : ℕ, dyadicGrid N i ≤ T → -a ≤ w (dyadicGrid N i)}

theorem measurableSet_dyadicStaySet (T : ℝ≥0) (a : ℝ) : MeasurableSet (dyadicStaySet T a) := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun N => Measurable.forall fun i => ?_)
  by_cases h : dyadicGrid N i ≤ T
  · simp only [h, true_imp_iff]
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_pi_apply _))
  · simp only [h, false_imp_iff]
    exact measurable_const

/-- For a continuous path, staying above `-a` at the dyadic times of `[0, T]` is staying above
`-a` on `[0, T]`. -/
theorem mem_dyadicStaySet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) {T : ℝ≥0} {a : ℝ} :
    w ∈ dyadicStaySet T a ↔ ∀ s ≤ T, -a ≤ w s := by
  refine ⟨fun h s hs => ?_, fun h N i hi => h _ hi⟩
  exact ge_of_tendsto ((hw.tendsto s).comp (tendsto_dyadicGrid_floor s))
    (Eventually.of_forall fun N => h N _ ((dyadicGrid_floor_le s N).trans hs))

/-! ### The weak Markov property at a deterministic time -/

theorem measurable_brownianFiltration (hm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[brownianFiltration B hm t] (B s) :=
  ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) s).mono
    ((brownianFiltration B hm).mono hst)).measurable

/-- **Weak Markov property.**  An event of the natural σ-algebra at time `v` is independent of
every measurable event of the motion restarted at time `v`. -/
theorem measure_inter_shift_mem (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (v : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[brownianFiltration B hm v] A)
    {Γ : Set (ℝ≥0 → ℝ)} (hΓ : MeasurableSet Γ) :
    P (A ∩ {ω | (fun t => B (v + t) ω - B v ω) ∈ Γ}) =
      P A * P {ω | (fun t => B (v + t) ω - B v ω) ∈ Γ} := by
  have hind := (IndepFun_iff_Indep _ _ _).1 (hB.indepFun_shift v)
  have hAc : MeasurableSet[MeasurableSpace.comap (fun ω (s : Set.Iic v) => B (s : ℝ≥0) ω)
      inferInstance] A := by
    rwa [brownianFiltration, Filtration.natural_eq_comap] at hA
  have hΓc : MeasurableSet[MeasurableSpace.comap (fun ω (t : ℝ≥0) => B (v + t) ω - B v ω)
      inferInstance] {ω | (fun t => B (v + t) ω - B v ω) ∈ Γ} := ⟨Γ, hΓ, rfl⟩
  rw [Set.inter_comm, (Indep_iff _ _ _).1 hind _ _ hΓc hAc, mul_comm]

/-! ### Hits -/

/-- The event that `[k - 1, k]` contains a running-minimum time of `B`. -/
def runningMinHitSet (B : ℝ≥0 → Ω → ℝ) (k : ℕ) : Set Ω :=
  {ω | IsRunningMinHit (fun t => B t ω) k}

/-- For continuous paths, the hit event of `[k - 1, k]` is an event of the natural σ-algebra at
time `k`. -/
theorem measurableSet_runningMinHitSet (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (k : ℕ) :
    MeasurableSet[brownianFiltration B hm k] (runningMinHitSet B k) := by
  have hk : ((k - 1 : ℕ) : ℝ≥0) ≤ (k : ℝ≥0) := by exact_mod_cast Nat.sub_le k 1
  have h : runningMinHitSet B k = {ω | DyadicMinBefore (fun t => B t ω)
      ((k - 1 : ℕ) : ℝ≥0) k ((k - 1 : ℕ) : ℝ≥0)} := by
    ext ω
    exact isRunningMinHit_iff (hcont ω) k
  rw [h]
  exact measurableSet_dyadicMinBefore (m := brownianFiltration B hm k) le_rfl hk
    fun s hs => measurable_brownianFiltration hm hs

/-! ### The escape bound -/

/-- **Escape bound.**  A Brownian motion comes back, during `[1, n]`, below its minimum over
`[0, 1]` with probability at most `1 - c₁ / (32 √n)`, where `c₁ = P (N(0, 1) ≥ 1)`. -/
theorem measure_mem_returnSet_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {n : ℕ} (hn : 1 ≤ n) :
    P {ω | (fun t => B t ω) ∈ returnSet n} ≤
      1 - gaussianReal 0 1 (Set.Ici 1) * ENNReal.ofReal (1 / (32 * Real.sqrt n)) := by
  have hcs : ∀ ω, Continuous fun t => B (1 + t) ω - B 1 ω := fun ω =>
    ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hA : MeasurableSet[brownianFiltration B hm 1] {ω | 1 ≤ B 1 ω - B 0 ω} :=
    ((measurable_brownianFiltration hm le_rfl).sub
      (measurable_brownianFiltration hm zero_le_one)) measurableSet_Ici
  have hSm : MeasurableSet {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)} :=
    (Measurable.of_eval fun t => (hm (1 + t)).sub (hm 1)) (measurableSet_dyadicStaySet _ _)
  have hEm : MeasurableSet ({ω | 1 ≤ B 1 ω - B 0 ω} ∩
      {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)}) :=
    ((brownianFiltration B hm).le 1 _ hA).inter hSm
  have hE : {ω | (fun t => B t ω) ∈ returnSet n} ⊆ ({ω | 1 ≤ B 1 ω - B 0 ω} ∩
      {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)})ᶜ := by
    rintro ω hωR ⟨hωA, hωS⟩
    have hA' : 1 ≤ B 1 ω - B 0 ω := hωA
    have hstay := (mem_dyadicStaySet_iff (hcs ω)).1 hωS
    refine notMem_returnSet_of_forall (w := fun t => B t ω) (δ := 1 / 2) (by norm_num)
      (fun u hu1 hun => ?_) hωR
    have h1 := hstay (u - 1) (tsub_le_self.trans hun)
    simp only [add_tsub_cancel_of_le hu1] at h1
    linarith
  have hprod := measure_inter_shift_mem hB.toIsPreBrownianReal hm 1 hA
    (measurableSet_dyadicStaySet (n : ℝ≥0) (1 / 2))
  have hPA : P {ω | 1 ≤ B 1 ω - B 0 ω} = gaussianReal 0 1 (Set.Ici 1) := by
    have h : HasLaw (B 1 - B 0) (gaussianReal 0 1) P := by
      convert hB.toIsPreBrownianReal.hasLaw_sub 1 0 using 2
      simp
    rw [← h.map_eq, Measure.map_apply ((hm 1).sub (hm 0)) measurableSet_Ici]
    rfl
  have hPS : ENNReal.ofReal (1 / (32 * Real.sqrt n)) ≤
      P {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)} := by
    have haT : (1 / 2 : ℝ) ^ 2 ≤ ((n : ℝ≥0) : ℝ) := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [NNReal.coe_natCast]
      nlinarith
    have h := le_measure_forall_ge_neg (hB.shift 1) (fun t => (hm _).sub (hm _))
      (T := n) (a := 1 / 2) (by norm_num) haT
    convert h using 2
    · rw [NNReal.coe_natCast]
      ring
    · ext ω
      simp only [Set.mem_ofPred_eq]
      rw [mem_dyadicStaySet_iff (hcs ω)]
      simp only [add_zero, sub_self, sub_zero]
  have hlow : gaussianReal 0 1 (Set.Ici 1) * ENNReal.ofReal (1 / (32 * Real.sqrt n)) ≤
      P ({ω | 1 ≤ B 1 ω - B 0 ω} ∩
        {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)}) := by
    rw [hprod, hPA]
    gcongr
  calc P {ω | (fun t => B t ω) ∈ returnSet n}
      ≤ P ({ω | 1 ≤ B 1 ω - B 0 ω} ∩
          {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)})ᶜ := measure_mono hE
    _ = 1 - P ({ω | 1 ≤ B 1 ω - B 0 ω} ∩
          {ω | (fun t => B (1 + t) ω - B 1 ω) ∈ dyadicStaySet n (1 / 2)}) :=
        prob_compl_eq_one_sub hEm
    _ ≤ _ := tsub_le_tsub_left hlow 1

/-- **Conditional escape bound.**  For an event `A` of the natural σ-algebra at time `k`, the
chance that `A` occurs and some `j ∈ [k + 2, n]` is a hit is at most `1 - c₁ / (32 √n)` times
`P A`. -/
theorem measure_inter_iUnion_runningMinHitSet_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {A : Set Ω}
    (hA : MeasurableSet[brownianFiltration B hm k] A) :
    P (A ∩ ⋃ j ∈ Finset.Icc (k + 2) n, runningMinHitSet B j) ≤
      (1 - gaussianReal 0 1 (Set.Ici 1) * ENNReal.ofReal (1 / (32 * Real.sqrt n))) * P A := by
  have hsub : A ∩ ⋃ j ∈ Finset.Icc (k + 2) n, runningMinHitSet B j ⊆
      A ∩ {ω | (fun t => B (k + t) ω - B k ω) ∈ returnSet n} := by
    rintro ω ⟨hωA, hω⟩
    simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop] at hω
    obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := hω
    exact ⟨hωA, shift_mem_returnSet_of_isRunningMinHit (hcont ω) hj1 hj2 hj⟩
  have hcs : ∀ ω, Continuous fun t => B (k + t) ω - B k ω := fun ω =>
    ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
  calc P (A ∩ ⋃ j ∈ Finset.Icc (k + 2) n, runningMinHitSet B j)
      ≤ P (A ∩ {ω | (fun t => B (k + t) ω - B k ω) ∈ returnSet n}) := measure_mono hsub
    _ = P A * P {ω | (fun t => B (k + t) ω - B k ω) ∈ returnSet n} :=
        measure_inter_shift_mem hB.toIsPreBrownianReal hm k hA (measurableSet_returnSet n)
    _ ≤ P A * (1 - gaussianReal 0 1 (Set.Ici 1) *
          ENNReal.ofReal (1 / (32 * Real.sqrt n))) := by
        gcongr
        exact measure_mem_returnSet_le (hB.shift k) (fun t => (hm _).sub (hm _)) hcs hn
    _ = _ := mul_comm _ _

/-! ### The number of hits -/

open Classical in
/-- The hits among `1, …, n`: the `k ∈ [1, n]` such that `[k - 1, k]` contains a running-minimum
time of `B`. -/
def runningMinHits (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k => ω ∈ runningMinHitSet B k

theorem gaussianReal_Ici_one_pos : 0 < (gaussianReal 0 1 (Set.Ici (1 : ℝ))).toReal := by
  refine ENNReal.toReal_pos (fun h => ?_) (measure_ne_top _ _)
  have h' := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  simp at h'

open Classical in
/-- **Running-minimum hits of Brownian motion.**  The number of unit intervals `[k - 1, k]`,
`1 ≤ k ≤ n`, containing a running-minimum time of a Brownian motion has an exponential tail on the
scale `√n`. -/
theorem exists_measure_lt_card_runningMinHits_le : ∃ C c : ℝ, 0 < c ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      (∀ t, Measurable (B t)) → (∀ ω, Continuous fun t => B t ω) → ∀ n : ℕ, 1 ≤ n → ∀ m : ℝ,
      P {ω | m < ((runningMinHits B n ω).card : ℝ)} ≤
        ENNReal.ofReal (C * Real.exp (-(c * m / Real.sqrt n))) := by
  obtain ⟨c₁, hg, hc₁pos, hc₁le⟩ : ∃ c : ℝ, gaussianReal 0 1 (Set.Ici (1 : ℝ)) =
      ENNReal.ofReal c ∧ 0 < c ∧ c ≤ 1 :=
    ⟨_, (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm, gaussianReal_Ici_one_pos,
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩
  refine ⟨Real.exp 1, c₁ / 64, by positivity, ?_⟩
  intro Ω _ P B hB hm hcont n hn m
  have := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hsn : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hx0 : 0 ≤ 1 / (32 * Real.sqrt n) := by positivity
  have hx1 : 1 / (32 * Real.sqrt n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hδ0 : 0 ≤ c₁ * (1 / (32 * Real.sqrt n)) := mul_nonneg hc₁pos.le hx0
  have hδ1 : c₁ * (1 / (32 * Real.sqrt n)) ≤ 1 := by
    calc c₁ * (1 / (32 * Real.sqrt n)) ≤ 1 * 1 := mul_le_mul hc₁le hx1 hx0 zero_le_one
      _ = 1 := one_mul 1
  rcases lt_or_ge m 0 with hm0 | hm0
  · calc P {ω | m < ((runningMinHits B n ω).card : ℝ)} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
        have h3 : c₁ / 64 * m / Real.sqrt n ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by positivity) hm0.le) (by positivity)
        have h2 : 1 ≤ Real.exp (-(c₁ / 64 * m / Real.sqrt n)) := Real.one_le_exp (by linarith)
        nlinarith
  have hren := measure_two_mul_add_one_le_card_hits_le (P := P)
    (fun k : ℕ => brownianFiltration B hm (k : ℝ≥0))
    (fun i j hij => (brownianFiltration B hm).mono (Nat.cast_le.2 hij))
    (fun k => (brownianFiltration B hm).le _) (runningMinHitSet B)
    (measurableSet_runningMinHitSet hm hcont) n
    (fun k _ A hA => measure_inter_iUnion_runningMinHitSet_le hB hm hcont hn k hA) (⌊m⌋₊ / 2)
  rw [hg, ← ENNReal.ofReal_mul hc₁pos.le, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hδ0,
    ← ENNReal.ofReal_pow (by linarith)] at hren
  have hsub : {ω | m < ((runningMinHits B n ω).card : ℝ)} ⊆
      {ω | 2 * (⌊m⌋₊ / 2) + 1 ≤
        ((Finset.Icc 1 n).filter fun k => ω ∈ runningMinHitSet B k).card} := by
    intro ω hω
    have h1 : ⌊m⌋₊ < (runningMinHits B n ω).card := (Nat.floor_lt hm0).2 hω
    show 2 * (⌊m⌋₊ / 2) + 1 ≤ (runningMinHits B n ω).card
    omega
  have hjm : m - 2 ≤ 2 * ((⌊m⌋₊ / 2 : ℕ) : ℝ) := by
    have h1 : m < (⌊m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one m
    have h2 : ⌊m⌋₊ ≤ 2 * (⌊m⌋₊ / 2) + 1 := by omega
    have h3 : (⌊m⌋₊ : ℝ) ≤ 2 * ((⌊m⌋₊ / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
    linarith
  refine (measure_mono hsub).trans (hren.trans (ENNReal.ofReal_le_ofReal ?_))
  set δ := c₁ * (1 / (32 * Real.sqrt n)) with hδ
  set j := ⌊m⌋₊ / 2 with hj
  have key : c₁ / 64 * m / Real.sqrt n = δ * m / 2 := by
    rw [hδ]
    ring
  have hprod : δ * m - 2 * δ ≤ 2 * (δ * j) := by
    nlinarith [mul_le_mul_of_nonneg_left hjm hδ0]
  calc (1 - δ) ^ j ≤ Real.exp (-δ) ^ j :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg δ) j
    _ = Real.exp (-(δ * j)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ Real.exp (1 + -(c₁ / 64 * m / Real.sqrt n)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp 1 * Real.exp (-(c₁ / 64 * m / Real.sqrt n)) := Real.exp_add _ _

end LatticeProb
