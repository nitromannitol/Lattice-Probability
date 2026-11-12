/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.OccupationHit at commit fdb5cad; only the module paths of local imports are changed.
   Changed for Lean v4.35: set_option autoImplicit true after the imports, the default of the source repository (this library disables it).
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.Occupation
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.MarkovHit

set_option autoImplicit true

/-!
Second half of node W3 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), towards the two items
`occDens_nonneg_const` and `prob_hit_neg`. This file contains the ingredients that do not use the
strong Markov property:

* `hitLevel_mem` / `lt_hitLevel_of_pos` / `hitLevel_lt_of_neg`: a continuous path started at
  `0` that hits the level `a` hits it *at* `hitLevel`, and before that time it stays strictly on
  the side of `0` (`a > 0` below `a`, `a < 0` above `a`). Own elementary proofs (intermediate
  value theorem).
* `lintegral_Ioi_add`: translation invariance of `∫⁻` over `(c, ∞)` for Lebesgue measure.
* `measurableSet_exists_dpath_eq`: the event `{ω | ∃ t, Y t ω = a}` is measurable. The argument
  is the one of `strongMarkov_hit` (`MarkovHit.lean`): `{∃t, Y t = a}` is the union over `n` of
  the events `{Y (hittingBtwn Y {a} 0 n) = a}`, which are measurable as stopped values.
* `ae_exists_eq_level`: for `σ, μ > 0` the drift Brownian motion hits every level `x > 0` almost
  surely (it drifts to `+∞`). Chebyshev at integer times, as in `WedgeTrans.ae_exists_below`.
* `lintegral_Ioi_indicator_restart`: the key pointwise identity: if the indicator of `T` vanishes
  on the part of the path strictly before the first hitting time `τ` of the level `a`, then the
  occupation integral of `T` equals the occupation integral, over the restarted path
  `u ↦ w (τ + u) − a`, of `T` shifted by `-a` (`T - a := {z | z + a ∈ T}`). The time `τ` itself
  contributes nothing, because a single point is Lebesgue-null.
* `occDens_pos_zero`: for `σ, μ > 0` the occupation density at the origin is positive.
* `lt_of_not_exists_eq`: a continuous path started at `0` above a level `y < 0` that never hits
  `y` stays above it.
* `measurable_dpath_hitLevel_add` / `measurable_uncurry_dpath_hitLevel`: the shift
  `u ↦ Y_{τ(ω)+u}(ω)` is measurable in `ω` for each fixed `u`, and jointly measurable in
  `(ω, u)`. The proof approximates the shifted *path* by
  `u ↦ (if hittingBtwn Y {a} 0 n = n then Y u else Y (hittingBtwn Y {a} 0 n + u))`: mathlib's
  `hittingBtwn u s n m x` takes the junk value `m` (the *upper* bound) when `s` is not hit in
  `[n, m]`, so the capped hitting times alone do not converge pointwise to `hitLevel`; the `if`
  sends the non-hitting case to `Y u = Y (0 + u)` (`hitLevel` has junk value `0`). The limit is
  measurable by `measurable_of_tendsto_metrizable`, and joint measurability follows from
  continuity in `u` (`measurable_uncurry_of_continuous_of_measurable`).
* `eqOn_Ioi_of_integral_Ioc_eq`: if two continuous functions have equal integrals over every
  interval `(a, b)` with `0 < a < b`, then they are equal on `(0, ∞)`; this is the blueprint's
  "the densities agree a.e., then everywhere by continuity", proved directly by differentiating
  with the fundamental theorem of calculus.

**Not yet formalized here** (the two remaining steps towards `occDens_nonneg_const` and
`prob_hit_neg`): (i) the strong Markov (Tonelli) step giving the measure identity
`occ σ μ T = P {ω | ∃t, Y t = a} * occ σ μ (T - a)` for Borel `T` on the correct side of `a`
(in the positive case `T ⊆ (a, ∞)`, with `P {∃t, Y t = a} = 1` by `ae_exists_eq_level`; in the
negative case `a < 0` and `T ⊆ (-∞, a]`, with the factor `P {∃t, Y t = a}` left symbolic). The
ingredients are all present: apply `strongMarkov_hit` with the constant past functional `A ≡ 1`
and the functional `G_r(w) = T.indicator 1 (w r)` for the fixed shift `r = u.toNNReal`, giving
`∫_{ω∈E} 1_T (Y_{τ+r} − a) = P E · ∫_ω 1_T (Y_r)`; integrate over `u ∈ (0, ∞)` (Tonelli, using
`measurable_uncurry_dpath_hitLevel` for the joint measurability) and use
`lintegral_Ioi_indicator_restart` pointwise to identify the left side with `occ σ μ T`, and
`occ_eq_lintegral` twice (plus `lintegral_const_mul`) on the right. (ii) With the measure
identity at hand, `eqOn_Ioi_of_integral_Ioc_eq` applied to `occDens σ μ (·+a)` and
`P {∃t, Y t = a} · occDens σ μ` converts it into the pointwise identity
`occDens σ μ (z+a) = P {∃t, Y t = a} * occDens σ μ z` for `z > 0`; letting `z ↓ 0` in the
positive case (and `z ↑ a` in the negative case) with `continuous_occDens` gives
`occDens_nonneg_const` (using `ae_exists_eq_level`) and, together with `occDens_pos_zero`, the
statement of `prob_hit_neg` (note `P.real s = (P s).toReal` and `P {∃t, Y t = a} ≤ 1`).

Sources: Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. VI §1 (local time,
occupation densities) and Ch. VII Prop 3.2, printed pp. 301–302 (hitting probabilities). The
Chebyshev argument is that of
`WedgeTrans.ae_exists_below`; the rest is own bookkeeping.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ}

/-! ## Deterministic facts about the first hitting time -/

/-- A continuous path that hits the level `a` hits it at `hitLevel`. -/
theorem hitLevel_mem {w : ℝ≥0 → ℝ} (hw : Continuous w) {a : ℝ} (h : ∃ t, w t = a) :
    w (hitLevel w a) = a :=
  (isClosed_singleton.preimage hw).csInf_mem h (OrderBot.bddBelow _)

/-- Before the first hitting time of a *negative* level `a`, a continuous path started at `0`
stays strictly above `a`. Own elementary proof (intermediate value theorem). -/
theorem hitLevel_lt_of_neg {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {a : ℝ}
    (ha : a < 0) {m : ℝ≥0} (hm : m < hitLevel w a) : a < w m := by
  by_contra h
  push_neg at h
  obtain ⟨s, hs, hsa⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ m by simp)
    hw.continuousOn (show a ∈ Icc (w m) (w 0) from ⟨h, by rw [hw0]; exact ha.le⟩)
  have hle : hitLevel w a ≤ m :=
    (csInf_le (OrderBot.bddBelow ({t : ℝ≥0 | w t = a})) hsa).trans hs.2
  exact absurd hle (not_le.2 hm)

/-! ## Translation invariance of the integral over a half-line -/

/-- Shift of the integral over `(c, ∞)`: `∫_{c}^{∞} f = ∫_0^∞ f (c + ·)`. -/
theorem lintegral_Ioi_add (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ m in Set.Ioi c, f m = ∫⁻ u in Set.Ioi 0, f (c + u) := by
  have h : ∀ m : ℝ, (Set.Ioi c).indicator f (c + m)
      = (Set.Ioi 0).indicator (fun u => f (c + u)) m := by
    intro m
    by_cases hm : (0 : ℝ) < m
    · rw [Set.indicator_of_mem (Set.mem_Ioi.2 (by linarith)),
        Set.indicator_of_mem (Set.mem_Ioi.2 hm)]
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; linarith),
        Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact not_lt.1 hm)]
  calc ∫⁻ m in Set.Ioi c, f m
      = ∫⁻ m, (Set.Ioi c).indicator f m := (lintegral_indicator measurableSet_Ioi f).symm
    _ = ∫⁻ m, (Set.Ioi c).indicator f (c + m) := (lintegral_add_left_eq_self _ c).symm
    _ = ∫⁻ m, (Set.Ioi 0).indicator (fun u => f (c + u)) m := lintegral_congr h
    _ = ∫⁻ m in Set.Ioi 0, f (c + m) := lintegral_indicator measurableSet_Ioi _

/-! ## Measurability of the event that a level is hit -/

/-- **The event that the drift path hits the level `a` is measurable.** Same argument as in
`strongMarkov_hit`: it is the union over `n` of the events `{Y (hittingBtwn Y {a} 0 n) = a}`,
which are measurable as stopped values. -/
theorem measurableSet_exists_dpath_eq (hb : GoodBM b P) (σ μ a : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a} := by
  have hAd : Adapted (pastFilt b hb.meas) (fun t (ω : Ω) => dpath σ μ b ω t) := fun t =>
    ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
      ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
  have hprog : IsStronglyProgressive (pastFilt b hb.meas)
      (fun t (ω : Ω) => dpath σ μ b ω t) :=
    hAd.stronglyAdapted.isStronglyProgressive_of_continuous (continuous_dpath hb σ μ)
  have hstopn (n : ℕ) : IsStoppingTime (pastFilt b hb.meas)
      (fun ω => ((hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω : ℝ≥0) :
        WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := pastFilt b hb.meas) hAd
      (continuous_dpath hb σ μ) (isClosed_singleton (x := a)) (n : ℝ≥0)
  have hEnm (n : ℕ) : MeasurableSet
      {ω | dpath σ μ b ω (hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω)
        = a} := by
    have h := (measurable_stoppedValue hprog (hstopn n)).mono (hstopn n).measurableSpace_le le_rfl
    have h2 := h (measurableSet_singleton a)
    convert h2 using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_preimage,
      MeasureTheory.stoppedValue, untopA_coe_nnreal]
  have hunion : {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a}
      = ⋃ n : ℕ, {ω | dpath σ μ b ω
          (hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω) = a} := by
    ext ω
    constructor
    · rintro ⟨t, ht⟩
      refine Set.mem_iUnion.mpr ⟨⌈(t : ℝ)⌉₊, ?_⟩
      have htle : t ≤ (⌈(t : ℝ)⌉₊ : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]
        push_cast
        exact Nat.le_ceil (t : ℝ)
      exact mem_hittingBtwn_of_isClosed (u := fun t (ω : Ω) => dpath σ μ b ω t)
        (continuous_dpath hb σ μ) (isClosed_singleton (x := a))
        ⟨t, Set.mem_Icc.mpr ⟨zero_le, htle⟩, ht⟩
    · rintro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
      exact ⟨_, hn⟩
  rw [hunion]
  exact MeasurableSet.iUnion hEnm

/-! ## The drift Brownian motion hits every positive level -/

/-- **The drift Brownian motion hits every level `x > 0` almost surely** (it drifts to `+∞`
because `μ > 0`). Chebyshev at integer times, as in `WedgeTrans.ae_exists_below`: if the level is
never hit then the path is below `x` at every integer time, and `P(Y n < x) ≤ n σ²/(μ n − x)²`. -/
theorem ae_exists_eq_level (hb : GoodBM b P) {σ μ x : ℝ} (hσ : 0 < σ) (hμ : 0 < μ)
    (hx : 0 < x) : ∀ᵐ ω ∂P, ∃ t : ℝ≥0, dpath σ μ b ω t = x := by
  haveI : IsProbabilityMeasure P := hb.pre.isGaussianProcess.isProbabilityMeasure
  rw [ae_iff]
  set F : Set Ω := {ω | ¬ ∃ t : ℝ≥0, dpath σ μ b ω t = x} with hF
  have hsub : F ⊆ {ω | ∀ n : ℕ, dpath σ μ b ω n < x} := by
    intro ω hω n
    by_contra h
    push_neg at h
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ (n : ℝ≥0) by simp)
      (continuous_dpath hb σ μ ω).continuousOn
      (show x ∈ Icc (dpath σ μ b ω 0) (dpath σ μ b ω n) from
        ⟨by simp [dpath, hb.zero ω]; exact hx.le, h⟩)
    exact hω ⟨s, hs⟩
  have hbound : ∀ n : ℕ, 2 * x / μ ≤ n → 1 ≤ n →
      P F ≤ ENNReal.ofReal ((4 * σ ^ 2 / μ ^ 2) / n) := by
    intro n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h2x : 2 * x ≤ μ * n := by
      rw [div_le_iff₀ hμ] at hn; linarith
    have hmn : μ * n / 2 ≤ μ * n - x := by linarith
    set c : ℝ := (μ * n - x) / σ with hc
    have hc0 : 0 < c := by rw [hc]; exact div_pos (by linarith) hσ
    have hsub2 : F ⊆ {ω | c ≤ |b n ω - P[b n]|} := by
      intro ω hω
      have h1 : σ * b n ω + μ * (n : ℝ) < x := hsub hω n
      rw [hb.pre.integral_eval n]
      simp only [sub_zero]
      have hbn : b n ω < (x - μ * (n : ℝ)) / σ := by
        rw [lt_div_iff₀ hσ]
        nlinarith [h1]
      rw [hc, show (μ * (n : ℝ) - x) / σ = -((x - μ * (n : ℝ)) / σ) by ring]
      exact le_trans (neg_le_neg hbn.le) (neg_le_abs _)
    have hvar : variance (b n) P = n := by
      rw [← covariance_self (hb.pre.aemeasurable n), hb.pre.covariance_eval n n, min_self,
        NNReal.coe_natCast]
    refine (measure_mono hsub2).trans ((meas_ge_le_variance_div_sq
      (hb.pre.isGaussianProcess.hasGaussianLaw_eval n).memLp_two hc0).trans ?_)
    rw [hvar]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : (μ * n) ^ 2 ≤ 4 * (μ * n - x) ^ 2 := by
      have h1 : (μ * n / 2) ^ 2 ≤ (μ * n - x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hmn 2
      nlinarith [h1]
    have hA : (0 : ℝ) < (μ * n - x) ^ 2 := pow_pos (by linarith) 2
    calc n / c ^ 2 = n * σ ^ 2 / (μ * n - x) ^ 2 := by
          rw [hc, div_pow]
          field_simp
      _ ≤ 4 * σ ^ 2 / (μ ^ 2 * n) := by
          rw [div_le_div_iff₀ hA (by positivity)]
          nlinarith [h4, sq_nonneg σ]
      _ = (4 * σ ^ 2 / μ ^ 2) / n := by ring
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal ((4 * σ ^ 2 / μ ^ 2) / n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat _)
  refine le_antisymm (ge_of_tendsto htend ?_) zero_le
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * x / μ : ℝ)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  exact hbound n (hN.trans (by exact_mod_cast (le_max_left _ _).trans hn))
    (by exact_mod_cast (le_max_right _ _).trans hn)

/-! ## The key pointwise identity -/

/-- **Key identity.** If the indicator of `T` vanishes on the part of the path strictly before
the first hitting time `τ` of the level `a`, then the occupation integral of `T` over `(0, ∞)`
equals the occupation integral, over the restarted path `u ↦ w (τ + u) − a`, of `T` shifted by
`-a` (`T - a := {z | z + a ∈ T}`).

The time `τ` itself contributes nothing, because a single point is Lebesgue-null: this is why the
hypothesis on `T` is only needed strictly before `τ`. -/
theorem lintegral_Ioi_indicator_restart {w : ℝ≥0 → ℝ} (hw : Measurable w) {a : ℝ} {T : Set ℝ}
    (hT : MeasurableSet T) (hlt : ∀ m : ℝ≥0, m < hitLevel w a → w m ∉ T) :
    ∫⁻ m in Set.Ioi (0 : ℝ), T.indicator 1 (w m.toNNReal)
      = ∫⁻ u in Set.Ioi (0 : ℝ),
          ((fun z => z + a) ⁻¹' T).indicator 1 (w (hitLevel w a + u.toNNReal) - a) := by
  set F : ℝ → ℝ≥0∞ := fun m => T.indicator 1 (w m.toNNReal) with hFdef
  have hFm : Measurable F :=
    (measurable_const.indicator hT).comp (hw.comp measurable_id.real_toNNReal)
  -- split the integral at the hitting time
  have hpoint : ∀ m : ℝ, (Set.Ioi (0 : ℝ)).indicator F m
      = (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m
        + (Set.Ioi (hitLevel w a : ℝ)).indicator F m := by
    intro m
    by_cases hm0 : (0 : ℝ) < m
    · by_cases hmτ : m ≤ (hitLevel w a : ℝ)
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hm0),
          Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hm0, hmτ⟩),
          Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact hmτ), add_zero]
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hm0),
          Set.indicator_of_notMem (by
            simp only [Set.mem_Ioc, not_and]
            exact fun _ => hmτ),
          Set.indicator_of_mem (Set.mem_Ioi.2 (not_le.1 hmτ)), zero_add]
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi, not_lt]; exact not_lt.1 hm0),
        Set.indicator_of_notMem (by
          intro hmem
          exact hm0 (Set.mem_Ioc.1 hmem).1),
        Set.indicator_of_notMem (by
          simp only [Set.mem_Ioi, not_lt]
          exact le_trans (not_lt.1 hm0) (by positivity)), add_zero]
  -- the part before `τ` contributes nothing (only the single point `τ` can be in the support)
  have hzero : ∫⁻ m in Set.Ioc (0 : ℝ) (hitLevel w a : ℝ), F m = 0 := by
    have hle : ∫⁻ m in Set.Ioc (0 : ℝ) (hitLevel w a : ℝ), F m ≤ 0 := by
      rw [← lintegral_indicator measurableSet_Ioc]
      calc ∫⁻ m, (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m
          ≤ ∫⁻ m, ({(hitLevel w a : ℝ)} : Set ℝ).indicator (fun _ => ⊤) m := by
            refine lintegral_mono fun m => ?_
            by_cases hm : m ∈ Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)
            · by_cases hme : m = (hitLevel w a : ℝ)
              · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (Set.mem_singleton_iff.mpr hme)]
                exact le_top
              · have hmemτ : m.toNNReal < hitLevel w a := by
                  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hm.1.le]
                  exact lt_of_le_of_ne hm.2 hme
                rw [Set.indicator_of_mem hm,
                  Set.indicator_of_notMem (by simp only [Set.mem_singleton_iff]; exact hme)]
                exact le_of_eq (by
                  simp only [hFdef, Set.indicator_of_notMem (hlt m.toNNReal hmemτ)])
            · rw [Set.indicator_of_notMem hm]; exact bot_le
        _ = 0 := by
            rw [lintegral_indicator (measurableSet_singleton _), setLIntegral_const,
              measure_singleton, mul_zero]
    exact le_antisymm hle bot_le
  have hsplit : (∫⁻ m, (Set.Ioi (0 : ℝ)).indicator F m)
      = (∫⁻ m, (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m)
        + (∫⁻ m, (Set.Ioi (hitLevel w a : ℝ)).indicator F m) := by
    have h1 : (∫⁻ m, ((Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m
          + (Set.Ioi (hitLevel w a : ℝ)).indicator F m))
        = (∫⁻ m, (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m)
          + (∫⁻ m, (Set.Ioi (hitLevel w a : ℝ)).indicator F m) :=
      lintegral_add_left (μ := volume)
        (f := fun m : ℝ => (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m)
        (hFm.indicator measurableSet_Ioc) _
    rw [← h1]
    exact lintegral_congr fun m => hpoint m
  calc (∫⁻ m in Set.Ioi (0 : ℝ), F m)
      = (∫⁻ m, (Set.Ioi (0 : ℝ)).indicator F m) :=
        (lintegral_indicator (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi F).symm
    _ = (∫⁻ m, (Set.Ioc (0 : ℝ) (hitLevel w a : ℝ)).indicator F m)
          + (∫⁻ m, (Set.Ioi (hitLevel w a : ℝ)).indicator F m) := hsplit
    _ = (∫⁻ m in Set.Ioc (0 : ℝ) (hitLevel w a : ℝ), F m)
          + (∫⁻ m in Set.Ioi (hitLevel w a : ℝ), F m) := by
        exact congrArg₂ (fun x y : ℝ≥0∞ => x + y)
          (lintegral_indicator (μ := volume) (s := Set.Ioc (0 : ℝ) (hitLevel w a : ℝ))
            measurableSet_Ioc F)
          (lintegral_indicator (μ := volume) (s := Set.Ioi (hitLevel w a : ℝ))
            measurableSet_Ioi F)
    _ = (∫⁻ m in Set.Ioi (hitLevel w a : ℝ), F m) := by
        rw [hzero, zero_add]
    _ = (∫⁻ u in Set.Ioi (0 : ℝ), F ((hitLevel w a : ℝ) + u)) := lintegral_Ioi_add F _
    _ = ∫⁻ u in Set.Ioi (0 : ℝ),
          ((fun z => z + a) ⁻¹' T).indicator 1 (w (hitLevel w a + u.toNNReal) - a) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hcoe : (((hitLevel w a : ℝ≥0) : ℝ) + u).toNNReal = hitLevel w a + u.toNNReal := by
          refine NNReal.coe_injective ?_
          rw [Real.coe_toNNReal _ (add_nonneg (by positivity) hu.le), NNReal.coe_add,
            Real.coe_toNNReal u hu.le]
        rw [hFdef]
        simp only [hcoe]
        by_cases hmem : w (hitLevel w a + u.toNNReal) ∈ T
        · rw [Set.indicator_of_mem hmem]
          rw [Set.indicator_of_mem (show w (hitLevel w a + u.toNNReal) - a
              ∈ (fun z => z + a) ⁻¹' T by
            simp only [Set.mem_preimage]
            rw [sub_add_cancel]
            exact hmem)]
          rfl
        · rw [Set.indicator_of_notMem hmem]
          rw [Set.indicator_of_notMem (show w (hitLevel w a + u.toNNReal) - a
              ∉ (fun z => z + a) ⁻¹' T by
            simp only [Set.mem_preimage]
            intro h
            exact hmem (by rwa [sub_add_cancel] at h))]

/-! ## Positivity of the occupation density at `0` -/

/-- **W3.** For `σ, μ > 0` the occupation density at the origin is positive: the integrand is
strictly positive on `(0, ∞)`, a set of infinite Lebesgue measure. Own elementary proof. -/
theorem occDens_pos_zero (hσ : 0 < σ) (hμ : 0 < μ) : 0 < occDens σ μ 0 := by
  have hint := integrable_occDens_integrand hσ hμ 0
  have hsub : Set.Ioi (0 : ℝ)
      ⊆ Function.support fun m : ℝ => gaussianPDFReal (μ * m) (occVar σ m) 0 := by
    intro m hm
    have hm0 : (0 : ℝ) < m := hm
    simp only [Function.mem_support]
    rw [gaussianPDFReal_occVar_eq σ μ hm0.le 0]
    refine mul_ne_zero (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 ?_))) (Real.exp_ne_zero _)
    exact mul_pos (by positivity) (mul_pos (by positivity) hm0)
  have hinf : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) = ⊤ := by
    rw [Measure.restrict_apply measurableSet_Ioi, Set.inter_self]
    exact Real.volume_Ioi
  rw [occDens, integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun m => gaussianPDFReal_nonneg _ _ _) hint]
  exact lt_of_lt_of_le (by rw [hinf]; exact ENNReal.zero_lt_top) (measure_mono hsub)

/-! ## Measurability of the path evaluated after the first hit of a level -/

/-- Let `Y = dpath σ μ b` and `τ = hitLevel Y a`. For `n : ℕ`, the capped path
`u ↦ (if hittingBtwn Y {a} 0 n = n then Y u else Y (hittingBtwn Y {a} 0 n + u))` agrees with
`u ↦ Y (τ + u)` at `u` as soon as `n` exceeds the hitting time: the `if` compensates mathlib's
convention that `hittingBtwn u s n m x = m` (the *upper* bound) when `s` is not hit in `[n, m]`,
so that off the hitting event the capped path is `Y u = Y (0 + u)`, the junk value of `hitLevel`
being `0`. -/
theorem measurable_dpath_hitLevel_add (hb : GoodBM b P) (σ μ a : ℝ) (u : ℝ≥0) :
    Measurable fun ω => dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + u) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω => if hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω
        = (n : ℝ≥0) then dpath σ μ b ω u
      else dpath σ μ b ω (hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω + u))
    ?_ ?_
  · intro n
    have hAd : Adapted (pastFilt b hb.meas) (fun t (ω : Ω) => dpath σ μ b ω t) := fun t =>
      ((WedgeTrans.meas_comap_eval (fun ω (r : Set.Iic t) => b r ω)
        ⟨t, Set.mem_Iic.2 le_rfl⟩).const_mul σ).add_const (μ * (t : ℝ))
    have hstopn : IsStoppingTime (pastFilt b hb.meas)
        (fun ω => ((hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω : ℝ≥0) :
          WithTop ℝ≥0)) :=
      ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := pastFilt b hb.meas) hAd
        (continuous_dpath hb σ μ) (isClosed_singleton (x := a)) (n : ℝ≥0)
    have hTm : Measurable fun ω =>
        hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω :=
      StrongMarkov.measurable_of_isStoppingTime hstopn
    have hshift : Measurable fun ω =>
        dpath σ μ b ω (hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω + u) :=
      StrongMarkov.measurable_randomTime_eval (B := fun t (ω : Ω) => dpath σ μ b ω t)
        (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t) (hTm.add_const u)
    exact Measurable.ite (measurableSet_eq_fun hTm measurable_const)
      (measurable_dpath hb σ μ u) hshift
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ∃ t : ℝ≥0, dpath σ μ b ω t = a
    · obtain ⟨N, hN⟩ := exists_nat_ge (hitLevel (dpath σ μ b ω) a : ℝ)
      have hτmem : dpath σ μ b ω (hitLevel (dpath σ μ b ω) a) = a :=
        hitLevel_mem (continuous_dpath hb σ μ ω) hω
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (N + 1)] with n hn
      have hnτ : hitLevel (dpath σ μ b ω) a < (n : ℝ≥0) := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_natCast]
        have hn' : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hτle : hitLevel (dpath σ μ b ω) a ≤ (n : ℝ≥0) := hnτ.le
      have hmemIcc : dpath σ μ b ω (hitLevel (dpath σ μ b ω) a) ∈ ({a} : Set ℝ) := by
        simpa using hτmem
      have hne : ∃ j ∈ Set.Icc (0 : ℝ≥0) (n : ℝ≥0), dpath σ μ b ω j ∈ ({a} : Set ℝ) :=
        ⟨hitLevel (dpath σ μ b ω) a, Set.mem_Icc.mpr ⟨zero_le, hτle⟩, hmemIcc⟩
      have hinf : sInf (Set.Icc (0 : ℝ≥0) (n : ℝ≥0)
          ∩ {i : ℝ≥0 | dpath σ μ b ω i ∈ ({a} : Set ℝ)}) = hitLevel (dpath σ μ b ω) a := by
        refine le_antisymm ?_ ?_
        · exact csInf_le (OrderBot.bddBelow _)
            ⟨Set.mem_Icc.mpr ⟨zero_le, hτle⟩, hmemIcc⟩
        · refine le_csInf ⟨hitLevel (dpath σ μ b ω) a,
            Set.mem_Icc.mpr ⟨zero_le, hτle⟩, hmemIcc⟩ ?_
          rintro y ⟨-, hyK⟩
          exact csInf_le (OrderBot.bddBelow _) hyK
      have hτn : hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω
          = hitLevel (dpath σ μ b ω) a := by
        simp only [hittingBtwn]
        rw [if_pos hne]
        exact hinf
      have hne' : ¬ (hitLevel (dpath σ μ b ω) a = (n : ℝ≥0)) := ne_of_lt hnτ
      rw [hτn, if_neg hne']
    · have hempty : {t : ℝ≥0 | dpath σ μ b ω t = a} = ∅ := by
        ext t
        exact ⟨fun ht => absurd ⟨t, ht⟩ hω, fun ht => absurd ht (Set.notMem_empty t)⟩
      have hzero : hitLevel (dpath σ μ b ω) a = 0 := by
        rw [hitLevel, hempty]
        simp
      refine tendsto_const_nhds.congr' ?_
      refine Filter.Eventually.of_forall fun n => ?_
      have hno : ¬ ∃ j ∈ Set.Icc (0 : ℝ≥0) (n : ℝ≥0), dpath σ μ b ω j ∈ ({a} : Set ℝ) := by
        rintro ⟨j, -, hj⟩
        exact hω ⟨j, hj⟩
      have hτn : hittingBtwn (fun t (ω : Ω) => dpath σ μ b ω t) {a} 0 (n : ℝ≥0) ω = (n : ℝ≥0) := by
        simp only [hittingBtwn]
        exact if_neg hno
      simp only []
      rw [hτn, if_pos rfl, hzero, zero_add]

/-- **Joint measurability.** `(ω, u) ↦ Y (τ(ω) + u) (ω)` is measurable on `Ω × ℝ≥0`, where
`Y = dpath σ μ b` and `τ = hitLevel Y a`. -/
theorem measurable_uncurry_dpath_hitLevel (hb : GoodBM b P) (σ μ a : ℝ) :
    Measurable fun p : Ω × ℝ≥0 => dpath σ μ b p.1 (hitLevel (dpath σ μ b p.1) a + p.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ≥0) (ω : Ω) => dpath σ μ b ω (hitLevel (dpath σ μ b ω) a + r))
    (fun ω => (continuous_dpath hb σ μ ω).comp (continuous_const.add continuous_id))
    (fun r => measurable_dpath_hitLevel_add hb σ μ a r)
  exact h.comp measurable_swap

/-! ## From the measure identity to the density: equality of continuous functions -/

/-- **Extraction of a pointwise identity from interval integrals.** If two continuous functions
have equal integrals over every interval `(a, b)` with `0 < a < b`, then they agree on `(0, ∞)`
(this is the blueprint's "the densities agree a.e., then everywhere by continuity": here the
equality of the integrals over all intervals is differentiated with the fundamental theorem of
calculus). Own elementary proof. -/
theorem eqOn_Ioi_of_integral_Ioc_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a b : ℝ, 0 < a → a < b → ∫ x in a..b, f x = ∫ x in a..b, g x) :
    Set.EqOn f g (Set.Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have ha : (0 : ℝ) < t / 2 := by linarith
  have hat : t / 2 < t := by linarith
  have hf_int : IntervalIntegrable f volume (t / 2) t := hf.intervalIntegrable _ _
  have hg_int : IntervalIntegrable g volume (t / 2) t := hg.intervalIntegrable _ _
  have hf_sm : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    hf.stronglyMeasurableAtFilter volume (𝓝 t)
  have hg_sm : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    hg.stronglyMeasurableAtFilter volume (𝓝 t)
  have hderiv : HasDerivAt
      (fun b => (∫ x in t / 2..b, f x) - (∫ x in t / 2..b, g x)) (f t - g t) t :=
    (intervalIntegral.integral_hasDerivAt_right hf_int hf_sm hf.continuousAt).sub
      (intervalIntegral.integral_hasDerivAt_right hg_int hg_sm hg.continuousAt)
  have h0 : (fun b => (∫ x in t / 2..b, f x) - (∫ x in t / 2..b, g x)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (t / 2) from hat)] with b hb
    rw [h (t / 2) b ha hb, sub_self]
  have hzero : deriv (fun b => (∫ x in t / 2..b, f x) - (∫ x in t / 2..b, g x)) t = 0 := by
    rw [Filter.EventuallyEq.deriv_eq h0, deriv_const]
  rw [hderiv.deriv] at hzero
  linarith

end QuantumZipper.Williams
