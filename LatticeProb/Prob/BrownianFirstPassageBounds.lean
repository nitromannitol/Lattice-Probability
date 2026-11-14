import LatticeProb.Prob.BrownianLevyReflection
import LatticeProb.Prob.BrownianDriftExitMoment
import LatticeProb.Prob.BrownianFirstPassageStrict
import LatticeProb.Analysis.StraddlingLevelPairs

/-!
# Bounds for the first passage of a real Brownian motion below a level

Let `X : Ω → ℝ → ℝ` have continuous paths and let its restriction to `[0, ∞)` be a standard real
Brownian motion. For a level `a > 0` write `T_a ω = firstBelow (X ω) 0 (-a)` for the first time
`t ≥ 0` with `X ω t ≤ -a`.

* `firstBelow_zero_nonneg`, `firstBelow_zero_le_iff`, `firstBelow_zero_eq_zero`: deterministic facts
  (`T_a ≥ 0`, the event `T_a ≤ t`, the value `sInf ∅ = 0` when the level is never reached).
* `measurable_firstBelow`: `ω ↦ T_a ω` is measurable.
* `ae_forall_exists_nonneg_le`: almost surely the path goes below every level on `[0, ∞)`.
* `measure_le_neg_le_measure_firstBelow_le`, `gaussianReal_Iic_neg_one_le_measure_firstBelow_le`:
  `P(X t ≤ -a) ≤ P(T_a ≤ t)`, hence `Φ(-1) ≤ P(T_a ≤ a²)`.
* `lintegral_inv_sqrt_firstBelow_le`: `E[T_a^{-1/2}] ≤ 4 / a`. By Lévy's reflection inequality
  `P(T_a < x^{-2}) ≤ 2 P(B_{x^{-2}} ≤ -a/2) ≤ 2 P(|N| ≥ a x / 2)` for a standard Gaussian `N`, and
  the layer-cake formula turns this into `E[T_a^{-1/2}] ≤ (4 / a) E|N| ≤ 4 / a`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- The first time at or after `0` at which `f` is at most `l` is nonnegative; this includes the
value `sInf ∅ = 0` when `f` never reaches `l` on `[0, ∞)`. -/
theorem firstBelow_zero_nonneg (f : ℝ → ℝ) (l : ℝ) : 0 ≤ firstBelow f 0 l := by
  rcases Set.eq_empty_or_nonempty {u | 0 ≤ u ∧ f u ≤ l} with h | h
  · rw [firstBelow, h, Real.sInf_empty]
  · exact le_csInf h fun _ hu => hu.1

/-- For a continuous function which is at most `l` somewhere on `[0, ∞)`, the first time at or
after `0` at which it is at most `l` is at most `t` if and only if this happens in `[0, t]`. -/
theorem firstBelow_zero_le_iff {f : ℝ → ℝ} {l : ℝ} (hf : Continuous f)
    (hb : ∃ b, 0 ≤ b ∧ f b ≤ l) (t : ℝ) :
    firstBelow f 0 l ≤ t ↔ ∃ u, 0 ≤ u ∧ u ≤ t ∧ f u ≤ l :=
  ⟨fun h => ⟨_, (firstBelow_mem hf hb).1, h, (firstBelow_mem hf hb).2⟩,
    fun ⟨_, hu0, hut, hu⟩ => (firstBelow_le hu0 hu).trans hut⟩

/-- If `f` is never at most `l` on `[0, ∞)`, then `firstBelow f 0 l = 0` (the value `sInf ∅`). -/
theorem firstBelow_zero_eq_zero {f : ℝ → ℝ} {l : ℝ} (hb : ¬∃ b, 0 ≤ b ∧ f b ≤ l) :
    firstBelow f 0 l = 0 := by
  have h : {u | 0 ≤ u ∧ f u ≤ l} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun u hu => hb ⟨u, hu⟩
  rw [firstBelow, h, Real.sInf_empty]

/-- The law of a centred Gaussian variable of variance `c²` is the image of the standard
Gaussian law under `y ↦ c y`. -/
theorem gaussianReal_sq_apply (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    gaussianReal 0 (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) S =
      gaussianReal 0 1 ((fun y => c * y) ⁻¹' S) := by
  have h : (gaussianReal 0 1).map (fun y => c * y) = gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
    have h' := gaussianReal_map_const_mul (μ := 0) (v := 1) c
    rw [mul_zero, mul_one] at h'
    exact h'
  rw [← h, Measure.map_apply (measurable_const_mul c) hS]

/-- The first absolute moment of a standard Gaussian variable is at most `1`. -/
theorem lintegral_ofReal_abs_gaussianReal_le_one :
    ∫⁻ y, ENNReal.ofReal |y| ∂gaussianReal 0 1 ≤ 1 := by
  have hL2 : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by norm_num)
  have hsqI : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := hL2.integrable_sq
  have hsq : ∫ y, y ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h := variance_eq_integral (X := id) (μ := gaussianReal 0 1) measurable_id.aemeasurable
    have h0 : ∫ x, id x ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    rw [variance_id_gaussianReal, h0] at h
    simpa using h.symm
  have hI : Integrable (fun y : ℝ => (1 + y ^ 2) / 2) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add hsqI).div_const 2
  calc ∫⁻ y, ENNReal.ofReal |y| ∂gaussianReal 0 1
      ≤ ∫⁻ y, ENNReal.ofReal ((1 + y ^ 2) / 2) ∂gaussianReal 0 1 :=
        lintegral_mono fun y =>
          ENNReal.ofReal_le_ofReal (by nlinarith [sq_abs y, sq_nonneg (|y| - 1)])
    _ = ENNReal.ofReal (∫ y, (1 + y ^ 2) / 2 ∂gaussianReal 0 1) :=
        (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun y => by positivity)).symm
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const (1 : ℝ)) hsqI, hsq]
        norm_num

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ → ℝ}

/-- For a process with continuous paths and measurable coordinates, the event that the path is at
most `l` at some time of `[0, t]` is measurable. -/
theorem measurableSet_exists_le_le (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t)
    (hcont : ∀ ω, Continuous (X ω)) (l : ℝ) (t : ℝ≥0) :
    MeasurableSet {ω | ∃ s : ℝ≥0, s ≤ t ∧ X ω s ≤ l} := by
  have hBc : ∀ ω, Continuous fun s : ℝ≥0 => X ω s := fun ω => (hcont ω).comp NNReal.continuous_coe
  have hst := isStoppingTime_hitDrift_neg_brownian (B := fun s ω => X ω s) hm hBc 0 (-l) t
  have h := (brownianFiltration (fun s ω => X ω s) hm).le t _ hst
  have hBc' : ∀ ω, Continuous fun s => (fun (t : ℝ≥0) ω => -X ω t) s ω := fun ω => (hBc ω).neg
  convert h using 1
  ext ω
  change (∃ s : ℝ≥0, s ≤ t ∧ X ω s ≤ l) ↔
    hitDrift (fun (t : ℝ≥0) ω => -X ω t) (-0) (-l) ω ≤ (t : ℝ≥0∞)
  rw [hitDrift_le_iff hBc' (-0) (-l) ω t]
  constructor
  · rintro ⟨s, hs, hX⟩
    exact ⟨s, hs, by simp only [neg_zero, zero_mul, add_zero]; linarith⟩
  · rintro ⟨s, hs, hX⟩
    refine ⟨s, hs, ?_⟩
    simp only [neg_zero, zero_mul, add_zero] at hX
    linarith

/-- For a process with continuous paths and measurable coordinates, the event that the path is at
most `l` at some time of `[0, ∞)` is measurable. -/
theorem measurableSet_exists_nonneg_le (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t)
    (hcont : ∀ ω, Continuous (X ω)) (l : ℝ) :
    MeasurableSet {ω | ∃ u, 0 ≤ u ∧ X ω u ≤ l} := by
  have h : {ω | ∃ u, 0 ≤ u ∧ X ω u ≤ l} = ⋃ n : ℕ, {ω | ∃ s : ℝ≥0, s ≤ n ∧ X ω s ≤ l} := by
    ext ω
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu0, hu⟩
      obtain ⟨n, hn⟩ := exists_nat_ge u
      exact ⟨n, u.toNNReal, Real.toNNReal_le_iff_le_coe.2 (by simpa using hn),
        by rwa [Real.coe_toNNReal _ hu0]⟩
    · rintro ⟨n, s, -, hs⟩
      exact ⟨s, s.coe_nonneg, hs⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => measurableSet_exists_le_le hm hcont l n

/-- **Measurability of the first passage time.** For a process with continuous paths and
measurable coordinates, `ω ↦ firstBelow (X ω) 0 l` is measurable. -/
theorem measurable_firstBelow (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t)
    (hcont : ∀ ω, Continuous (X ω)) (l : ℝ) : Measurable fun ω => firstBelow (X ω) 0 l := by
  refine measurable_of_Iic fun c => ?_
  rcases lt_or_ge c 0 with hc | hc
  · have h : (fun ω => firstBelow (X ω) 0 l) ⁻¹' Iic c = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun ω (hω : firstBelow (X ω) 0 l ≤ c) =>
        absurd (hω.trans_lt hc) (not_lt.2 (firstBelow_zero_nonneg _ _))
    rw [h]
    exact MeasurableSet.empty
  · have h : (fun ω => firstBelow (X ω) 0 l) ⁻¹' Iic c =
        {ω | ∃ s : ℝ≥0, s ≤ c.toNNReal ∧ X ω s ≤ l} ∪ {ω | ∃ u, 0 ≤ u ∧ X ω u ≤ l}ᶜ := by
      ext ω
      show firstBelow (X ω) 0 l ≤ c ↔
        (∃ s : ℝ≥0, s ≤ c.toNNReal ∧ X ω s ≤ l) ∨ ¬∃ u, 0 ≤ u ∧ X ω u ≤ l
      by_cases hb : ∃ b, 0 ≤ b ∧ X ω b ≤ l
      · rw [firstBelow_zero_le_iff (hcont ω) hb]
        constructor
        · rintro ⟨u, hu0, huc, hu⟩
          exact Or.inl ⟨u.toNNReal, Real.toNNReal_le_toNNReal huc,
            by rwa [Real.coe_toNNReal _ hu0]⟩
        · rintro (⟨s, hs, hX⟩ | hn)
          · exact ⟨s, s.coe_nonneg, (NNReal.coe_le_coe.2 hs).trans_eq (Real.coe_toNNReal c hc), hX⟩
          · exact absurd hb hn
      · rw [firstBelow_zero_eq_zero hb]
        exact iff_of_true hc (Or.inr hb)
    rw [h]
    exact (measurableSet_exists_le_le hm hcont l _).union
      (measurableSet_exists_nonneg_le hm hcont l).compl

/-- **Recurrence.** If the restriction of `X` to `[0, ∞)` is a Brownian motion, then almost surely
the path is at most `l` at some time of `[0, ∞)`, for every level `l`. -/
theorem ae_forall_exists_nonneg_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal (fun (t : ℝ≥0) ω => X ω t) P)
    (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t) (hcont : ∀ ω, Continuous (X ω)) :
    ∀ᵐ ω ∂P, ∀ l : ℝ, ∃ u, 0 ≤ u ∧ X ω u ≤ l := by
  have hBc : ∀ ω, Continuous fun s : ℝ≥0 => X ω s := fun ω => (hcont ω).comp NNReal.continuous_coe
  have hall := ae_all_iff.2 fun n : ℕ => LadderSet.ae_hitDrift_neg_lt_top hB hm hBc (n : ℝ)
  filter_upwards [hall] with ω hω l
  obtain ⟨n, hn⟩ := exists_nat_ge (-l)
  have h := hω n
  unfold hitDrift at h
  split_ifs at h with hc
  · obtain ⟨s, hs⟩ := hc
    have hs' : (n : ℝ) ≤ -X ω s + 0 * s := hs
    exact ⟨s, s.coe_nonneg, by linarith⟩
  · exact absurd h (lt_irrefl _)

/-- If the path is at most `-a` at the time `t ≥ 0`, its first passage at most `-a` is at most
`t`. -/
theorem measure_le_neg_le_measure_firstBelow_le (t : ℝ≥0) (a : ℝ) :
    P {ω | X ω t ≤ -a} ≤ P {ω | firstBelow (X ω) 0 (-a) ≤ t} :=
  measure_mono fun _ hω => firstBelow_le t.coe_nonneg hω

/-- **The first passage below `-a` happens by time `a²` with probability at least `Φ(-1)`.** -/
theorem gaussianReal_Iic_neg_one_le_measure_firstBelow_le
    (hB : IsBrownianReal (fun (t : ℝ≥0) ω => X ω t) P)
    (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t) {a : ℝ} (ha : 0 < a) :
    gaussianReal 0 1 (Iic (-1)) ≤ P {ω | firstBelow (X ω) 0 (-a) ≤ a ^ 2} := by
  have hlaw : P.map (fun ω => X ω (⟨a ^ 2, sq_nonneg a⟩ : ℝ≥0)) =
      gaussianReal 0 ⟨a ^ 2, sq_nonneg a⟩ :=
    (hB.toIsPreBrownianReal.hasLaw_eval _).map_eq
  have hpre : (fun y => a * y) ⁻¹' Iic (-a) = Iic (-1) := by
    ext y
    show a * y ≤ -a ↔ y ≤ -1
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  calc gaussianReal 0 1 (Iic (-1))
      = P {ω | X ω (⟨a ^ 2, sq_nonneg a⟩ : ℝ≥0) ≤ -a} := by
        rw [← hpre, ← gaussianReal_sq_apply a measurableSet_Iic, ← hlaw]
        exact Measure.map_apply (hm _) measurableSet_Iic
    _ ≤ P {ω | firstBelow (X ω) 0 (-a) ≤ (⟨a ^ 2, sq_nonneg a⟩ : ℝ≥0)} :=
        measure_le_neg_le_measure_firstBelow_le _ a

/-- **Inverse square-root moment of the first passage time.** If the restriction of `X` to
`[0, ∞)` is a Brownian motion with continuous paths, then for `a > 0` the first passage time
`T_a = firstBelow (X ·) 0 (-a)` satisfies `E[T_a^{-1/2}] ≤ 4 / a` (with `0^{-1/2} = 0`). -/
theorem lintegral_inv_sqrt_firstBelow_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal (fun (t : ℝ≥0) ω => X ω t) P)
    (hm : ∀ t : ℝ≥0, Measurable fun ω => X ω t) (hcont : ∀ ω, Continuous (X ω))
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ ω, ENNReal.ofReal (√(firstBelow (X ω) 0 (-a)))⁻¹ ∂P ≤ ENNReal.ofReal (4 / a) := by
  have hTm := measurable_firstBelow hm hcont (-a)
  have hFm : Measurable fun ω => (√(firstBelow (X ω) 0 (-a)))⁻¹ := hTm.sqrt.inv
  rw [lintegral_eq_lintegral_meas_lt P
    (ae_of_all _ fun ω => inv_nonneg.2 (Real.sqrt_nonneg _)) hFm.aemeasurable]
  have hneg : IsBrownianReal (-fun (t : ℝ≥0) ω => X ω t) P := hB.neg
  have hmneg : ∀ t : ℝ≥0, Measurable ((-fun (t : ℝ≥0) ω => X ω t) t) := fun t => (hm t).neg
  have h0ae := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have key : ∀ x ∈ Ioi (0 : ℝ), P {ω | x < (√(firstBelow (X ω) 0 (-a)))⁻¹} ≤
      2 * gaussianReal 0 1 {y | x ≤ |y| / (a / 2)} := by
    intro x hx
    have hx : 0 < x := hx
    set t : ℝ≥0 := ⟨x⁻¹ ^ 2, sq_nonneg _⟩ with ht
    have hlaw : P.map (fun ω => X ω t) = gaussianReal 0 t :=
      (hB.toIsPreBrownianReal.hasLaw_eval t).map_eq
    have hsub : {ω | x < (√(firstBelow (X ω) 0 (-a)))⁻¹} ≤ᵐ[P]
        {ω | ∃ s ≤ t, a / 2 < (-fun (t : ℝ≥0) ω => X ω t) s ω -
          (-fun (t : ℝ≥0) ω => X ω t) 0 ω} := by
      filter_upwards [h0ae] with ω h0 hω
      have hω' : x < (√(firstBelow (X ω) 0 (-a)))⁻¹ := hω
      have hsq : 0 < √(firstBelow (X ω) 0 (-a)) := by
        rcases (Real.sqrt_nonneg (firstBelow (X ω) 0 (-a))).lt_or_eq with h | h
        · exact h
        · rw [← h, inv_zero] at hω'
          exact absurd hω' (not_lt.2 hx.le)
      have hT0 : 0 < firstBelow (X ω) 0 (-a) := Real.sqrt_pos.1 hsq
      have hb : ∃ b, 0 ≤ b ∧ X ω b ≤ -a := by
        by_contra hb
        rw [firstBelow_zero_eq_zero hb] at hT0
        exact lt_irrefl _ hT0
      obtain ⟨hTnn, hXT⟩ := firstBelow_mem (hcont ω) hb
      have hlt : √(firstBelow (X ω) 0 (-a)) < x⁻¹ := (lt_inv_comm₀ hx hsq).1 hω'
      have hTt : firstBelow (X ω) 0 (-a) ≤ x⁻¹ ^ 2 :=
        calc firstBelow (X ω) 0 (-a) = √(firstBelow (X ω) 0 (-a)) ^ 2 := (Real.sq_sqrt hTnn).symm
          _ ≤ x⁻¹ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hlt.le 2
      refine ⟨(firstBelow (X ω) 0 (-a)).toNNReal, Real.toNNReal_le_iff_le_coe.2 hTt, ?_⟩
      have h0' : X ω 0 = 0 := by simpa using h0
      show a / 2 < -X ω ((firstBelow (X ω) 0 (-a)).toNNReal : ℝ) - -X ω ((0 : ℝ≥0) : ℝ)
      rw [Real.coe_toNNReal _ hTnn, NNReal.coe_zero, h0']
      linarith
    calc P {ω | x < (√(firstBelow (X ω) 0 (-a)))⁻¹}
        ≤ P {ω | ∃ s ≤ t, a / 2 < (-fun (t : ℝ≥0) ω => X ω t) s ω -
            (-fun (t : ℝ≥0) ω => X ω t) 0 ω} := measure_mono_ae hsub
      _ ≤ 2 * P {ω | a / 2 ≤ (-fun (t : ℝ≥0) ω => X ω t) t ω -
            (-fun (t : ℝ≥0) ω => X ω t) 0 ω} := measure_exists_lt_le_two_mul hneg hmneg t (a / 2)
      _ ≤ 2 * P {ω | X ω t ≤ -(a / 2)} := by
          gcongr _ * ?_
          refine measure_mono_ae ?_
          filter_upwards [h0ae] with ω h0 hω
          have hω' : a / 2 ≤ -X ω t - -X ω ((0 : ℝ≥0) : ℝ) := hω
          have h0' : X ω 0 = 0 := by simpa using h0
          rw [NNReal.coe_zero, h0'] at hω'
          show X ω t ≤ -(a / 2)
          linarith
      _ = 2 * gaussianReal 0 1 ((fun y => x⁻¹ * y) ⁻¹' Iic (-(a / 2))) := by
          rw [← gaussianReal_sq_apply x⁻¹ measurableSet_Iic, ← ht, ← hlaw,
            Measure.map_apply (hm t) measurableSet_Iic]
          rfl
      _ ≤ 2 * gaussianReal 0 1 {y | x ≤ |y| / (a / 2)} := by
          gcongr _ * ?_
          refine measure_mono fun y hy => ?_
          have hy' : x⁻¹ * y ≤ -(a / 2) := hy
          show x ≤ |y| / (a / 2)
          rw [le_div_iff₀ (by positivity)]
          have hxy : y ≤ -(a / 2) * x := by
            have h := mul_le_mul_of_nonneg_left hy' hx.le
            rwa [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul, mul_comm] at h
          linarith [neg_le_abs y]
  calc ∫⁻ x in Ioi 0, P {ω | x < (√(firstBelow (X ω) 0 (-a)))⁻¹}
      ≤ ∫⁻ x in Ioi 0, 2 * gaussianReal 0 1 {y | x ≤ |y| / (a / 2)} :=
        setLIntegral_mono' measurableSet_Ioi key
    _ = 2 * ∫⁻ x in Ioi 0, gaussianReal 0 1 {y | x ≤ |y| / (a / 2)} :=
        lintegral_const_mul' _ _ (by norm_num)
    _ = 2 * ∫⁻ y, ENNReal.ofReal (|y| / (a / 2)) ∂gaussianReal 0 1 := by
        rw [lintegral_eq_lintegral_meas_le _ (ae_of_all _ fun y => by positivity)
          (by fun_prop : Measurable fun y : ℝ => |y| / (a / 2)).aemeasurable]
    _ = 2 * (ENNReal.ofReal (2 / a) * ∫⁻ y, ENNReal.ofReal |y| ∂gaussianReal 0 1) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.ofReal_mul (p := 2 / a) (by positivity)]
        congr 1
        ring
    _ ≤ 2 * (ENNReal.ofReal (2 / a) * 1) := by
        gcongr
        exact lintegral_ofReal_abs_gaussianReal_le_one
    _ = ENNReal.ofReal (4 / a) := by
        rw [mul_one, show (4 : ℝ) / a = 2 * (2 / a) by ring,
          ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]

end Process

end LatticeProb
