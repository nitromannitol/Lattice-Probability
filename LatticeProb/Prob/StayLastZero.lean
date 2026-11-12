import Mathlib
import LatticeProb.Prob.UpcrossStay
import LatticeProb.Prob.DriftLawStaySmall

/-!
# A late zero before the end of a successful attempt

For a path `w` with `w 0 = 0` that hits `c > 0` before `-δ` (`w ∈ levelSuccess δ c`), if the last zero
before the first hit of `c` is later than `s₀`, then `w > -δ` on `[0, s₀]` and the increments after the
first zero `ζ ≥ s₀` form a path in `levelSuccess δ c`.  By the strong Markov property at `ζ`, for
Brownian motion with positive drift,
`P(late zero, success) ≤ P(w > -δ on [0, s₀]) * P(success)`.

* `LatticeProb.isStopFun_const`: a constant time is a stopping functional.
* `LatticeProb.lastZero_levelSuccess_split`: the pathwise decomposition.
* `LatticeProb.driftLaw_lastZero_inter_levelSuccess_le`: the strong Markov bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A constant time is a stopping functional. -/
theorem isStopFun_const (s : ℝ≥0∞) : IsStopFun (fun _ => s) :=
  fun _ _ => ⟨fun _ => rfl, fun h => h⟩

/-- The first hit after a later time is later. -/
lemma hitFrom_mono_start {a : ℝ} {r r' : ℝ≥0∞} (h : r ≤ r') (w : ℝ≥0 → ℝ) :
    hitFrom a r w ≤ hitFrom a r' w :=
  le_iInf₂ fun _ hs => hitFrom_le (h.trans hs.1) hs.2

/-- **Pathwise decomposition at a late zero.**  Let `w` start at `0` and hit `c` before `-δ`.  If the
last zero of `w` before its first hit of `c` is after `s₀`, then the first zero `ζ` after `s₀` is finite,
`w > -δ` on `[0, s₀]`, and the increments of `w` after `ζ` hit `c` before `-δ`. -/
lemma lastZero_levelSuccess_split {δ c : ℝ} {w : C(ℝ≥0, ℝ)} (h0 : w 0 = 0)
    (hLS : w ∈ levelSuccess δ c) (hδ : 0 < δ) {s₀ : ℝ≥0}
    (hz : s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal) :
    hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) < ⊤ ∧ (∀ t : ℝ≥0, t ≤ s₀ → -δ < w t) ∧
      shiftPath (hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ)).toNNReal w ∈ levelSuccess δ c := by
  have hLS' : hitFrom c 0 (w : ℝ≥0 → ℝ) < hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) := hLS
  have hTtop : hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_lt hLS'
  obtain ⟨Tn, hTn, -, hwT, -⟩ := exists_hitFrom_eq w.continuous hTtop
  rw [hTn, ENNReal.toNNReal_coe] at hz
  rw [hTn] at hLS'
  have hne : {s : ℝ≥0 | s ≤ Tn ∧ w s = 0}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold lastZeroBefore at hz
    rw [hne] at hz
    simp at hz
  obtain ⟨s1, ⟨hs1T, hws1⟩, hs1⟩ := exists_lt_of_lt_csSup hne (by
    unfold lastZeroBefore at hz; exact hz)
  have hζle : hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) ≤ s1 :=
    hitFrom_le (by exact_mod_cast hs1.le) hws1
  have hζtop : hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζle
  obtain ⟨z, hzeq, hs0z, hwz, -⟩ := exists_hitFrom_eq w.continuous hζtop
  have hzs1 : z ≤ s1 := by rw [hzeq] at hζle; exact_mod_cast hζle
  have hs0z' : s₀ ≤ z := by exact_mod_cast hs0z
  refine ⟨by rw [hzeq]; exact ENNReal.coe_lt_top, ?_, ?_⟩
  · intro t ht
    by_contra hcon
    have hcon' : w t ≤ -δ := not_lt.1 hcon
    have hmem : -δ ∈ Icc (w t) (w 0) := ⟨hcon', by rw [h0]; linarith⟩
    obtain ⟨s, hs, hws⟩ := intermediate_value_Icc' zero_le w.continuous.continuousOn hmem
    have h1 : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) ≤ s := hitFrom_le zero_le hws
    have h2 : (s : ℝ≥0∞) ≤ Tn := by
      exact_mod_cast hs.2.trans (ht.trans (hs0z'.trans (hzs1.trans hs1T)))
    exact absurd (h1.trans h2) (not_le.2 hLS')
  · rw [hzeq, ENNReal.toNNReal_coe]
    show hitFrom c 0 ((shiftPath z w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) <
      hitFrom (-δ) 0 ((shiftPath z w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)
    have e1 := hitFrom_add_coe c z 0 (w : ℝ≥0 → ℝ)
    have e2 := hitFrom_add_coe (-δ) z 0 (w : ℝ≥0 → ℝ)
    rw [add_zero, hwz, sub_zero] at e1 e2
    have hzT : (z : ℝ≥0) ≤ Tn := hzs1.trans hs1T
    have e3 : hitFrom c (z : ℝ≥0∞) (w : ℝ≥0 → ℝ) = Tn :=
      le_antisymm (hitFrom_le (by exact_mod_cast hzT) hwT)
        (hTn ▸ hitFrom_mono_start zero_le _)
    have e4 : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) ≤ hitFrom (-δ) (z : ℝ≥0∞) (w : ℝ≥0 → ℝ) :=
      hitFrom_mono_start zero_le _
    have hsh : ((shiftPath z w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) = fun s => w (z + s) - 0 := by
      ext s; simp [shiftPath, hwz]
    rw [hsh]
    have hlt : (z : ℝ≥0∞) + hitFrom c 0 (fun s => w (z + s) - 0) <
        (z : ℝ≥0∞) + hitFrom (-δ) 0 (fun s => w (z + s) - 0) := by
      rw [← e1, ← e2, e3]
      exact lt_of_lt_of_le hLS' e4
    exact (ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top).1 hlt

/-- **Pathwise decomposition at a late zero, path above `-δ`.**  If `w` starts at `0`, stays above `-δ`
forever, and has a zero in `(s₀, b]`, then the first zero `ζ` after `s₀` is finite, `w > -δ` on `[0, s₀]`,
and the increments of `w` after `ζ` stay above `-δ` forever. -/
lemma lastZero_staySet_split {δ : ℝ} {w : C(ℝ≥0, ℝ)} (hst : w ∈ staySet δ) {s₀ b : ℝ≥0}
    (hz : s₀ < lastZeroBefore w b) :
    hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) < ⊤ ∧ (∀ t : ℝ≥0, t ≤ s₀ → -δ < w t) ∧
      shiftPath (hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ)).toNNReal w ∈ staySet δ := by
  have hne : {s : ℝ≥0 | s ≤ b ∧ w s = 0}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold lastZeroBefore at hz
    rw [hne] at hz
    simp at hz
  obtain ⟨s1, ⟨-, hws1⟩, hs1⟩ := exists_lt_of_lt_csSup hne (by
    unfold lastZeroBefore at hz; exact hz)
  have hζle : hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) ≤ s1 :=
    hitFrom_le (by exact_mod_cast hs1.le) hws1
  have hζtop : hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζle
  obtain ⟨z, hzeq, -, hwz, -⟩ := exists_hitFrom_eq w.continuous hζtop
  refine ⟨by rw [hzeq]; exact ENNReal.coe_lt_top, fun t _ => hst t, ?_⟩
  rw [hzeq, ENNReal.toNNReal_coe]
  intro u
  have : (shiftPath z w : C(ℝ≥0, ℝ)) u = w (z + u) := by simp [shiftPath, hwz]
  rw [this]
  exact hst _

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Stopping at a time after `s₀` does not change a path on `[0, s₀]`. -/
lemma stopAt_apply_of_le {s₀ : ℝ≥0} {T : ℝ≥0∞} (hT : (s₀ : ℝ≥0∞) ≤ T) (w : C(ℝ≥0, ℝ)) {t : ℝ≥0}
    (ht : t ≤ s₀) : stopAt T w t = w t := by
  rw [stopAt_apply, min_eq_left ((ENNReal.coe_le_coe.2 ht).trans hT), ENNReal.toNNReal_coe]

/-- **Strong Markov bound at the first zero after `s₀`.**  If, almost surely on `X`, the first zero
`ζ` after `s₀` is finite, the path is above `-δ` on `[0, s₀]` and the increments after `ζ` lie in a
measurable set `S`, then `P(X) ≤ P(above `-δ` on `[0, s₀]`) * P(S)`. -/
theorem driftLaw_le_of_late_zero_split [IsProbabilityMeasure P] (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) (s₀ : ℝ≥0) (δ : ℝ)
    {S X : Set C(ℝ≥0, ℝ)} (hS : MeasurableSet S) (hB : IsBrownianReal B P)
    (hX : ∀ᵐ w ∂(driftLaw P B hcont mu), w ∈ X →
      hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) < ⊤ ∧ (∀ t : ℝ≥0, t ≤ s₀ → -δ < w t) ∧
        shiftPath (hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ)).toNNReal w ∈ S) :
    driftLaw P B hcont mu X ≤
      driftLaw P B hcont mu {w | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} * driftLaw P B hcont mu S := by
  set μ := driftLaw P B hcont mu with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_driftLaw hm hcont mu
  set ζ : C(ℝ≥0, ℝ) → ℝ≥0∞ := fun w => hitFrom 0 (s₀ : ℝ≥0∞) (w : ℝ≥0 → ℝ) with hζ
  have hζm : Measurable ζ := measurable_hitFrom (r := fun _ => (s₀ : ℝ≥0∞)) measurable_const 0
  have hζs : IsStopFun ζ := (isStopFun_const (s₀ : ℝ≥0∞)).hitFrom 0
  set Stay : Set C(ℝ≥0, ℝ) := {w | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} with hStaydef
  have hStay : MeasurableSet Stay := (isOpen_stayUpTo δ s₀).measurableSet
  have hstop : ∀ w : C(ℝ≥0, ℝ), stopAt (ζ w) w ∈ Stay ↔ w ∈ Stay := by
    intro w
    have hle : (s₀ : ℝ≥0∞) ≤ ζ w := le_hitFrom
    constructor
    · intro h t ht
      have := h t ht
      rwa [stopAt_apply_of_le hle w ht] at this
    · intro h t ht
      rw [stopAt_apply_of_le hle w ht]
      exact h t ht
  set Φ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞ := fun p =>
    Stay.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * S.indicator (fun _ => (1 : ℝ≥0∞)) p.2
    with hΦdef
  have hΦ : Measurable Φ :=
    ((measurable_const.indicator hStay).comp measurable_fst).mul
      ((measurable_const.indicator hS).comp measurable_snd)
  have hSM := lintegral_stopAt_shift_driftLaw hB hm hcont mu hζm hζs hΦ
  set Z : Set C(ℝ≥0, ℝ) := {w | ζ w < ⊤} with hZdef
  have hZ : MeasurableSet Z := hζm measurableSet_Iio
  set g : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) :=
    fun w => (stopAt (ζ w) w, shiftPath (ζ w).toNNReal w) with hgdef
  have hgm : Measurable g := (measurable_stopAt_path hζm).prodMk (measurable_shiftPath_path hζm)
  set Y : Set C(ℝ≥0, ℝ) := Z ∩ g ⁻¹' (Stay ×ˢ S) with hYdef
  have hYm : MeasurableSet Y := hZ.inter (hgm (hStay.prod hS))
  have h1 : μ X ≤ μ Y := by
    refine measure_mono_ae ?_
    filter_upwards [hX] with w hw hwX
    obtain ⟨hz1, hz2, hz3⟩ := hw hwX
    exact ⟨hz1, (hstop w).2 hz2, hz3⟩
  have h2 : μ Y = ∫⁻ w in Z, Φ (g w) ∂μ := by
    rw [← lintegral_indicator hZ, ← lintegral_indicator_one hYm]
    congr 1
    funext w
    by_cases hwZ : w ∈ Z
    · by_cases hw2 : g w ∈ Stay ×ˢ S
      · have hwY : w ∈ Y := ⟨hwZ, hw2⟩
        obtain ⟨hw21, hw22⟩ := Set.mem_prod.1 hw2
        rw [Set.indicator_of_mem hwZ, Set.indicator_of_mem hwY]
        simp only [Φ, Set.indicator_of_mem hw21, Set.indicator_of_mem hw22, Pi.one_apply, mul_one]
      · have hwY : w ∉ Y := fun h => hw2 h.2
        rw [Set.indicator_of_mem hwZ, Set.indicator_of_notMem hwY]
        have hn : (g w).1 ∉ Stay ∨ (g w).2 ∉ S := by
          by_contra hcon
          exact hw2 (Set.mem_prod.2 ⟨not_not.1 (fun h => hcon (Or.inl h)),
            not_not.1 (fun h => hcon (Or.inr h))⟩)
        rcases hn with hn | hn
        · simp [Φ, Set.indicator_of_notMem hn]
        · simp [Φ, Set.indicator_of_notMem hn]
    · have hwY : w ∉ Y := fun h => hwZ h.1
      rw [Set.indicator_of_notMem hwZ, Set.indicator_of_notMem hwY]
  have h3 : ∫⁻ w in Z, Φ (g w) ∂μ =
      ∫⁻ w in Z, (Stay.indicator (fun _ => (1 : ℝ≥0∞)) w) * μ S ∂μ := by
    have hSM' : ∫⁻ w in Z, Φ (g w) ∂μ = ∫⁻ w in Z, ∫⁻ v, Φ (stopAt (ζ w) w, v) ∂μ ∂μ := hSM
    rw [hSM']
    refine setLIntegral_congr_fun hZ fun w _ => ?_
    have : ∀ v, Φ (stopAt (ζ w) w, v) = Stay.indicator (fun _ => (1 : ℝ≥0∞)) w *
        S.indicator (fun _ => (1 : ℝ≥0∞)) v := by
      intro v
      have hind : Stay.indicator (fun _ => (1 : ℝ≥0∞)) (stopAt (ζ w) w) =
          Stay.indicator (fun _ => (1 : ℝ≥0∞)) w := by
        by_cases hw : w ∈ Stay
        · rw [Set.indicator_of_mem hw, Set.indicator_of_mem ((hstop w).2 hw)]
        · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw ((hstop w).1 h))]
      simp only [hΦdef, hind]
    simp only [this]
    rw [lintegral_const_mul _ (measurable_const.indicator hS), lintegral_indicator_const hS, one_mul]
  calc μ X ≤ μ Y := h1
    _ = ∫⁻ w in Z, (Stay.indicator (fun _ => (1 : ℝ≥0∞)) w) * μ S ∂μ := h2.trans h3
    _ ≤ ∫⁻ w, (Stay.indicator (fun _ => (1 : ℝ≥0∞)) w) * μ S ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = μ Stay * μ S := by
        rw [lintegral_mul_const _ (measurable_const.indicator hStay), lintegral_indicator_const hStay, one_mul]

/-- **Strong Markov bound for a late zero, successful attempt.**  For Brownian motion with positive
drift, the probability that an attempt to reach `c` before `-δ` succeeds although the last zero before
the hit of `c` is later than `s₀` is at most the probability to stay above `-δ` up to time `s₀` times
the probability of success. -/
theorem driftLaw_lastZero_inter_levelSuccess_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (s₀ : ℝ≥0) :
    driftLaw P B hcont mu
        ({w | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal} ∩ levelSuccess δ c) ≤
      driftLaw P B hcont mu {w | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} *
        driftLaw P B hcont mu (levelSuccess δ c) := by
  refine driftLaw_le_of_late_zero_split hm hcont mu s₀ δ (measurableSet_levelSuccess δ c) hB ?_
  filter_upwards [(ae_start_hitFrom_driftLaw hB hm hcont hmu hc.le)] with w hw ⟨hwA, hwL⟩
  exact lastZero_levelSuccess_split hw.1 hwL hδ hwA

/-- **Strong Markov bound for a late zero, path above `-δ`.**  For Brownian motion with positive drift,
the probability that the path stays above `-δ` forever and has its last zero before the first hit of
`c` later than `s₀` is at most the probability to stay above `-δ` up to time `s₀` times the probability
to stay above `-δ` forever. -/
theorem driftLaw_lastZero_inter_staySet_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {δ : ℝ} (c : ℝ) (s₀ : ℝ≥0) :
    driftLaw P B hcont mu
        ({w | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal} ∩ staySet δ) ≤
      driftLaw P B hcont mu {w | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} *
        driftLaw P B hcont mu (staySet δ) := by
  refine driftLaw_le_of_late_zero_split hm hcont mu s₀ δ (measurableSet_staySet δ) hB ?_
  filter_upwards with w ⟨hwA, hwL⟩
  exact lastZero_staySet_split hwL hwA

/-- **Conditioned on staying above `-δ`, the last zero is early.**  The conditional probability, given
that Brownian motion with positive drift stays above `-δ` forever, that the last zero before the first
hit of `c` is later than `s₀` is at most the probability to stay above `-δ` up to time `s₀`. -/
theorem cond_staySet_lastZero_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {δ : ℝ} (c : ℝ) (s₀ : ℝ≥0) :
    (driftLaw P B hcont mu)[|staySet δ]
        {w | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal} ≤
      driftLaw P B hcont mu {w | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} := by
  set μ := driftLaw P B hcont mu with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_driftLaw hm hcont mu
  set A : Set C(ℝ≥0, ℝ) := {w | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal}
  rw [ProbabilityTheory.cond_apply (measurableSet_staySet δ)]
  by_cases h0 : μ (staySet δ) = 0
  · have : μ (staySet δ ∩ A) = 0 := measure_mono_null Set.inter_subset_left h0
    simp [this]
  · have hle := driftLaw_lastZero_inter_staySet_le hB hm hcont mu (δ := δ) c s₀
    rw [Set.inter_comm] at hle
    calc (μ (staySet δ))⁻¹ * μ (staySet δ ∩ A)
        ≤ (μ (staySet δ))⁻¹ * (μ {w : C(ℝ≥0, ℝ) | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} * μ (staySet δ)) :=
          mul_le_mul' le_rfl hle
      _ = μ {w : C(ℝ≥0, ℝ) | ∀ t : ℝ≥0, t ≤ s₀ → -δ < w t} := by
          rw [mul_comm (μ _) (μ (staySet δ)), ← mul_assoc, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _),
            one_mul]

/-- **The last zero before the first hit of `c` is near `0` for the process conditioned to stay
positive.**  For Brownian motion with positive drift and `s₀ > 0`, the conditional probability, given
that the path stays above `-δ` forever, of a last zero before the first hit of `c` later than `s₀`
tends to `0` as `δ → 0+`. -/
theorem tendsto_cond_staySet_lastZero [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    (c : ℝ) {s₀ : ℝ≥0} (hs₀ : 0 < s₀) :
    Filter.Tendsto (fun δ : ℝ => (driftLaw P B hcont mu)[|staySet δ]
        {w | s₀ < lastZeroBefore w (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal})
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_driftLaw_stay_small hB.toIsPreBrownianReal hm hcont mu hs₀)
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards with δ
  exact cond_staySet_lastZero_le hB hm hcont mu c s₀

end Law

end LatticeProb
