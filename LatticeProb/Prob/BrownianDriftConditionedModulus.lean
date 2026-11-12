/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LatticeProb.Prob.BrownianModulus
import LatticeProb.Prob.BrownianDriftConditionedRestart

/-!
# Modulus of continuity of the drifted Brownian motion conditioned to stay above `-δ`

Let `Y t = B t + c t` with `c > 0`, let `G_δ = {Y t > -δ for all t}` and let `τ` be the first time
at which `Y` reaches the level `ε`.  On `G_δ` the path `Y` stays in `(-δ, ε]` up to `τ`, so its
modulus of continuity on `[0, T]` is controlled by the modulus of continuity of the post-`τ` path
`u ↦ Y (τ + u)`, up to the additive error `ε + δ`.

* `LatticeProb.HasModulus`: the predicate `|g s - g t| ≤ a` for `s, t ≤ T`, `|s - t| ≤ η`.
* `LatticeProb.hasModulus_of_hit`: the deterministic decomposition at the hitting time.
* `LatticeProb.badPath`: the measurable set of paths with a large oscillation at times of a
  countable dense set; `LatticeProb.hasModulus_of_not_mem_badPath` is its deterministic
  counterpart.
* `LatticeProb.hasModulus_stayAbove_of_not_badPath`: the decomposition for the drifted motion.
* `LatticeProb.measure_stayAbove_inter_mem_mul_le`: the probability of the post-`τ` increments
  lying in a measurable set `S` on `G_δ ∩ {τ ≤ η}` is at most the probability of `S` for the
  drifted motion, divided by `1 - e^{-2c(ε+δ)}`.
* `LatticeProb.measure_stayAbove_inter_badPath_mul_le`: the same for `badPath`, with the Brownian
  modulus bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The path `g` has modulus `a` at scale `η` on `[0, T]`. -/
def HasModulus (g : ℝ≥0 → ℝ) (T η : ℝ≥0) (a : ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ η → |g s - g t| ≤ a

/-- **Decomposition at the hitting time.**  If `W > -δ` everywhere, `W ≤ ε` up to the time `τ`
and the post-`τ` path has modulus `a`, then `W` has modulus `ε + δ + a`. -/
theorem hasModulus_of_hit {W : ℝ≥0 → ℝ} {τ T η : ℝ≥0} {ε δ a : ℝ} (hW : ∀ t, -δ < W t)
    (hle : ∀ t ≤ τ, W t ≤ ε) (hZ : HasModulus (fun u => W (τ + u)) T η a) (ha : 0 ≤ a) :
    HasModulus W T η (ε + δ + a) := by
  have hεδ : 0 ≤ ε + δ := by
    have h1 := hW τ
    have h2 := hle τ le_rfl
    linarith
  have key : ∀ s t : ℝ≥0, s < τ → τ ≤ t → s ≤ T → t ≤ T → |(s : ℝ) - t| ≤ η →
      |W s - W t| ≤ ε + δ + a := by
    intro s t hsτ hτt hs ht hst
    have h1 : |W s - W τ| ≤ ε + δ := by
      have e1 := hW s
      have e2 := hW τ
      have e3 := hle s hsτ.le
      have e4 := hle τ le_rfl
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hts : ((t - τ : ℝ≥0) : ℝ) = (t : ℝ) - τ := NNReal.coe_sub hτt
    have hsτ' : (s : ℝ) < τ := by exact_mod_cast hsτ
    have h2 : |W τ - W t| ≤ a := by
      have := hZ 0 (t - τ) zero_le ((tsub_le_self).trans ht) (by
        rw [hts]
        have h3 : (0 : ℝ) ≤ (t : ℝ) - τ := by
          have : (τ : ℝ) ≤ t := by exact_mod_cast hτt
          linarith
        rw [NNReal.coe_zero, zero_sub, abs_neg, abs_of_nonneg h3]
        have h4 : |(s : ℝ) - t| = (t : ℝ) - s := by
          rw [abs_sub_comm, abs_of_nonneg]
          have : (s : ℝ) ≤ t := by linarith
          linarith
        rw [h4] at hst
        linarith)
      simpa [add_tsub_cancel_of_le hτt] using this
    calc |W s - W t| = |(W s - W τ) + (W τ - W t)| := by ring_nf
      _ ≤ |W s - W τ| + |W τ - W t| := abs_add_le _ _
      _ ≤ ε + δ + a := by linarith
  intro s t hs ht hst
  by_cases hsτ : s < τ
  · by_cases htτ : t < τ
    · have e1 := hW s
      have e2 := hW t
      have e3 := hle s hsτ.le
      have e4 := hle t htτ.le
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · exact key s t hsτ (not_lt.1 htτ) hs ht hst
  · by_cases htτ : t < τ
    · rw [abs_sub_comm]
      exact key t s htτ (not_lt.1 hsτ) ht hs (by rwa [abs_sub_comm])
    · have hsτ' := not_lt.1 hsτ
      have htτ' := not_lt.1 htτ
      have := hZ (s - τ) (t - τ) ((tsub_le_self).trans hs) ((tsub_le_self).trans ht) (by
        rw [NNReal.coe_sub hsτ', NNReal.coe_sub htτ']
        convert hst using 2
        ring)
      simp only [add_tsub_cancel_of_le hsτ', add_tsub_cancel_of_le htτ'] at this
      linarith

/-- The paths with two times of the countable set `D` in `[0, T]`, at distance at most `η`, whose
values differ by more than `a`. -/
def badPath (D : Set ℝ≥0) (T η : ℝ≥0) (a : ℝ) : Set (ℝ≥0 → ℝ) :=
  {g | ∃ s ∈ D, ∃ t ∈ D, s ≤ T ∧ t ≤ T ∧ |(s : ℝ) - t| ≤ η ∧ a < |g s - g t|}

/-- The set `badPath` is measurable for the product σ-algebra. -/
theorem measurableSet_badPath {D : Set ℝ≥0} (hD : D.Countable) (T η : ℝ≥0) (a : ℝ) :
    MeasurableSet (badPath D T η a) :=
  measurableSet_badMod (B := fun t (g : ℝ≥0 → ℝ) => g t) hD (fun t => measurable_pi_apply t) T η a

/-- A continuous path outside `badPath D T' η' a`, for a dense set `D`, has modulus `a` at scale
`η` on `[0, T]` (`T < T'`, `η < η'`). -/
theorem hasModulus_of_not_mem_badPath {D : Set ℝ≥0} (hD : Dense D) {g : ℝ≥0 → ℝ}
    (hg : Continuous g) {T T' η η' : ℝ≥0} (hT : T < T') (hη : η < η') {a : ℝ}
    (hbad : g ∉ badPath D T' η' a) : HasModulus g T η a := by
  intro s t hs ht hst
  exact abs_sub_le_of_not_badMod (B := fun t (_ : Unit) => g t) hD (fun _ => hg) hT hη
    (ω := ()) hbad hs ht hst

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit mΩ in
/-- Up to the truncated hitting time of the level `ε`, the drifted motion stays at most `ε`. -/
theorem drift_le_of_le_hitDriftTrunc (hcont : ∀ ω, Continuous fun s => B s ω) (c : ℝ) {ε : ℝ}
    (hε : 0 < ε) {η : ℝ≥0} {ω : Ω} (h0 : B 0 ω = 0) (h : hitDrift B c ε ω ≤ (η : ℝ≥0∞))
    {t : ℝ≥0} (ht : t ≤ hitDriftTrunc B c ε η ω) : B t ω + c * t ≤ ε := by
  set τ := hitDriftTrunc B c ε η ω with hτdef
  have hcoe : ((τ : ℝ≥0) : ℝ≥0∞) = hitDrift B c ε ω := coe_hitDriftTrunc_of_le B c ε η ω h
  have hlt : ∀ x : ℝ≥0, x < τ → B x ω + c * x < ε := by
    intro x hx
    by_contra hge
    have := (hitDrift_le_iff hcont c ε ω x).2 ⟨x, le_rfl, not_lt.1 hge⟩
    rw [← hcoe] at this
    exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hx)
  rcases ht.lt_or_eq with ht | ht
  · exact (hlt t ht).le
  · rw [ht]
    by_cases hτ0 : τ = 0
    · rw [hτ0]
      simp [h0, hε.le]
    · have hY : Continuous fun s : ℝ≥0 => B s ω + c * s :=
        (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
      have hpos : (Set.Iio τ).Nonempty := ⟨0, pos_iff_ne_zero.2 hτ0⟩
      have hcl : τ ∈ closure (Set.Iio τ) := by rw [closure_Iio' hpos]; exact Set.mem_Iic.2 le_rfl
      exact (isClosed_le hY (continuous_const (y := ε))).closure_subset_iff.2
        (fun x hx => (hlt x hx).le) hcl

omit mΩ in
/-- **The decomposition at the hitting time for the drifted motion.** -/
theorem hasModulus_stayAbove_of_not_badPath (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ}
    {ε δ : ℝ} (hε : 0 < ε) {η0 : ℝ≥0} {D : Set ℝ≥0} (hD : Dense D) {T T' η η' : ℝ≥0}
    (hT : T < T') (hη : η < η') {a : ℝ} (ha : 0 ≤ a) {ω : Ω} (h0 : B 0 ω = 0)
    (hG : ∀ t : ℝ≥0, -δ < B t ω + c * t) (hτ : hitDrift B c ε ω ≤ (η0 : ℝ≥0∞))
    (hbad : driftIncr B c (hitDriftTrunc B c ε η0) ω ∉ badPath D T' η' a) :
    HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η (ε + δ + a) := by
  set τ := hitDriftTrunc B c ε η0 ω with hτdef
  have hY : Continuous fun s : ℝ≥0 => B s ω + c * s :=
    (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
  have hincr : Continuous (driftIncr B c (hitDriftTrunc B c ε η0) ω) := by
    unfold driftIncr
    exact (hY.comp (continuous_const.add continuous_id)).sub continuous_const
  have hZ := hasModulus_of_not_mem_badPath hD hincr hT hη hbad
  refine hasModulus_of_hit (τ := τ) hG (fun t ht => drift_le_of_le_hitDriftTrunc hcont c hε h0 hτ ht)
    ?_ ha
  intro u v hu hv huv
  have := hZ u v hu hv huv
  simp only [driftIncr] at this
  convert this using 2
  ring


/-- **Conditional bound for the post-hitting increments.**  On `G_δ ∩ {τ ≤ η}`, the restarted
increments of `B + c ·` after the hitting time of `ε` lie in the measurable set `S` with
probability at most that of the drifted motion in `S`, divided by `1 - e^{-2c(ε+δ)}`. -/
theorem measure_stayAbove_inter_mem_mul_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ S}) *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) ≤
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ S} := by
  have hτ := isStoppingTime_hitDriftTrunc hm hcont c ε η
  have hincr := measurable_driftIncr hm hcont c (measurable_of_isStoppingTime_nnreal hm hτ)
  have hY : Measurable (fun ω (t : ℝ≥0) => B t ω + c * (t : ℝ)) :=
    measurable_pi_iff.2 fun t => (hm t).add measurable_const
  have h1 := lintegral_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η
    (Φ := S.indicator 1) (measurable_const.indicator hS)
  have hL : ∫⁻ ω in {ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)},
      S.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
        (driftIncr B c (hitDriftTrunc B c ε η) ω) ∂P =
      P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ S}) := by
    have hfun : (fun ω => S.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
        (driftIncr B c (hitDriftTrunc B c ε η) ω)) =
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ S}.indicator 1 := by
      ext ω; simp [Set.indicator]
    have hmS : MeasurableSet {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ S} := hincr hS
    rw [hfun, lintegral_indicator_one hmS, Measure.restrict_apply hmS, Set.inter_comm]
  have hR : ∫⁻ ω in {ω | ∀ t : ℝ≥0, -(ε + δ) < B t ω + c * t},
      S.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∂P ≤
      P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ S} := by
    have hfun : (fun ω => S.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)
        (fun t : ℝ≥0 => B t ω + c * (t : ℝ))) =
        {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ S}.indicator 1 := by
      ext ω; simp [Set.indicator]
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hmS : MeasurableSet {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ S} := hY hS
    rw [hfun, lintegral_indicator_one hmS]
  rw [hL] at h1
  have h2 := measure_stayAbove_inter_hitDrift_le hB hm hcont hc hε hδ η
  calc _ = (P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) * _) * _ := by rw [h1]
    _ ≤ (P (topFirst B c ε δ ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        P {ω | (fun t : ℝ≥0 => B t ω + c * (t : ℝ)) ∈ S}) *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) := by gcongr
    _ = _ := by rw [h2]; ring

/-- **Conditional modulus bound.**  On `G_δ ∩ {τ ≤ η}`, the restarted increments after the hitting
time of `ε` have the Brownian modulus bound, divided by `1 - e^{-2c(ε+δ)}`. -/
theorem measure_stayAbove_inter_badPath_mul_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (η : ℝ≥0) {D : Set ℝ≥0} (hD : D.Countable) (T η' : ℝ≥0)
    (hη' : 0 < η') {a : ℝ} (ha : c * η' < a) :
    P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ badPath D T η' a}) *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) ≤
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        (((⌈(T : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
          (4 * ENNReal.ofReal (Real.exp (-(((a - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ)))))))) := by
  refine (measure_stayAbove_inter_mem_mul_le hB hm hcont hc hε hδ η
    (measurableSet_badPath hD T η' a)).trans ?_
  gcongr
  refine le_trans (measure_mono ?_)
    (measure_badMod_le hB D T η' hη' (a := a - c * η') (by linarith))
  rintro ω ⟨s, hsD, t, htD, hsT, htT, hst, hlt⟩
  refine ⟨s, hsD, t, htD, hsT, htT, hst, ?_⟩
  have h1 : |((B s ω + c * s) - (B t ω + c * t))| ≤ |B s ω - B t ω| + c * η' := by
    have : (B s ω + c * s) - (B t ω + c * t) = (B s ω - B t ω) + c * ((s : ℝ) - t) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hc]
    gcongr
  linarith


/-- **The modulus of the conditioned drifted motion.**  On `G_δ ∩ {τ ≤ η}`, the drifted motion
`B + c ·` has modulus `ε + δ + a` at scale `η₁ < η'` on `[0, T]` except on an event whose
probability, multiplied by `1 - e^{-2c(ε+δ)}`, is at most `P(G_δ ∩ {τ ≤ η})` times the Brownian
modulus bound at the scale `η'` on `[0, T']`, `T < T'`, with the level `a - c η'`. -/
theorem measure_stayAbove_inter_not_hasModulus_mul_le [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun s => B s ω) {c : ℝ} (hc : 0 < c) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (η : ℝ≥0) {D : Set ℝ≥0} (hD : D.Countable) (hDd : Dense D)
    {T T' η₁ η' : ℝ≥0} (hT : T < T') (hη₁ : η₁ < η') (hη' : 0 < η') {a : ℝ} (ha : c * η' < a) :
    P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₁ (ε + δ + a)}) *
        ENNReal.ofReal (1 - Real.exp (-(2 * c * (ε + δ)))) ≤
      P ({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) *
        (((⌈(T' : ℝ) / η'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
          (4 * ENNReal.ofReal (Real.exp (-(((a - c * η') / 2) ^ 2 / (32 * (2 * (η' : ℝ)))))))) := by
  have h0 : ∀ᵐ ω ∂P, B 0 ω = 0 :=
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero.mono fun ω h => h
  have ha0 : 0 ≤ a := by
    have : 0 ≤ c * (η' : ℝ) := by positivity
    linarith
  have hsub : P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | ¬ HasModulus (fun t : ℝ≥0 => B t ω + c * t) T η₁ (ε + δ + a)}) ≤
      P (({ω | ∀ t : ℝ≥0, -δ < B t ω + c * t} ∩ {ω | hitDrift B c ε ω ≤ (η : ℝ≥0∞)}) ∩
        {ω | driftIncr B c (hitDriftTrunc B c ε η) ω ∈ badPath D T' η' a}) := by
    refine measure_mono_ae ?_
    filter_upwards [h0] with ω h0ω hω
    by_contra hnot
    exact hω.2 (hasModulus_stayAbove_of_not_badPath hcont hε hDd hT hη₁ ha0 h0ω hω.1.1 hω.1.2
      fun h => hnot ⟨hω.1, h⟩)
  exact (mul_le_mul' hsub le_rfl).trans
    (measure_stayAbove_inter_badPath_mul_le hB hm hcont hc hε hδ η hD T' η' hη' ha)

end Prob

end LatticeProb
