/-
The Laplace transform of the first zero of a Brownian motion with drift, integrated over the
starting point.

For a Brownian motion `B`, a drift `mu > 0` and a rate `q > 0`, let `τ_x` be the first time the
process `x + B s + mu * s` is at `0` (`hitFrom 0 0`, possibly `⊤`).  Then
`K = ∫ dx E[e^{-q τ_x}]` (with `e^{-q ⊤} = 0`) is positive and finite.

* For `x > 0` the process must go below `x / 2` relative to its drift, which has probability at
  most `exp (-mu * x)` (drift survival bound).
* For `x < 0`, either `τ_x ≤ T = |x| / (2 mu)`, which forces `sup_{[0,T]} B ≥ |x| / 2`
  (probability at most `exp (-mu |x| / 4)`), or `e^{-q τ_x} ≤ e^{-q T}`.
* For `x ∈ (-mu, 0)` the process reaches `0` before time `1` as soon as `B 1 > 0`, which has
  probability `1/2`, so `E[e^{-q τ_x}] ≥ e^{-q} / 2`.
-/
import Mathlib
import LatticeProb.Prob.UpcrossIntervals
import LatticeProb.Prob.BrownianExpMartingale
import LatticeProb.Prob.BrownianSupTail
import LatticeProb.Prob.BrownianFrequentPositivity

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-- The Laplace functional of the first zero of a path: `e^{-q τ}` where `τ = hitFrom 0 0 w` is
the first zero, and `0` if the path has no zero. -/
def laplaceHitZero (q : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if hitFrom 0 0 w = ⊤ then 0 else ENNReal.ofReal (Real.exp (-q * (hitFrom 0 0 w).toReal))

lemma laplaceHitZero_le_one {q : ℝ} (hq : 0 ≤ q) (w : ℝ≥0 → ℝ) : laplaceHitZero q w ≤ 1 := by
  unfold laplaceHitZero
  split_ifs with h
  · exact zero_le
  · rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_one_iff.2
    have := ENNReal.toReal_nonneg (a := hitFrom 0 0 w)
    nlinarith

lemma laplaceHitZero_eq_zero_of_forall_ne {q : ℝ} {w : ℝ≥0 → ℝ} (h : ∀ s, w s ≠ 0) :
    laplaceHitZero q w = 0 := by
  have : hitFrom 0 0 w = ⊤ := by
    simp [hitFrom, h]
  simp [laplaceHitZero, this]

/-- If the first zero comes after time `T`, the Laplace functional is at most `e^{-q T}`. -/
lemma laplaceHitZero_le_of_continuous {q : ℝ} (hq : 0 ≤ q) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    {T : ℝ} (p : Prop) [Decidable p] (hp : (∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ w t = 0) → p) :
    laplaceHitZero q w ≤ (if p then 1 else 0) + ENNReal.ofReal (Real.exp (-(q * T))) := by
  unfold laplaceHitZero
  by_cases htop : hitFrom 0 0 w = ⊤
  · simp [htop]
  · obtain ⟨s, hs, -, hws, -⟩ := exists_hitFrom_eq hw htop
    simp only [htop, ↓reduceIte]
    by_cases hsT : (s : ℝ) ≤ T
    · have hpp : p := hp ⟨s, hsT, hws⟩
      simp only [hpp, ↓reduceIte]
      calc ENNReal.ofReal (Real.exp (-q * (hitFrom 0 0 w).toReal)) ≤ 1 := by
            have := laplaceHitZero_le_one hq w
            simpa [laplaceHitZero, htop] using this
        _ ≤ 1 + _ := le_self_add
    · have hTs : T < s := not_le.1 hsT
      have h1 : ENNReal.ofReal (Real.exp (-q * (hitFrom 0 0 w).toReal)) ≤
          ENNReal.ofReal (Real.exp (-(q * T))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [hs, ENNReal.coe_toReal]
        nlinarith
      exact h1.trans le_add_self

lemma continuous_driftPath {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (ω : Ω) (x mu : ℝ) : Continuous fun s : ℝ≥0 => x + B s ω + mu * s := by
  have := hcont ω
  fun_prop

section Bounds

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- Starting point `x > 0`: the first zero exists only if the drifted process goes below `-x/2`. -/
lemma lintegral_laplaceHitZero_le_of_pos (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu q : ℝ}
    (hmu : 0 < mu) (hq : 0 ≤ q) {x : ℝ} (hx : 0 < x) :
    ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P ≤
      ENNReal.ofReal (Real.exp (-(mu * x))) := by
  classical
  have hbound : ∀ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ≤
      {ω | ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)}.indicator 1 ω := by
    intro ω
    by_cases hω : ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)
    · have hmem : ω ∈ {ω | ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)} := hω
      rw [Set.indicator_of_mem hmem]
      exact laplaceHitZero_le_one hq _
    · have hmem : ω ∉ {ω | ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)} := hω
      rw [Set.indicator_of_notMem hmem]
      rw [laplaceHitZero_eq_zero_of_forall_ne]
      intro s hs
      have hs' : x + B s ω + mu * s = 0 := hs
      exact hω ⟨s, by linarith⟩
  calc ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P
      ≤ ∫⁻ ω, {ω | ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)}.indicator 1 ω ∂P :=
        lintegral_mono hbound
    _ ≤ P {ω | ∃ t : ℝ≥0, B t ω + mu * t < -(x / 2)} := lintegral_indicator_one_le _
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * mu * (x / 2)))) :=
        measure_exists_drift_lt_le hB hm hcont hmu (x / 2)
    _ = ENNReal.ofReal (Real.exp (-(mu * x))) := by
        congr 2; ring

/-- Starting point `x < 0`: either the first zero is before `T = |x| / (2 mu)`, which forces the
Brownian motion above `|x| / 2` before time `T`, or `e^{-q τ} ≤ e^{-q T}`. -/
lemma lintegral_laplaceHitZero_le_of_neg (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu q : ℝ}
    (hmu : 0 < mu) (hq : 0 ≤ q) {x : ℝ} (hx : x < 0) :
    ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P ≤
      ENNReal.ofReal (Real.exp (-(mu * (-x) / 4))) +
        ENNReal.ofReal (Real.exp (-(q * ((-x) / (2 * mu))))) := by
  classical
  set T : ℝ := (-x) / (2 * mu) with hT
  set a : ℝ := (-x) / 2 with ha
  have hTpos : 0 < T := div_pos (neg_pos.2 hx) (by linarith)
  have hapos : 0 < a := half_pos (neg_pos.2 hx)
  have hmuT : mu * T = a := by
    rw [hT, ha]; field_simp
  have hbound : ∀ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ≤
      {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω}.indicator 1 ω +
        ENNReal.ofReal (Real.exp (-(q * T))) := by
    intro ω
    have h := laplaceHitZero_le_of_continuous hq (continuous_driftPath hcont ω x mu)
      (T := T) (ω ∈ {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω}) (by
        rintro ⟨t, htT, ht0⟩
        have ht0' : x + B t ω + mu * t = 0 := ht0
        refine ⟨t, htT, ?_⟩
        have : mu * (t : ℝ) ≤ mu * T := mul_le_mul_of_nonneg_left htT hmu.le
        linarith)
    simpa [Set.indicator_apply] using h
  have hP : P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) :=
    measure_exists_le_ge_le_exp hB hm (Filter.Eventually.of_forall hcont) hTpos hapos
  have hexp : a ^ 2 / (2 * T) = mu * (-x) / 4 := by
    rw [hT, ha]; field_simp; ring
  calc ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P
      ≤ ∫⁻ ω, ({ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω}.indicator 1 ω +
        ENNReal.ofReal (Real.exp (-(q * T)))) ∂P := lintegral_mono hbound
    _ = ∫⁻ ω, {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω}.indicator 1 ω ∂P +
        ∫⁻ _ω, ENNReal.ofReal (Real.exp (-(q * T))) ∂P :=
        lintegral_add_right _ measurable_const
    _ ≤ P {ω | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ a ≤ B t ω} + ENNReal.ofReal (Real.exp (-(q * T))) := by
        gcongr
        · exact lintegral_indicator_one_le _
        · simp
    _ ≤ _ := by
        rw [hexp] at hP
        exact add_le_add hP le_rfl

omit [IsProbabilityMeasure P] in
/-- Starting point `x ∈ (-mu, 0)`: the process reaches `0` before time `1` as soon as `B 1 > 0`. -/
lemma le_lintegral_laplaceHitZero_of_mem_Ioo (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu q : ℝ}
    (hq : 0 ≤ q) {x : ℝ} (hx0 : x < 0) (hxmu : -mu < x) :
    ENNReal.ofReal (Real.exp (-q)) * 2⁻¹ ≤
      ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P := by
  classical
  set S : Set Ω := {ω | B 0 ω = 0 ∧ 0 < B 1 ω} with hS
  have hSm : MeasurableSet S :=
    ((hm 0) (measurableSet_singleton 0)).inter ((hm 1) measurableSet_Ioi)
  have hP1 : P {ω | 0 < B 1 ω} = 2⁻¹ := by
    have h1 := (hB.hasLaw_eval 1).map_eq
    have h2 : (P.map (B 1)) (Ioi 0) = P (B 1 ⁻¹' Ioi 0) :=
      Measure.map_apply (hm 1) measurableSet_Ioi
    rw [h1] at h2
    have h3 := gaussianReal_zero_measure_Ioi (t := 1) one_ne_zero
    exact (h2.symm.trans h3)
  have hPS : (2⁻¹ : ℝ≥0∞) ≤ P S := by
    have hnull : P {ω | ¬ B 0 ω = 0} = 0 := ae_iff.1 hB.eval_zero_ae_eq_zero
    have hsub : {ω | 0 < B 1 ω} ⊆ S ∪ {ω | ¬ B 0 ω = 0} := by
      intro ω hω
      by_cases h0 : B 0 ω = 0
      · exact Or.inl ⟨h0, hω⟩
      · exact Or.inr h0
    calc (2⁻¹ : ℝ≥0∞) = P {ω | 0 < B 1 ω} := hP1.symm
      _ ≤ P (S ∪ {ω | ¬ B 0 ω = 0}) := measure_mono hsub
      _ ≤ P S + P {ω | ¬ B 0 ω = 0} := measure_union_le _ _
      _ = P S := by rw [hnull, add_zero]
  have hbound : ∀ ω, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-q))) ω ≤
      laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      obtain ⟨h0, h1⟩ := hω
      have hw := continuous_driftPath hcont ω x mu
      have hlo : (fun s : ℝ≥0 => x + B s ω + mu * s) 0 ≤ 0 := by
        simp [h0, hx0.le]
      have hhi : 0 ≤ (fun s : ℝ≥0 => x + B s ω + mu * s) 1 := by
        simp only [NNReal.coe_one, mul_one]; linarith
      obtain ⟨s, hs1, hs0⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ≥0) ≤ 1)
        hw.continuousOn ⟨hlo, hhi⟩
      have hle : hitFrom 0 0 (fun s : ℝ≥0 => x + B s ω + mu * s) ≤ s :=
        hitFrom_le zero_le hs0
      have hne : hitFrom 0 0 (fun s : ℝ≥0 => x + B s ω + mu * s) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      unfold laplaceHitZero
      simp only [hne, ↓reduceIte]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have h3 := ENNReal.toReal_mono ENNReal.coe_ne_top hle
      rw [ENNReal.coe_toReal] at h3
      have h4 : (s : ℝ) ≤ 1 := by exact_mod_cast hs1.2
      nlinarith
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  calc ENNReal.ofReal (Real.exp (-q)) * 2⁻¹
      ≤ ENNReal.ofReal (Real.exp (-q)) * P S := by gcongr
    _ = ∫⁻ ω, S.indicator (fun _ => ENNReal.ofReal (Real.exp (-q))) ω ∂P :=
        (lintegral_indicator_const hSm _).symm
    _ ≤ _ := lintegral_mono hbound

/-- Finiteness of the integral over the starting point. -/
lemma lintegral_lintegral_laplaceHitZero_lt_top (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu q : ℝ}
    (hmu : 0 < mu) (hq : 0 < q) :
    ∫⁻ x : ℝ, ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P ∂volume < ⊤ := by
  classical
  set c : ℝ := min (mu / 4) (q / (2 * mu)) with hc
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c ≤ mu / 4 := min_le_left _ _
  have hc2 : c ≤ q / (2 * mu) := min_le_right _ _
  set I : ℝ → ℝ≥0∞ := fun x => ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P
    with hI
  have hpos : ∀ x ∈ Ioi (0 : ℝ), I x ≤ ENNReal.ofReal (Real.exp (-c * x)) := by
    intro x hx
    refine (lintegral_laplaceHitZero_le_of_pos hB hm hcont hmu hq.le (Set.mem_Ioi.1 hx)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have hx' : 0 < x := hx
    nlinarith
  have hneg : ∀ x ∈ (Ioi (0 : ℝ))ᶜ, I x ≤ 2 * ENNReal.ofReal (Real.exp (c * x)) := by
    intro x hx
    have hx0 : x ≤ 0 := by simpa using hx
    rcases hx0.lt_or_eq with hlt | heq
    · refine (lintegral_laplaceHitZero_le_of_neg hB hm hcont hmu hq.le hlt).trans ?_
      rw [two_mul (ENNReal.ofReal (Real.exp (c * x)))]
      apply add_le_add
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        nlinarith
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have : q * ((-x) / (2 * mu)) = (q / (2 * mu)) * (-x) := by ring
        rw [this]
        nlinarith
    · subst heq
      have h1 : I 0 ≤ 1 := by
        calc I 0 ≤ ∫⁻ _ω, 1 ∂P := lintegral_mono fun ω => laplaceHitZero_le_one hq.le _
          _ = 1 := by simp
      refine h1.trans ?_
      simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
      norm_num
  have hsplit := lintegral_add_compl I (measurableSet_Ioi (a := (0 : ℝ))) (μ := volume)
  rw [← hsplit]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · calc ∫⁻ x in Ioi (0 : ℝ), I x ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c * x)) :=
          setLIntegral_mono' measurableSet_Ioi hpos
      _ < ⊤ := (exp_neg_integrableOn_Ioi 0 hcpos).lintegral_lt_top
  · rw [compl_Ioi] at hneg ⊢
    calc ∫⁻ x in Iic (0 : ℝ), I x ≤ ∫⁻ x in Iic (0 : ℝ), 2 * ENNReal.ofReal (Real.exp (c * x)) :=
          setLIntegral_mono' measurableSet_Iic hneg
      _ = 2 * ∫⁻ x in Iic (0 : ℝ), ENNReal.ofReal (Real.exp (c * x)) :=
          lintegral_const_mul' _ _ (by norm_num)
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num)
          ((integrableOn_exp_mul_Iic hcpos 0).lintegral_lt_top)

omit [IsProbabilityMeasure P] in
/-- Positivity of the integral over the starting point. -/
lemma lintegral_lintegral_laplaceHitZero_pos (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu q : ℝ}
    (hmu : 0 < mu) (hq : 0 < q) :
    0 < ∫⁻ x : ℝ, ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P ∂volume := by
  classical
  set c' : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-q)) * 2⁻¹ with hc'
  have hc'pos : 0 < c' := ENNReal.mul_pos (by simp [Real.exp_pos]) (by simp)
  have hle : ∀ x, (Ioo (-mu) 0).indicator (fun _ => c') x ≤
      ∫⁻ ω, laplaceHitZero q (fun s : ℝ≥0 => x + B s ω + mu * s) ∂P := by
    intro x
    by_cases hx : x ∈ Ioo (-mu) 0
    · rw [Set.indicator_of_mem hx]
      exact le_lintegral_laplaceHitZero_of_mem_Ioo hB hm hcont hq.le hx.2 hx.1
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc 0 < c' * volume (Ioo (-mu) 0) := by
        refine ENNReal.mul_pos hc'pos.ne' ?_
        simp [hmu]
    _ = ∫⁻ x, (Ioo (-mu) 0).indicator (fun _ => c') x ∂volume :=
        (lintegral_indicator_const measurableSet_Ioo _).symm
    _ ≤ _ := lintegral_mono hle

end Bounds

/-- For a Brownian motion `B` with continuous paths, a drift `mu > 0` and a rate `q > 0`, the
integral over the starting point `x ∈ ℝ` (Lebesgue measure) of the Laplace transform
`E[e^{-q τ_x}]` of the first zero `τ_x` of `x + B s + mu * s` (with `e^{-q ⊤} = 0`) is positive
and finite. -/
theorem lintegral_lebesgue_laplace_hit_zero_pos_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ w, Continuous fun t => B t w) {mu q : ℝ}
    (hmu : 0 < mu) (hq : 0 < q) :
    let K := ∫⁻ x : ℝ, ∫⁻ w, (if hitFrom 0 0 (fun s => x + B s w + mu * s) = ⊤ then 0 else
      ENNReal.ofReal (Real.exp (-q * (hitFrom 0 0 (fun s => x + B s w + mu * s)).toReal))) ∂P
      ∂volume
    0 < K ∧ K < ⊤ :=
  ⟨lintegral_lintegral_laplaceHitZero_pos hB.toIsPreBrownianReal hm hcont hmu hq,
    lintegral_lintegral_laplaceHitZero_lt_top hB.toIsPreBrownianReal hm hcont hmu hq⟩

end LatticeProb
