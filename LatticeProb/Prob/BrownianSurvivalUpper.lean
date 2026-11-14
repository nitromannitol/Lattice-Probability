import LatticeProb.Prob.BrownianDriftSurvival
import LatticeProb.Prob.BrownianRunningMinCount

/-!
# Survival upper bound for Brownian motion

For a Brownian motion `B`, `T > 0` and `x ≥ 0`, the probability that `B s - B 0` stays above `-x`
during `[0, T]` is at most `3 x / √T`:
`P (∀ s ≤ T, -x ≤ B s - B 0) ≤ 3 x / √T`.
Together with the lower bound `LatticeProb.le_measure_forall_ge_neg` this pins the survival
probability to order `x / √T`.

The route is the gambler's ruin for Brownian motion with drift
(`LatticeProb.measure_forall_drift_gt_le`) combined with the weak Markov property at the
deterministic time `T` (`LatticeProb.measure_inter_shift_mem`).  Put `c = 1 / √T` and
`δ = 3 √T / 4 < c T`.  If the path stays above `-x` during `[0, T]` and the motion restarted at
time `T` stays above `-δ - c u` for all `u ≥ 0`, then `B t - B 0 + c t > -x` for all `t ≥ 0`.  The
two events are independent, the second one has probability at least
`1 - exp (-2 c δ) = 1 - exp (-3 / 2) ≥ 2 / 3`, and the drifted event has probability at most
`1 - exp (-2 c x) ≤ 2 x / √T`.  To keep the events measurable they are read on the dyadic times
`k / 2 ^ N`, `k ≤ N 2 ^ N`; almost every path is continuous, which recovers the whole time line.

## Main results

* `LatticeProb.measure_forall_ge_neg_le_of_pos`: the bound for `x > 0`.
* `LatticeProb.measure_forall_ge_neg_le`: the bound for `x ≥ 0` (for `x = 0` it says that the
  survival event is null).
-/

open MeasureTheory ProbabilityTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- `3 ≤ exp (3 / 2)`, from `exp (1 / 2) ≥ 3 / 2` and `(3 / 2) ^ 3 = 27 / 8`. -/
theorem three_le_exp_three_div_two : (3 : ℝ) ≤ Real.exp (3 / 2) := by
  have h1 : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have h3 : Real.exp (3 / 2) = Real.exp (1 / 2) * Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have h2 : (3 / 2 : ℝ) * (3 / 2) ≤ Real.exp (1 / 2) * Real.exp (1 / 2) :=
    mul_le_mul h1 h1 (by norm_num) (Real.exp_pos _).le
  have h4 : (3 / 2 : ℝ) * (3 / 2) * (3 / 2) ≤
      Real.exp (1 / 2) * Real.exp (1 / 2) * Real.exp (1 / 2) :=
    mul_le_mul h2 h1 (by norm_num) (by positivity)
  rw [h3]
  linarith

/-- A continuous function on `ℝ≥0` which is at least `a` at the dyadic times `k / 2 ^ N` with
`k ≤ N 2 ^ N` is at least `a` everywhere. -/
theorem le_of_forall_dyadic_le_of_continuous {g : ℝ≥0 → ℝ} (hg : Continuous g) {a : ℝ}
    (h : ∀ N k : ℕ, k ≤ N * 2 ^ N → a ≤ g ((k : ℝ≥0) / 2 ^ N)) (t : ℝ≥0) : a ≤ g t := by
  by_contra hlt
  obtain ⟨N, k, hk, hgk⟩ := exists_dyadic_lt_of_continuous hg (not_le.1 hlt)
  exact not_le.2 hgk (h N k hk)

/-- **Survival upper bound, positive level.**  For `T > 0` and `x > 0`, a Brownian motion stays
above `B 0 - x` during `[0, T]` with probability at most `3 x / √T`. -/
theorem measure_forall_ge_neg_le_of_pos [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {T : ℝ≥0} (hT : 0 < T) {x : ℝ} (hx : 0 < x) :
    P {ω | ∀ s ≤ T, -x ≤ B s ω - B 0 ω} ≤ ENNReal.ofReal (3 * x / Real.sqrt T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  set r : ℝ := Real.sqrt T
  have hr0 : 0 < r := Real.sqrt_pos.2 hTr
  have hrr : r * r = T := Real.mul_self_sqrt hTr.le
  set c : ℝ := r⁻¹ with hc_def
  have hc : 0 < c := inv_pos.2 hr0
  have hcT : c * T = r := by
    rw [hc_def, ← hrr, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
  set δ : ℝ := 3 / 4 * r with hδ_def
  have hδT : δ < c * T := by
    rw [hcT, hδ_def]
    linarith
  have h2cδ : 2 * c * δ = 3 / 2 := by
    have h : r⁻¹ * r = 1 := inv_mul_cancel₀ hr0.ne'
    rw [hc_def, hδ_def]
    linear_combination (3 / 2 : ℝ) * h
  let g : ℕ → ℕ → ℝ≥0 := fun N k => (k : ℝ≥0) / 2 ^ N
  have hgmono : ∀ N, Monotone (g N) := fun N a b h => by
    simp only [g]
    gcongr
  -- the survival event before time `T`, read on the dyadic grid
  set A' : Set Ω := {ω | ∀ N k : ℕ, k ≤ N * 2 ^ N → -x ≤ B (min (g N k) T) ω - B 0 ω}
    with hA'_def
  -- the survival event of the drifted motion restarted at time `T`, read on the dyadic grid
  set Γ : Set (ℝ≥0 → ℝ) := {w | ∀ N k : ℕ, k ≤ N * 2 ^ N → -δ ≤ w (g N k) + c * g N k}
    with hΓ_def
  set F' : Set Ω := {ω | (fun u => B (T + u) ω - B T ω) ∈ Γ} with hF'_def
  -- the survival event of the drifted motion
  set E : Set Ω := {ω | ∀ t : ℝ≥0, -x < B (0 + t) ω - B 0 ω + c * t} with hE_def
  have hA'm : MeasurableSet[brownianFiltration B hm T] A' := by
    have h : A' = ⋂ N : ℕ, ⋂ k : ℕ,
        {ω | k ≤ N * 2 ^ N → -x ≤ B (min (g N k) T) ω - B 0 ω} := by
      ext ω
      simp only [hA'_def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h]
    refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun k => ?_
    by_cases hk : k ≤ N * 2 ^ N
    · simp only [hk, true_implies]
      exact ((measurable_brownianFiltration hm (min_le_right (g N k) T)).sub
        (measurable_brownianFiltration hm (zero_le : (0 : ℝ≥0) ≤ T))) measurableSet_Ici
    · simp only [hk, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  have hΓm : MeasurableSet Γ := by
    have h : Γ = ⋂ N : ℕ, ⋂ k : ℕ,
        {w : ℝ≥0 → ℝ | k ≤ N * 2 ^ N → -δ ≤ w (g N k) + c * g N k} := by
      ext w
      simp only [hΓ_def, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h]
    refine MeasurableSet.iInter fun N => MeasurableSet.iInter fun k => ?_
    by_cases hk : k ≤ N * 2 ^ N
    · simp only [hk, true_implies]
      exact ((measurable_pi_apply (g N k)).add_const _) measurableSet_Ici
    · simp only [hk, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  -- weak Markov property at time `T`
  have hprod : P (A' ∩ F') = P A' * P F' :=
    measure_inter_shift_mem hB.toIsPreBrownianReal hm T hA'm hΓm
  -- the restarted drifted motion survives with probability at least `1 - exp (-2 c δ)`
  have hFc : P F'ᶜ ≤ ENNReal.ofReal (Real.exp (-(2 * c * δ))) := by
    have hW := (hB.shift T).toIsPreBrownianReal
    have hWm : ∀ u, Measurable (fun ω => B (T + u) ω - B T ω) := fun u => (hm _).sub (hm _)
    let D : ℕ → Set Ω := fun N =>
      {ω | ∃ k ≤ N * 2 ^ N, B (T + g N k) ω - B T ω + c * g N k ≤ -δ}
    have hDmono : Monotone D := by
      refine monotone_nat_of_le_succ fun N ω hω => ?_
      obtain ⟨k, hk, hX⟩ := hω
      refine ⟨2 * k, ?_, ?_⟩
      · calc 2 * k ≤ 2 * (N * 2 ^ N) := by omega
          _ ≤ (N + 1) * 2 ^ (N + 1) := by rw [pow_succ]; nlinarith [Nat.zero_le (2 ^ N)]
      · have h : g (N + 1) (2 * k) = g N k := by
          simp only [g]
          push_cast
          rw [pow_succ]
          field_simp
        rw [h]
        exact hX
    have hsub : F'ᶜ ⊆ ⋃ N, D N := by
      intro ω hω
      simp only [hF'_def, hΓ_def, Set.mem_compl_iff, Set.mem_ofPred_eq] at hω
      push Not at hω
      obtain ⟨N, k, hk, hlt⟩ := hω
      exact Set.mem_iUnion.2 ⟨N, k, hk, hlt.le⟩
    calc P F'ᶜ ≤ P (⋃ N, D N) := measure_mono hsub
      _ = ⨆ N, P (D N) := hDmono.measure_iUnion
      _ ≤ _ := iSup_le fun N => measure_exists_drift_le hW hWm hc (hgmono N) (N * 2 ^ N) δ
  have hfF : 1 - Real.exp (-(2 * c * δ)) ≤ P.real F' := by
    have h1 : P.real F'ᶜ ≤ Real.exp (-(2 * c * δ)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hFc
    have hun : (1 : ℝ) ≤ P.real F' + P.real F'ᶜ := by
      have h := measureReal_union_le (μ := P) F' F'ᶜ
      rw [Set.union_compl_self, probReal_univ] at h
      exact h
    linarith
  -- the drifted motion survives with probability at most `1 - exp (-2 c x)`
  have hE : P.real E ≤ 1 - Real.exp (-(2 * c * x)) :=
    ENNReal.toReal_le_of_le_ofReal
      (sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_pos (mul_pos two_pos hc) hx).le)))
      (measure_forall_drift_gt_le (hB.shift 0).toIsPreBrownianReal
        (fun t => (hm _).sub (hm _)) hc hx)
  -- on a continuous path, both survival events force the drifted survival event
  have hincl : ∀ᵐ ω ∂P, ω ∈ A' ∩ F' → ω ∈ E := by
    filter_upwards [hB.cont] with ω hω hmem
    obtain ⟨hA, hF⟩ := hmem
    simp only [hA'_def, Set.mem_ofPred_eq] at hA
    simp only [hF'_def, hΓ_def, Set.mem_ofPred_eq] at hF
    have hcontA : Continuous fun s : ℝ≥0 => B (min s T) ω - B 0 ω :=
      (hω.comp (continuous_id.min continuous_const)).sub continuous_const
    have hcontF : Continuous fun u : ℝ≥0 => B (T + u) ω - B T ω + c * u :=
      ((hω.comp (continuous_const.add continuous_id)).sub continuous_const).add
        (continuous_const.mul NNReal.continuous_coe)
    have hA2 : ∀ s : ℝ≥0, -x ≤ B (min s T) ω - B 0 ω :=
      le_of_forall_dyadic_le_of_continuous (g := fun s : ℝ≥0 => B (min s T) ω - B 0 ω)
        hcontA hA
    have hF2 : ∀ u : ℝ≥0, -δ ≤ B (T + u) ω - B T ω + c * u :=
      le_of_forall_dyadic_le_of_continuous (g := fun u : ℝ≥0 => B (T + u) ω - B T ω + c * u)
        hcontF hF
    simp only [hE_def, Set.mem_ofPred_eq]
    intro t
    rw [zero_add]
    rcases le_total t T with htT | hTt
    · have h1 := hA2 t
      rw [min_eq_left htT] at h1
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
      · subst h0
        simp only [sub_self, NNReal.coe_zero, mul_zero, add_zero]
        linarith
      · have h2 : 0 < c * (t : ℝ) := mul_pos hc (by exact_mod_cast h0)
        linarith
    · have h1 := hA2 T
      rw [min_self] at h1
      have h2 := hF2 (t - T)
      rw [add_tsub_cancel_of_le hTt, NNReal.coe_sub hTt, mul_sub] at h2
      linarith
  have hPE : P (A' ∩ F') ≤ P E := measure_mono_ae hincl
  have hP : P.real (A' ∩ F') = P.real A' * P.real F' := by
    simp only [measureReal_def, hprod, ENNReal.toReal_mul]
  have hPE' : P.real (A' ∩ F') ≤ P.real E := ENNReal.toReal_mono (measure_ne_top P E) hPE
  -- numerics: `1 - exp (-3 / 2) ≥ 2 / 3` and `1 - exp (-2 c x) ≤ 2 c x`
  have hexp : Real.exp (-(3 / 2 : ℝ)) ≤ 1 / 3 := by
    have h3 := three_le_exp_three_div_two
    have hmul : Real.exp (-(3 / 2 : ℝ)) * Real.exp (3 / 2) = 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos (-(3 / 2 : ℝ))]
  have hf23 : 2 / 3 ≤ P.real F' := by
    rw [h2cδ] at hfF
    linarith
  have hEx : 1 - Real.exp (-(2 * c * x)) ≤ 2 * c * x := by
    linarith [Real.add_one_le_exp (-(2 * c * x))]
  have ha0 : 0 ≤ P.real A' := measureReal_nonneg
  have hmain : P.real A' * (2 / 3) ≤ 2 * c * x :=
    calc P.real A' * (2 / 3) ≤ P.real A' * P.real F' := mul_le_mul_of_nonneg_left hf23 ha0
      _ = P.real (A' ∩ F') := hP.symm
      _ ≤ P.real E := hPE'
      _ ≤ 1 - Real.exp (-(2 * c * x)) := hE
      _ ≤ 2 * c * x := hEx
  have hreal : P.real A' ≤ 3 * x / r := by
    have h : 3 * x / r = 3 * c * x := by
      rw [hc_def, div_eq_mul_inv]
      ring
    rw [h]
    linarith
  have hsubA : {ω | ∀ s ≤ T, -x ≤ B s ω - B 0 ω} ⊆ A' := by
    intro ω hω
    simp only [hA'_def, Set.mem_ofPred_eq] at hω ⊢
    exact fun N k _ => hω _ (min_le_right _ _)
  calc P {ω | ∀ s ≤ T, -x ≤ B s ω - B 0 ω} ≤ P A' := measure_mono hsubA
    _ = ENNReal.ofReal (P A').toReal := (ENNReal.ofReal_toReal (measure_ne_top P A')).symm
    _ ≤ ENNReal.ofReal (3 * x / r) := ENNReal.ofReal_le_ofReal hreal

/-- **Survival upper bound.**  For `T > 0` and `x ≥ 0`, a Brownian motion stays above `B 0 - x`
during `[0, T]` with probability at most `3 x / √T`.  For `x = 0` the bound is `0`: the event is
contained in the survival event at every level `y > 0`, whose probability is at most `3 y / √T`. -/
theorem measure_forall_ge_neg_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) {T : ℝ≥0} (hT : 0 < T) {x : ℝ} (hx : 0 ≤ x) :
    P {ω | ∀ s ≤ T, -x ≤ B s ω - B 0 ω} ≤ ENNReal.ofReal (3 * x / Real.sqrt T) := by
  rcases hx.lt_or_eq with hx | hx
  · exact measure_forall_ge_neg_le_of_pos hB hm hT hx
  · subst hx
    have hcont : Continuous fun y : ℝ => ENNReal.ofReal (3 * y / Real.sqrt T) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
    refine le_trans (measure_mono fun ω hω => ?_) (measure_forall_ge_neg_le_of_pos hB hm hT hy)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    intro s hs
    have h := hω s hs
    have hy' : (0 : ℝ) < y := hy
    linarith

end LatticeProb
