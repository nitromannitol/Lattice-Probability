import Mathlib
import LatticeProb.Prob.PathRenewalFailure
import LatticeProb.Prob.UpcrossConcat

/-!
# Strong Markov property on path space, and the two-level gluing identity

* `LatticeProb.lintegral_stopAt_shift_driftLaw`: for Brownian motion with drift (law `driftLaw`),
  a measurable stopping functional `τ` and a measurable functional `Φ` of the pair (path stopped at
  `τ`, increments after `τ`), on `{τ < ∞}` the increments are integrated out against the law of
  the drifted Brownian path.
* `LatticeProb.lintegral_attemptSuccess_piece_driftLaw`: for levels `0 < c' < c` and a measurable
  functional `f` of a path, the integral of `f (piece_c)` over the event that, after the first hit
  of `c'`, the path hits `c` before `0`, is the integral over the first up-crossing piece to `c'`
  of the integral over the second leg of `f` of the concatenation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section StrongMarkov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Stopping a path at a measurable random time is a measurable map of paths. -/
lemma measurable_stopAt_path {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable fun w : C(ℝ≥0, ℝ) => stopAt (τ w) w := by
  refine measurable_pathValued_of_eval fun s => ?_
  exact measurable_eval_comp (τ := fun w => (min (s : ℝ≥0∞) (τ w)).toNNReal)
    (measurable_const.min hτ).ennreal_toNNReal

/-- The increments after a measurable random time form a measurable map of paths. -/
lemma measurable_shiftPath_path {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτ : Measurable τ) :
    Measurable fun w : C(ℝ≥0, ℝ) => shiftPath (τ w).toNNReal w := by
  refine measurable_pathValued_of_eval fun s => ?_
  exact (measurable_eval_comp (τ := fun w => (τ w).toNNReal + s) (hτ.ennreal_toNNReal.add_const s)).sub
    (measurable_eval_comp (τ := fun w => (τ w).toNNReal) hτ.ennreal_toNNReal)

/-- **Strong Markov property on path space.**  For Brownian motion with drift `mu`, a measurable
stopping functional `τ` and a measurable functional `Φ` of the pair (path stopped at `τ`, increments
after `τ`), on `{τ < ∞}` the increments after `τ` are integrated out against the law of the drifted
Brownian path. -/
theorem lintegral_stopAt_shift_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {τ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hτm : Measurable τ) (hτ : IsStopFun τ)
    {Φ : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ w in {w | τ w < ⊤}, Φ (stopAt (τ w) w, shiftPath (τ w).toNNReal w)
        ∂(driftLaw P B hcont mu) =
      ∫⁻ w in {w | τ w < ⊤}, ∫⁻ v, Φ (stopAt (τ w) w, v) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_driftLaw hm hcont mu
  set X : ℝ≥0 → Ω → ℝ := fun s ω => B s ω + mu * (s : ℝ) with hX
  have hXad : StronglyAdapted (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm)) X :=
    fun s => (stronglyAdapted_natFiltration_real hm s).add_const (mu * (s : ℝ))
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => X t ω := fun ω =>
    (hcont ω).add (continuous_const.mul NNReal.continuous_coe)
  have hXinc : ∀ (ω : Ω) (t s : ℝ≥0),
      X (t + s) ω - X t ω = (B (t + s) ω - B t ω) + mu * (s : ℝ) := fun ω t s => by
    simp only [hX]; push_cast; ring
  have hXm : ∀ t, Measurable (X t) := fun t => (hm t).add_const _
  have hpX : ∀ ω, pathMap X hXc ω = driftMap mu (pathMap B hcont ω) := fun ω => by
    ext s; simp [hX, pathMap_apply, driftMap_apply]
  have hpm : Measurable (pathMap X hXc) := measurable_pathMap X hXm hXc
  have hmap : P.map (pathMap X hXc) = μ := by
    rw [hμ, driftLaw, Measure.map_map (measurable_driftMap mu) (measurable_pathMap B hm hcont)]
    congr 1
  have hAm : MeasurableSet {w : C(ℝ≥0, ℝ) | τ w < ⊤} := measurableSet_lt hτm measurable_const
  have hG : Measurable fun w : C(ℝ≥0, ℝ) =>
      Φ (stopAt (τ w) w, shiftPath (τ w).toNNReal w) :=
    hΦ.comp ((measurable_stopAt_path hτm).prodMk (measurable_shiftPath_path hτm))
  have hH : Measurable fun w : C(ℝ≥0, ℝ) => ∫⁻ v, Φ (stopAt (τ w) w, v) ∂μ :=
    Measurable.lintegral_prod_right' (f := fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      Φ (stopAt (τ p.1) p.1, p.2))
      (hΦ.comp (((measurable_stopAt_path hτm).comp measurable_fst).prodMk measurable_snd))
  have key := lintegral_restart_path hB hm hcont hXad hXc hXinc
    (isStoppingTime_of_isStopFun hXad hXc hτm hτ) hΦ
  have e1 := setLIntegral_map (μ := P) (g := pathMap X hXc) hAm hG hpm
  have e2 := setLIntegral_map (μ := P) (g := pathMap X hXc) hAm hH hpm
  rw [hmap] at e1 e2
  exact e1.trans (key.trans e2.symm)

end StrongMarkov


section Gluing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Stopping a path at its first hit of `c'` does not change its first up-crossing piece to `c'`,
nor the length of that piece. -/
lemma concat_stopAt_eq {c' : ℝ} {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0) (hc' : 0 < c')
    (hτ : hitFrom c' 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    upcrossLen c' (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) = upcrossLen c' (w : ℝ≥0 → ℝ) ∧
      firstUpcrossPiece c' (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) =
        firstUpcrossPiece c' (w : ℝ≥0 → ℝ) := by
  obtain ⟨T, hτT, -, -, -⟩ := exists_hitFrom_eq w.continuous hτ
  have hend' : upcrossEnd₁ c' (w : ℝ≥0 → ℝ) = T := by
    rw [upcrossEnd₁_of_zero_start hw0]; exact hτT
  obtain ⟨hE, hSt⟩ := upcross_stopAt hc' hend'
  rw [hτT]
  refine ⟨?_, firstUpcrossPiece_stopAt c' w hend'⟩
  unfold upcrossLen; rw [hE, hSt, hend']

/-- The second-leg integral of the functional is an integral over the success event. -/
lemma lintegral_concatFunctional_right (c' c : ℝ) (f : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (u : C(ℝ≥0, ℝ)) (ν : Measure C(ℝ≥0, ℝ)) :
    ∫⁻ v, concatFunctional c' c f (u, v) ∂ν =
      ∫⁻ v in legSuccess c' c, f (concatAt (upcrossLen c' (u : ℝ≥0 → ℝ))
        (firstUpcrossPiece c' (u : ℝ≥0 → ℝ)) (legStop c' c v : ℝ≥0 → ℝ)) ∂ν := by
  rw [← lintegral_indicator (measurableSet_legSuccess c' c)]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ legSuccess c' c
  · rw [Set.indicator_of_mem hv]; simp [concatFunctional, hv]
  · rw [Set.indicator_of_notMem hv]; simp [concatFunctional, hv]

/-- **Gluing identity at two levels.**  For Brownian motion with drift `mu`, levels `0 < c' < c`
and a measurable functional `f` of a path, the integral of `f (piece_c)` over the event that, after
the first hit `τ` of `c'`, the path hits `c` before `0`, is the integral over `{τ < ∞}` of the
integral, over the increments after `τ` that hit `c - c'` before `-c'` (stopped at their exit),
of `f` of the first up-crossing piece to `c'` followed by those increments. -/
theorem lintegral_attemptSuccess_piece_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {c' c : ℝ} (hc' : 0 < c') (hcc : c' < c) {f : (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w in attemptSuccess c' c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) =
      ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
        ∫⁻ v in legSuccess c' c, f (concatAt (upcrossLen c' (w : ℝ≥0 → ℝ))
          (firstUpcrossPiece c' (w : ℝ≥0 → ℝ)) (legStop c' c v : ℝ≥0 → ℝ))
          ∂(driftLaw P B hcont mu) ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c'
  have hSM := lintegral_stopAt_shift_driftLaw hB hm hcont mu hτm (isStopFun_hitFrom_zero c')
    (Φ := concatFunctional c' c f) (measurable_concatFunctional c' c hf)
  have hAm : MeasurableSet {w : C(ℝ≥0, ℝ) | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤} :=
    measurableSet_lt hτm measurable_const
  have hFm : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) :=
    hf.comp (measurable_firstUpcrossPiece c)
  have hSm : MeasurableSet (attemptSuccess c' c) :=
    measurableSet_lt
      (measurable_hitFrom (r := fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ)) hτm c)
      (measurable_hitFrom (r := fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ)) hτm 0)
  have hSA : attemptSuccess c' c ⊆ {w : C(ℝ≥0, ℝ) | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤} := by
    intro w hw
    have : hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) <
        hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := hw
    by_contra hcon
    have h : hitFrom c' 0 (w : ℝ≥0 → ℝ) = ⊤ := by simpa using hcon
    rw [h, hitFrom_top, hitFrom_top] at this
    exact lt_irrefl _ this
  have hw0 : ∀ᵐ w : C(ℝ≥0, ℝ) ∂μ, w 0 = 0 := by
    refine (ae_driftLaw_iff hm hcont mu (p := fun w : C(ℝ≥0, ℝ) => w 0 = 0)
      (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const)).2 ?_
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h0
    simp [driftMap_apply, pathMap_apply, show B 0 ω = 0 from h0]
  have hL : ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
      concatFunctional c' c f (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w,
        shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂μ =
      ∫⁻ w in attemptSuccess c' c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ := by
    calc ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
          concatFunctional c' c f (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w,
            shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂μ
        = ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤}, (attemptSuccess c' c).indicator
            (fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) w ∂μ := by
          refine setLIntegral_congr_fun_ae hAm ?_
          filter_upwards [hw0] with w h0 hτ
          exact concatFunctional_stopAt_shift f h0 hc' hcc (ne_of_lt hτ)
      _ = ∫⁻ w, (attemptSuccess c' c).indicator
            (fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) w ∂μ :=
          setLIntegral_eq_of_support_subset ((Set.support_indicator_subset).trans hSA)
      _ = ∫⁻ w in attemptSuccess c' c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ :=
          lintegral_indicator hSm _
  rw [← hL, hSM]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hw0] with w h0 hτ
  obtain ⟨hl, hp⟩ := concat_stopAt_eq h0 hc' (ne_of_lt hτ)
  rw [lintegral_concatFunctional_right, hl, hp]

end Gluing

end LatticeProb
