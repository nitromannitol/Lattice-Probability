import Mathlib

/-!
# Circle integrability of random radial profiles

Let `X ω : ℝ → ℝ` be a random function of the radius which is almost surely continuous on `(0, ∞)`, measurable in
`ω` at each positive radius, and whose first absolute moment grows at most logarithmically at the origin:
`E |X(ρ)| ≤ C (1 - log ρ)` for `0 < ρ ≤ 1`. Then for every circle `∂B_R(c)`, almost surely the radial function
`x ↦ X(|x|)` is integrable on that circle (`ae_circleIntegrable_comp_norm`), including the circles through the
origin, where `|x|` vanishes at one point. Away from the origin this is continuity; near the origin it is Tonelli's
theorem together with the integrability of `log |x|` on circles.

A typical example is the radial part `ρ ↦ h_ρ(0)` of a log-correlated field (with a logarithmic singularity):
`h_{e^{-t}}(0)` is a Brownian motion with drift, whose first absolute moment at time `t` is `O(1 + t)`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal Interval

namespace LatticeProb.RadialCircle

/-- A circle of nonzero radius passes through a given point at a Lebesgue-null set of angles (at most a coset of
`2π ℤ`). -/
theorem volume_setOf_circleMap_eq (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    volume {θ : ℝ | circleMap c R θ = a} = 0 := by
  by_cases hne : ∃ θ₁, circleMap c R θ₁ = a
  · obtain ⟨θ₁, hθ₁⟩ := hne
    refine measure_mono_null ?_
      ((Set.countable_range fun n : ℤ => θ₁ + n * (2 * Real.pi)).measure_zero _)
    intro θ hθ
    have h : circleMap c R θ = circleMap c R θ₁ := (hθ : circleMap c R θ = a).trans hθ₁.symm
    obtain ⟨n, hn⟩ := (circleMap_eq_circleMap_iff c hR).1 h
    refine ⟨n, ?_⟩
    have h2 : ((θ₁ + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I = (θ : ℂ) * Complex.I := by
      rw [hn]; push_cast; ring
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2
  · simp only [not_exists] at hne
    have : {θ : ℝ | circleMap c R θ = a} = ∅ := Set.eq_empty_of_forall_notMem fun θ hθ => hne θ hθ
    rw [this, measure_empty]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Joint measurability.** A random function which is continuous on `(0, ∞)` for every sample and measurable in
the sample at every positive radius gives a jointly measurable function `(ρ, ω) ↦ 1_{ρ > 0} ‖Y ω ρ‖ₑ`. -/
theorem measurable_indicator_enorm_of_continuousOn {Y : Ω → ℝ → ℝ}
    (hmeas : ∀ ρ, 0 < ρ → Measurable fun ω => Y ω ρ) (hcont : ∀ ω, ContinuousOn (Y ω) (Ioi 0)) :
    Measurable (fun p : ℝ × Ω => (Ioi (0 : ℝ)).indicator (fun ρ => ‖Y p.2 ρ‖ₑ) p.1) := by
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  let F : ℕ → ℝ × Ω → ℝ≥0∞ := fun n =>
    {q : ℝ × Ω | 1 / ((n : ℝ) + 1) < q.1}.indicator
      (fun q => ‖Y q.2 (max q.1 (1 / ((n : ℝ) + 1)))‖ₑ)
  refine measurable_of_tendsto_metrizable (f := F) (fun n => ?_) ?_
  · refine Measurable.indicator ?_ (measurableSet_lt measurable_const measurable_fst)
    have hu : Measurable (Function.uncurry fun (ρ : ℝ) (ω : Ω) => Y ω (max ρ (1 / ((n : ℝ) + 1)))) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => (hcont ω).comp_continuous (continuous_id.max continuous_const)
          (fun ρ => lt_of_lt_of_le (hε n) (le_max_right _ _)))
        (fun ρ => hmeas _ (lt_of_lt_of_le (hε n) (le_max_right _ _)))
    exact hu.enorm
  · rw [tendsto_pi_nhds]
    rintro ⟨ρ, ω⟩
    by_cases hρ : 0 < ρ
    · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
      have hev : ∀ᶠ n in atTop, F n (ρ, ω) = (Ioi (0 : ℝ)).indicator (fun ρ => ‖Y ω ρ‖ₑ) ρ := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hεn : 1 / ((n : ℝ) + 1) < ρ := by
          refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hN
          exact_mod_cast Nat.add_le_add_right hn 1
        have hmem : (ρ, ω) ∈ {q : ℝ × Ω | 1 / ((n : ℝ) + 1) < q.1} := hεn
        simp only [F, Set.indicator_of_mem hmem, Set.indicator_of_mem (show ρ ∈ Ioi (0 : ℝ) from hρ),
          max_eq_left hεn.le]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
    · have hF : ∀ n, F n (ρ, ω) = 0 := fun n => by
        have hmem : (ρ, ω) ∉ {q : ℝ × Ω | 1 / ((n : ℝ) + 1) < q.1} := fun h =>
          hρ ((hε n).trans h)
        simp only [F, Set.indicator_of_notMem hmem]
      simp only [hF, Set.indicator_of_notMem (show ρ ∉ Ioi (0 : ℝ) from hρ)]
      exact tendsto_const_nhds

/-- **Circle integrability of a random radial profile.** If `X ω` is a.s. continuous on `(0, ∞)`, measurable in `ω`
at every positive radius, and `E |X(ρ)| ≤ C (1 - log ρ)` for `0 < ρ ≤ 1`, then for every circle `∂B_R(c)`
(also through the origin), almost surely `x ↦ X(|x|)` is integrable on it. -/
theorem ae_circleIntegrable_comp_norm {P : Measure Ω} [SFinite P] {X : Ω → ℝ → ℝ}
    (hmeas : ∀ ρ, 0 < ρ → Measurable fun ω => X ω ρ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (X ω) (Ioi 0)) {C : ℝ} (hC : 0 ≤ C)
    (hmom : ∀ ρ, 0 < ρ → ρ ≤ 1 → ∫⁻ ω, ‖X ω ρ‖ₑ ∂P ≤ ENNReal.ofReal (C * (1 - Real.log ρ)))
    (c : ℂ) (R : ℝ) : ∀ᵐ ω ∂P, CircleIntegrable (fun x => X ω ‖x‖) c R := by
  classical
  rcases eq_or_ne R 0 with rfl | hR
  · exact Eventually.of_forall fun ω => circleIntegrable_zero_radius
  -- a measurable null set outside of which the profile is continuous
  have hB : P {ω | ¬ ContinuousOn (X ω) (Ioi 0)} = 0 := ae_iff.1 hcont
  set T := toMeasurable P {ω | ¬ ContinuousOn (X ω) (Ioi 0)} with hTdef
  have hT : MeasurableSet T := measurableSet_toMeasurable _ _
  have hPT : P T = 0 := by rw [hTdef, measure_toMeasurable]; exact hB
  have hTae : ∀ᵐ ω ∂P, ω ∉ T := measure_eq_zero_iff_ae_notMem.1 hPT
  have hXc : ∀ ω, ω ∉ T → ContinuousOn (X ω) (Ioi 0) := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  -- the modified profile, continuous for every sample
  let Y : Ω → ℝ → ℝ := fun ω ρ => if ω ∈ T then 0 else X ω ρ
  have hYcont : ∀ ω, ContinuousOn (Y ω) (Ioi 0) := by
    intro ω
    by_cases hω : ω ∈ T
    · simp only [Y, hω, ↓reduceIte]; exact continuousOn_const
    · simp only [Y, hω, ↓reduceIte]; exact hXc ω hω
  have hYmeas : ∀ ρ, 0 < ρ → Measurable fun ω => Y ω ρ := fun ρ hρ =>
    Measurable.ite hT measurable_const (hmeas ρ hρ)
  have hρm : Measurable fun θ : ℝ => min ‖circleMap c R θ‖ 1 :=
    ((continuous_circleMap c R).norm.min continuous_const).measurable
  let G : Ω → ℝ → ℝ≥0∞ := fun ω θ =>
    (Ioi (0 : ℝ)).indicator (fun ρ => ‖Y ω ρ‖ₑ) (min ‖circleMap c R θ‖ 1)
  have hG : Measurable (Function.uncurry G) :=
    (measurable_indicator_enorm_of_continuousOn hYmeas hYcont).comp
      ((hρm.comp measurable_snd).prodMk measurable_fst)
  -- the first moment bound at each angle
  have hbound : ∀ θ, ∫⁻ ω, G ω θ ∂P ≤ ENNReal.ofReal (C * (1 + |Real.log ‖circleMap c R θ‖|)) := by
    intro θ
    by_cases hpos : 0 < min ‖circleMap c R θ‖ 1
    · have h1 : ∫⁻ ω, G ω θ ∂P = ∫⁻ ω, ‖X ω (min ‖circleMap c R θ‖ 1)‖ₑ ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hTae] with ω hω
        simp only [G, Set.indicator_of_mem (show min ‖circleMap c R θ‖ 1 ∈ Ioi (0 : ℝ) from hpos), Y, hω,
          ↓reduceIte]
      rw [h1]
      refine (hmom _ hpos (min_le_right _ _)).trans (ENNReal.ofReal_le_ofReal ?_)
      refine mul_le_mul_of_nonneg_left ?_ hC
      have : -Real.log (min ‖circleMap c R θ‖ 1) ≤ |Real.log ‖circleMap c R θ‖| := by
        rcases le_total ‖circleMap c R θ‖ 1 with h | h
        · rw [min_eq_left h]; exact neg_le_abs _
        · rw [min_eq_right h, Real.log_one, neg_zero]; exact abs_nonneg _
      linarith
    · have : ∀ ω, G ω θ = 0 := fun ω =>
        Set.indicator_of_notMem (show min ‖circleMap c R θ‖ 1 ∉ Ioi (0 : ℝ) from hpos) _
      simp only [this, lintegral_zero, zero_le]
  -- the deterministic bound is integrable over the circle
  have hint : IntervalIntegrable (fun θ => C * (1 + |Real.log ‖circleMap c R θ‖|)) volume 0
      (2 * Real.pi) := by
    have hlog : IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - 0‖) volume 0 (2 * Real.pi) :=
      circleIntegrable_log_norm_sub_const (a := 0) (c := c) R
    simp only [sub_zero] at hlog
    exact (intervalIntegrable_const.add hlog.abs).const_mul C
  have hK : ∫⁻ θ in Ι 0 (2 * Real.pi), ENNReal.ofReal (C * (1 + |Real.log ‖circleMap c R θ‖|)) < ∞ := by
    rw [intervalIntegrable_iff] at hint
    exact hint.lintegral_lt_top
  -- Tonelli
  have htot : ∫⁻ ω, (∫⁻ θ in Ι 0 (2 * Real.pi), G ω θ) ∂P < ∞ := by
    rw [lintegral_lintegral_swap hG.aemeasurable]
    exact (lintegral_mono fun θ => hbound θ).trans_lt hK
  have hfinae : ∀ᵐ ω ∂P, ∫⁻ θ in Ι 0 (2 * Real.pi), G ω θ < ∞ :=
    ae_lt_top (f := fun ω => ∫⁻ θ in Ι 0 (2 * Real.pi), G ω θ) hG.lintegral_prod_right' htot.ne
  have hnull : ∀ᵐ θ ∂volume, θ ∉ {θ : ℝ | circleMap c R θ = 0} :=
    measure_eq_zero_iff_ae_notMem.1 (volume_setOf_circleMap_eq c 0 hR)
  filter_upwards [hfinae, hTae] with ω hfin hω
  have hXω := hXc ω hω
  -- the part of the profile at radii `≥ 1` is continuous
  have hmax : IntervalIntegrable (fun θ => X ω (max ‖circleMap c R θ‖ 1)) volume 0 (2 * Real.pi) :=
    (hXω.comp_continuous ((continuous_circleMap c R).norm.max continuous_const)
      (fun θ => show (0 : ℝ) < _ from lt_of_lt_of_le one_pos (le_max_right _ _))).intervalIntegrable _ _
  -- the part at radii `≤ 1`, through Tonelli
  let φ : ℝ → ℝ := fun θ => (Ioi (0 : ℝ)).indicator (X ω) (min ‖circleMap c R θ‖ 1)
  have hφm : Measurable φ := by
    have hpw : Measurable ((Ioi (0 : ℝ)).piecewise (X ω) 0) :=
      ContinuousOn.measurable_piecewise hXω continuousOn_const measurableSet_Ioi
    rw [Set.piecewise_eq_indicator] at hpw
    exact hpw.comp hρm
  have hφint : IntervalIntegrable φ volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff]
    refine ⟨hφm.aestronglyMeasurable, ?_⟩
    have : (fun θ => ‖φ θ‖ₑ) = G ω := by
      funext θ
      simp only [φ, G, enorm_indicator_eq_indicator_enorm, Y, hω, ↓reduceIte]
    simpa only [HasFiniteIntegral, this] using hfin
  have hmin : IntervalIntegrable (fun θ => X ω (min ‖circleMap c R θ‖ 1)) volume 0 (2 * Real.pi) := by
    rw [intervalIntegrable_iff] at hφint ⊢
    refine hφint.congr ?_
    filter_upwards [ae_restrict_of_ae hnull] with θ hθ
    have hpos : 0 < min ‖circleMap c R θ‖ 1 :=
      lt_min (norm_pos_iff.2 fun h => hθ h) one_pos
    simp only [φ, Set.indicator_of_mem (show min ‖circleMap c R θ‖ 1 ∈ Ioi (0 : ℝ) from hpos)]
  have hdecomp : (fun θ => X ω ‖circleMap c R θ‖) = fun θ =>
      X ω (max ‖circleMap c R θ‖ 1) + X ω (min ‖circleMap c R θ‖ 1) - X ω 1 := by
    funext θ
    rcases le_total ‖circleMap c R θ‖ 1 with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]; ring
  show IntervalIntegrable (fun θ => X ω ‖circleMap c R θ‖) volume 0 (2 * Real.pi)
  rw [hdecomp]
  exact (hmax.add hmin).sub intervalIntegrable_const

end LatticeProb.RadialCircle
