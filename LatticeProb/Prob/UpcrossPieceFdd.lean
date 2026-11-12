import Mathlib
import LatticeProb.Prob.UpcrossPieceGap
import LatticeProb.Prob.ConvergingTogether
import LatticeProb.Prob.UpcrossStay
import LatticeProb.Prob.BrownianDriftConditionedTightFamily

/-!
# Finite-dimensional laws of the first up-crossing piece

For Brownian motion with positive drift, the first up-crossing piece of the path
(read from the last zero before the first hit of the level `c`) is independent of the
event `staySet δ` that the path stays above `-δ`.  Conditioning on `staySet δ` and letting
`δ → 0⁺` therefore does not change the law of the piece, whereas the conditioned paths,
stopped at their first hit of `c`, converge weakly to the stopped limit path, and the piece
is uniformly close to the stopped path in probability.  Combined by the
converging-together lemma, this identifies the finite-dimensional laws of the piece with those
of the stopped limit path.

* `LatticeProb.driftLaw_staySet_pos`: the stay event has positive probability.
* `LatticeProb.integral_cond_staySet_piece_eq`: the integral of a bounded function of the piece
  is unchanged by conditioning on the stay event.
* `LatticeProb.ae_integral_comp_piece_eq`: for Lebesgue-almost every level `c > 0`, the
  finite-dimensional laws of the piece under the drifted Brownian law equal those of the
  stopped limit path.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace LatticeProb

section Fdd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Brownian motion with positive drift stays above `-δ` forever with positive probability. -/
theorem driftLaw_staySet_pos [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {δ : ℝ} (hδ : 0 < δ) : 0 < driftLaw P B hcont mu (staySet δ) := by
  have h := measure_stayAbove_pos hB hm hcont hmu hδ
  have hS : MeasurableSet (staySet δ) := measurableSet_staySet δ
  rw [driftLaw, Measure.map_apply (measurable_driftMap mu) hS,
    Measure.map_apply (measurable_pathMap B hm hcont) ((measurable_driftMap mu) hS)]
  exact h

/-- **Conditioning on the stay event does not change the law of the first up-crossing piece.**
For a bounded function `G` of the piece, the conditional expectation given `staySet δ` equals the
unconditional expectation. -/
theorem integral_cond_staySet_piece_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {G : (ℝ≥0 → ℝ) → ℝ}
    (hG : Measurable fun w : C(ℝ≥0, ℝ) => G (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) {M : ℝ}
    (hM : ∀ p, |G p| ≤ M) :
    ∫ w, G (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂((driftLaw P B hcont mu)[|staySet δ]) =
      ∫ w, G (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  have : IsProbabilityMeasure (driftLaw P B hcont mu) := isProbabilityMeasure_driftLaw hm hcont mu
  set μ := driftLaw P B hcont mu with hμ
  set S := staySet δ with hSdef
  have hS : MeasurableSet S := measurableSet_staySet δ
  have hpos : μ S ≠ 0 := (driftLaw_staySet_pos hB hm hcont hmu hδ).ne'
  set g : C(ℝ≥0, ℝ) → ℝ := fun w => G (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) with hg
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hgi : Integrable g μ :=
    Integrable.of_bound hG.aestronglyMeasurable M
      (Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hM (firstUpcrossPiece c w))
  have hD : 0 < 2 * M + 1 := by linarith
  set H : C(ℝ≥0, ℝ) → ℝ := fun w => (g w + M) / (2 * M + 1) with hH
  have hH0 : ∀ w, 0 ≤ H w := fun w => by
    have := (abs_le.1 (hM (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))).1
    exact div_nonneg (by simp only [hg]; linarith) hD.le
  have hHm : Measurable H := (hG.add_const M).div_const _
  have hHi : Integrable H μ := (hgi.add (integrable_const M)).div_const _
  set f : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal ((G p + M) / (2 * M + 1)) with hf
  have hf1 : ∀ p, f p ≤ 1 := fun p => by
    simp only [hf]
    rw [ENNReal.ofReal_le_one, div_le_one hD]
    have := (abs_le.1 (hM p)).2
    linarith
  have hfm : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) :=
    ENNReal.measurable_ofReal.comp hHm
  have key := driftLaw_mul_lintegral_piece_eq_setLIntegral_stay hB hm hcont hmu hδ hc hfm hf1
  have hfH : ∀ w : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) = ENNReal.ofReal (H w) :=
    fun w => rfl
  simp only [hfH] at key
  rw [← ofReal_integral_eq_lintegral_ofReal hHi (Eventually.of_forall hH0),
    ← ofReal_integral_eq_lintegral_ofReal hHi.integrableOn (Eventually.of_forall hH0)] at key
  have key' : μ.real S * ∫ w, H w ∂μ = ∫ w in S, H w ∂μ := by
    have := congrArg ENNReal.toReal key
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg hH0),
      ENNReal.toReal_ofReal (setIntegral_nonneg hS fun w _ => hH0 w)] at this
  have e1 : ∫ w, H w ∂μ = ((∫ w, g w ∂μ) + M) / (2 * M + 1) := by
    simp only [hH]
    rw [integral_div, integral_add hgi (integrable_const _), integral_const]
    simp
  have e2 : ∫ w in S, H w ∂μ = ((∫ w in S, g w ∂μ) + μ.real S * M) / (2 * M + 1) := by
    simp only [hH]
    rw [integral_div, integral_add hgi.integrableOn (integrable_const _), setIntegral_const]
    simp [smul_eq_mul]
  rw [e1, e2] at key'
  have hkey : μ.real S * ∫ w, g w ∂μ = ∫ w in S, g w ∂μ := by
    field_simp at key'
    linarith
  have hreal : μ.real S ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos hpos (measure_ne_top μ S)).ne'
  change ∫ w, g w ∂(μ[|S]) = ∫ w, g w ∂μ
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
    ← hkey, smul_eq_mul, inv_mul_cancel_left₀ hreal]

/-- **Finite-dimensional laws of the first up-crossing piece.**  Suppose the drifted Brownian law,
conditioned to stay above `-δ`, converges weakly to `ν` as `δ → 0⁺`.  Then for Lebesgue-almost every
level `c > 0`, the finite-dimensional laws of the first up-crossing piece under the drifted Brownian
law equal those of the path stopped at its first hit of `c` under the drifted limit law. -/
theorem ae_integral_comp_piece_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν : ∀ f : C(ℝ≥0, ℝ) →ᵇ ℝ, Tendsto
      (fun δ : ℝ => ∫ w, f w ∂((P.map (pathMap B hcont))[|driftMap mu ⁻¹' staySet δ]))
      (𝓝[>] 0) (𝓝 (∫ w, f w ∂ν))) :
    ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), ∀ (n : ℕ) (t : Fin n → ℝ≥0) (f : (Fin n → ℝ) →ᵇ ℝ),
      ∫ y, f (fun i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i)) ∂(driftLaw P B hcont mu) =
        ∫ y, f (fun i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i)) ∂(ν.map (driftMap mu)) := by
  have hWprob : IsProbabilityMeasure (P.map (pathMap B hcont)) :=
    isProb_map (measurable_pathMap B hm hcont).aemeasurable
  filter_upwards [ae_tendsto_cond_staySet_pieceGap hB hm hcont hmu hν,
    ae_tendsto_integral_cond_staySet_stopAtHit (P.map (pathMap B hcont)) mu hν,
    ae_restrict_mem measurableSet_Ioi] with c hgap hstop hc0 n t f
  have hμprob : IsProbabilityMeasure (driftLaw P B hcont mu) :=
    isProbabilityMeasure_driftLaw hm hcont mu
  set μ := driftLaw P B hcont mu with hμ
  set X : C(ℝ≥0, ℝ) → (Fin n → ℝ) :=
    fun y i => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y (t i) with hX
  set Y : C(ℝ≥0, ℝ) → (Fin n → ℝ) :=
    fun y i => firstUpcrossPiece c (y : ℝ≥0 → ℝ) (t i) with hY
  have hSm : Measurable fun y : C(ℝ≥0, ℝ) => stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y :=
    measurable_stopAt_path (measurable_hitFrom (r := fun _ => 0) measurable_const c)
  have hXm : Measurable X :=
    measurable_pi_iff.2 fun i => (continuous_eval_const (t i)).measurable.comp hSm
  have hYm : Measurable Y :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply (t i)).comp (measurable_firstUpcrossPiece c)
  -- a family of probability measures agreeing with the conditioned laws for `δ > 0`
  set Pn : ℝ → Measure C(ℝ≥0, ℝ) := fun δ => if 0 < δ then μ[|staySet δ] else μ with hPn
  have hPnprob : ∀ δ, IsProbabilityMeasure (Pn δ) := by
    intro δ
    by_cases h : 0 < δ
    · simp only [hPn, h, ↓reduceIte]
      exact cond_isProbabilityMeasure (driftLaw_staySet_pos hB hm hcont hmu h).ne'
    · simp only [hPn, h, ↓reduceIte]
      exact hμprob
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, Pn δ = μ[|staySet δ] := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 < δ := hδ
    simp only [hPn, hδ', ↓reduceIte]
  have hXν : ∀ g : (Fin n → ℝ) →ᵇ ℝ, Tendsto (fun δ : ℝ => ∫ ω, g (X ω) ∂(Pn δ)) (𝓝[>] 0)
      (𝓝 (∫ x, g x ∂((ν.map (driftMap mu)).map X))) := by
    intro g
    have hF := hstop (g.compContinuous
      ⟨fun (w : C(ℝ≥0, ℝ)) i => w (t i), continuous_pi fun i => continuous_eval_const (t i)⟩)
    rw [integral_map hXm.aemeasurable g.continuous.aestronglyMeasurable]
    refine hF.congr' ?_
    filter_upwards [hev] with δ hδ
    rw [hδ]
    rfl
  have hXY : ∀ η : ℝ, 0 < η → Tendsto (fun δ : ℝ => Pn δ {ω | η ≤ ‖Y ω - X ω‖}) (𝓝[>] 0) (𝓝 0) := by
    intro η hη
    have := hgap n (Finset.univ.sup t) t (fun i => Finset.le_sup (Finset.mem_univ i)) η hη
    refine this.congr' ?_
    filter_upwards [hev] with δ hδ
    rw [hδ]
  have hmain := tendsto_integral_comp_of_tendstoInMeasure_sub (l := 𝓝[>] (0 : ℝ)) (P := Pn)
    (X := fun _ => X) (Y := fun _ => Y) (fun _ => hXm) (fun _ => hYm) hXν hXY f
  have hconst : Tendsto (fun δ : ℝ => ∫ ω, f (Y ω) ∂(Pn δ)) (𝓝[>] 0)
      (𝓝 (∫ ω, f (Y ω) ∂μ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδ0
    rw [hδ]
    exact (integral_cond_staySet_piece_eq hB hm hcont hmu (show 0 < δ from hδ0) hc0
      (G := fun p => f (fun i => p (t i))) (f.continuous.measurable.comp hYm)
      (M := ‖f‖) fun p => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm _).symm
  have huniq := tendsto_nhds_unique hconst hmain
  rw [huniq, integral_map hXm.aemeasurable f.continuous.aestronglyMeasurable]

end Fdd

end LatticeProb
