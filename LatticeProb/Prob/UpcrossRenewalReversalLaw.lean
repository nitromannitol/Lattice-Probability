import Mathlib
import LatticeProb.Prob.UpcrossStrongMarkov
import LatticeProb.Prob.UpcrossRenewalReversal
import LatticeProb.Prob.UpcrossAttempt

/-!
# Gluing identity at two levels for the time-reversed up-crossing piece

For Brownian motion with drift `mu`, levels `0 < c' < c' + a` and a measurable functional `F` of a
path, the integral of `F` of the reversed first up-crossing piece to `c' + a` over the event that,
after the first hit of `c'`, the path hits `c' + a` before `0`, is the integral over `{τ < ∞}`
(`τ` the first hit of `c'`) of the integral, over the increments that hit `a` before `-c'`, of `F`
of the reversal of those increments followed by the reversed first up-crossing piece to `c'`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

lemma reflGlueFunctional_apply (c' a : ℝ) (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :
    reflGlueFunctional c' a F x =
      (legSuccess c' (c' + a)).indicator
        (fun v : C(ℝ≥0, ℝ) => F (glueFun a (-(v : ℝ≥0 → ℝ))
          (upcrossRev c' (firstUpcrossPiece c' (x.1 : ℝ≥0 → ℝ))))) x.2 := by
  unfold reflGlueFunctional
  by_cases hv : x.2 ∈ legSuccess c' (c' + a)
  · simp only [hv, ite_true, Set.indicator_of_mem]; rw [coe_glueC_neg_revPieceC]
  · simp only [hv, ite_false, Set.indicator_of_notMem, not_false_eq_true]

section Gluing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Gluing identity at two levels for the reversed piece.** -/
theorem lintegral_attemptSuccess_rev_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ)
    {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a) {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w in attemptSuccess c' (c' + a),
        F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)))
        ∂(driftLaw P B hcont mu) =
      ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
        ∫⁻ v in legSuccess c' (c' + a), F (glueFun a (-(v : ℝ≥0 → ℝ))
          (upcrossRev c' (firstUpcrossPiece c' (w : ℝ≥0 → ℝ)))) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have hcc : c' < c' + a := lt_add_of_pos_right c' ha
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c'
  have hSM := lintegral_stopAt_shift_driftLaw hB hm hcont mu hτm (isStopFun_hitFrom_zero c')
    (Φ := reflGlueFunctional c' a F) (measurable_reflGlueFunctional hc' a hF)
  have hAm : MeasurableSet {w : C(ℝ≥0, ℝ) | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤} :=
    measurableSet_lt hτm measurable_const
  have hSm : MeasurableSet (attemptSuccess c' (c' + a)) :=
    measurableSet_lt
      (measurable_hitFrom (r := fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ)) hτm (c' + a))
      (measurable_hitFrom (r := fun w : C(ℝ≥0, ℝ) => hitFrom c' 0 (w : ℝ≥0 → ℝ)) hτm 0)
  have hSA : attemptSuccess c' (c' + a) ⊆ {w : C(ℝ≥0, ℝ) | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤} := by
    intro w hw
    have : hitFrom (c' + a) (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) <
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
      reflGlueFunctional c' a F (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w,
        shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂μ =
      ∫⁻ w in attemptSuccess c' (c' + a),
        F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ))) ∂μ := by
    calc ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
          reflGlueFunctional c' a F (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w,
            shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂μ
        = ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤}, (attemptSuccess c' (c' + a)).indicator
            (fun w : C(ℝ≥0, ℝ) =>
              F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)))) w ∂μ := by
          refine setLIntegral_congr_fun_ae hAm ?_
          filter_upwards [hw0] with w h0 hτ
          obtain ⟨T, hτT, -, -, -⟩ := exists_hitFrom_eq w.continuous (ne_of_lt hτ)
          have hend' : upcrossEnd₁ c' (w : ℝ≥0 → ℝ) = T := by
            rw [upcrossEnd₁_of_zero_start h0]; exact hτT
          have hE := (upcross_stopAt hc' hend').1
          rw [reflGlueFunctional_eq_concatFunctional hc' ha F (x := (stopAt (hitFrom c' 0
            (w : ℝ≥0 → ℝ)) w, shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w))
            (by rw [hτT]; simp only [hE]; exact ENNReal.coe_ne_top) (by simp),
            concatFunctional_stopAt_shift (fun p => F (upcrossRev (c' + a) p)) h0 hc' hcc
              (ne_of_lt hτ)]
      _ = ∫⁻ w, (attemptSuccess c' (c' + a)).indicator
            (fun w : C(ℝ≥0, ℝ) =>
              F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)))) w ∂μ :=
          setLIntegral_eq_of_support_subset ((Set.support_indicator_subset).trans hSA)
      _ = ∫⁻ w in attemptSuccess c' (c' + a),
            F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ))) ∂μ :=
          lintegral_indicator hSm _
  rw [← hL, hSM]
  refine setLIntegral_congr_fun_ae hAm ?_
  filter_upwards [hw0] with w h0 hτ
  obtain ⟨-, hp⟩ := concat_stopAt_eq h0 hc' (ne_of_lt hτ)
  rw [← lintegral_indicator (measurableSet_legSuccess c' (c' + a))]
  refine lintegral_congr fun v => ?_
  rw [reflGlueFunctional_apply]
  simp only [hp]

end Gluing

end LatticeProb
