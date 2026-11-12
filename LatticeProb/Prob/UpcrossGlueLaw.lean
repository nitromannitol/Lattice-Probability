import Mathlib
import LatticeProb.Prob.UpcrossGluePathwise
import LatticeProb.Prob.UpcrossRenewalReversalR
import LatticeProb.Prob.UpcrossPieceFdd

/-!
# The glued path on the level-failure event: the law of its stopped path

Let `M` be Brownian motion with drift `mu > 0` and `R` Brownian motion with drift `-mu`, and let
`ν` be a measure on paths started at `0` such that the first up-crossing piece to the level
`c' = b - a` under `M` has the law of a path stopped at its first hit of `c'` under `ν`.  For `y`
in the level-failure event `H' = {y hits -a before c'}`, the glued path of `y` and `z` stopped at
its first hit of `b` is the reversed piece of `y` followed by `z` stopped at its first hit of `c'`
(`stopAt_glueC_of_levelFailure`).  Integrating `z` against `ν` therefore replaces the stopped path
by the first up-crossing piece under `M`:

* `LatticeProb.lintegral_stop_glue_eq_of_levelFailure`: the identity for a fixed `y`.
* `LatticeProb.lintegral_levelFailure_stop_glue_eq`: integrated over `y ∈ H'` against `R`.
* `LatticeProb.lintegral_levelFailure_stop_glue_eq_mul`: combined with the renewal identity, the
  integral equals `R(H') · ∫ F(piece_b) dM`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

lemma measurable_stopHitFun (c : ℝ) :
    Measurable fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun s => (continuous_eval_const s).measurable.comp
    (measurable_stopAt_path (measurable_hitFrom (r := fun _ => 0) measurable_const c))

section Law

variable {a b : ℝ}

/-- For `y` hitting `-a` before `b - a`, integrating the continuation `z` against a law `ν` whose
stopped paths are distributed as the first up-crossing piece under `μ` turns the stopped glued
path into the glued first up-crossing piece. -/
lemma lintegral_stop_glue_eq_of_levelFailure {y : C(ℝ≥0, ℝ)} (hab : a < b) (hy : y 0 = 0)
    (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤)
    (hlt : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) < hitFrom (b - a) 0 (y : ℝ≥0 → ℝ))
    {μ ν : Measure C(ℝ≥0, ℝ)} (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : μ.map (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) : C(ℝ≥0, ℝ)) :
        ℝ≥0 → ℝ) ∂ν =
      ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ) (firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ))) ∂μ := by
  have hG : Measurable fun p : ℝ≥0 → ℝ => F (glueFun a (y : ℝ≥0 → ℝ) p) :=
    hF.comp (measurable_glueFun_right a y)
  have h1 : ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) :
        C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν =
      ∫⁻ z, F (glueFun a (y : ℝ≥0 → ℝ)
        ((stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hν0] with z hz
    rw [stopAt_glueC_of_levelFailure hab hy hz hT hlt]
    rfl
  rw [h1, ← lintegral_map hG (measurable_stopHitFun (b - a)), ← hpiece,
    lintegral_map hG (measurable_firstUpcrossPiece (b - a))]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Integrated over the level-failure event for Brownian motion with drift `-mu`. -/
theorem lintegral_levelFailure_stop_glue_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) (hab : a < b) {ν : Measure C(ℝ≥0, ℝ)} (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : (driftLaw P B hcont mu).map
        (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in levelFailure a (b - a), ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ))
        (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν ∂(driftLaw P B hcont (-mu)) =
      ∫⁻ y in levelFailure a (b - a), ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ)
        (firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ))) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont (-mu)) := by
  refine lintegral_congr_ae ((ae_restrict_iff' (measurableSet_levelFailure a (b - a))).2 ?_)
  filter_upwards [ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hmu ha.le] with y ⟨hy, hT⟩ hyH
  exact lintegral_stop_glue_eq_of_levelFailure hab hy hT hyH hν0 hpiece hF

/-- **The level-failure part of the gluing identity.**  With the renewal identity, the integral of
`F` of the stopped glued path over the level-failure event is `R(H')` times the integral of `F`
of the first up-crossing piece to `b` under `M`. -/
theorem lintegral_levelFailure_stop_glue_eq_mul [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) (hab : a < b) {ν : Measure C(ℝ≥0, ℝ)} (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : (driftLaw P B hcont mu).map
        (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) (hF1 : ∀ p, F p ≤ 1) :
    ∫⁻ y in levelFailure a (b - a), ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ))
        (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν ∂(driftLaw P B hcont (-mu)) =
      driftLaw P B hcont (-mu) (levelFailure a (b - a)) *
        ∫⁻ w, F (firstUpcrossPiece b (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  rw [lintegral_levelFailure_stop_glue_eq hB hm hcont hmu ha hab hν0 hpiece hF]
  have h := mul_lintegral_piece_eq_levelFailure_glue hB hm hcont hmu (sub_pos.2 hab) ha hF hF1
  rw [sub_add_cancel] at h
  exact h.symm

end Law

end LatticeProb
