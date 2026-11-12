import Mathlib
import LatticeProb.Prob.UpcrossRenewalReversalLaw
import LatticeProb.Prob.UpcrossPieceLaw
import LatticeProb.Prob.UpcrossGlueMeasure
import LatticeProb.Prob.UpcrossDriftLawNeg

/-!
# Reversal of the up-crossing piece: the renewal identity

For Brownian motion `M` with drift `mu > 0`, levels `0 < c'` and `a > 0`, and `R` the law of
Brownian motion with drift `-mu`, a measurable functional `F ≤ 1` of a path satisfies

`R(H') · ∫ F(piece_{c'+a}) dM = ∫_{H'} ∫ F(glueFun a y (piece_{c'})) dM dR(y)`,

where `H'` is the set of paths that hit `-a` before `c'` and `glueFun a y z` is the reversal of `y`
from its first hit of `-a`, read at level `a`, followed by `z`.

* `LatticeProb.driftLaw_attemptSuccess_eq_neg_levelFailure`: the probability that the attempt at
  `c'` succeeds is the probability `R(H')`.
* `LatticeProb.lintegral_rev_glue_eq_driftLaw_neg`: Tonelli and the reflection `v ↦ -v` turn the
  two-level integral into an integral over `H'` for `R`.
* `LatticeProb.mul_lintegral_piece_eq_levelFailure_glue`: the renewal identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

lemma measurable_glueFun_right (a : ℝ) (y : ℝ≥0 → ℝ) : Measurable (glueFun a y) := by
  refine measurable_pi_iff.2 fun s => ?_
  unfold glueFun concatAt
  exact (measurable_pi_apply (s - glueTime a y)).const_add _

lemma legSuccess_add_eq_preimage_levelFailure (c' a : ℝ) :
    legSuccess c' (c' + a) = (fun v : C(ℝ≥0, ℝ) => -v) ⁻¹' levelFailure a c' := by
  ext v
  simp only [legSuccess, levelFailure, Set.mem_ofPred_eq, Set.mem_preimage, ContinuousMap.coe_neg]
  rw [show c' + a - c' = a by ring, hitFrom_neg a 0 v]
  have h := hitFrom_neg (-c') 0 (v : ℝ≥0 → ℝ)
  rw [neg_neg] at h
  rw [h]

section Renewal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Almost every path of Brownian motion with positive drift hits the level `c'`. -/
lemma ae_mem_hitFrom_lt_top [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {c' : ℝ} (hc' : 0 < c') :
    ∀ᵐ w : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont mu),
      w ∈ {w : C(ℝ≥0, ℝ) | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤} := by
  filter_upwards [ae_start_hitFrom_driftLaw hB hm hcont hmu hc'.le] with w hw
  exact lt_top_iff_ne_top.2 hw.2

/-- **Tonelli and reflection.**  The two-level integral of the gluing identity is an integral over
`H' = levelFailure a c'` for the law of Brownian motion with drift `-mu`, of the glued path from
the unreversed first up-crossing piece to `c'`. -/
theorem lintegral_rev_glue_eq_driftLaw_neg [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {c' a : ℝ} (hc' : 0 < c') {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w in {w | hitFrom c' 0 (w : ℝ≥0 → ℝ) < ⊤},
        ∫⁻ v in legSuccess c' (c' + a), F (glueFun a (-(v : ℝ≥0 → ℝ))
          (upcrossRev c' (firstUpcrossPiece c' (w : ℝ≥0 → ℝ)))) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont mu) =
      ∫⁻ y in levelFailure a c', ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ)
          (firstUpcrossPiece c' (w : ℝ≥0 → ℝ))) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont (-mu)) := by
  set M := driftLaw P B hcont mu with hM
  rw [Measure.restrict_eq_self_of_ae_mem (ae_mem_hitFrom_lt_top hB hm hcont hmu hc')]
  have hcoe : Measurable fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun s => (continuous_eval_const s).measurable
  have hJ : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      F (glueC a x.1 (revPieceC c' x.2) : ℝ≥0 → ℝ) :=
    hF.comp (hcoe.comp ((measurable_glueC a).comp
      (measurable_fst.prodMk ((measurable_revPieceC hc').comp measurable_snd))))
  have hK : Measurable fun y : C(ℝ≥0, ℝ) =>
      ∫⁻ w, F (glueC a y (revPieceC c' w) : ℝ≥0 → ℝ) ∂M := hJ.lintegral_prod_right'
  have hLS : MeasurableSet (legSuccess c' (c' + a)) := measurableSet_legSuccess c' (c' + a)
  have hpiece : Measurable fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece c' (v : ℝ≥0 → ℝ) :=
    measurable_firstUpcrossPiece c'
  -- the inner integral on the right, rewritten with the reversed piece
  have hL1 : ∀ y : C(ℝ≥0, ℝ),
      ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ) (firstUpcrossPiece c' (w : ℝ≥0 → ℝ))) ∂M =
        ∫⁻ w, F (glueC a y (revPieceC c' w) : ℝ≥0 → ℝ) ∂M := by
    intro y
    have hg : Measurable fun p : ℝ≥0 → ℝ => F (glueFun a (y : ℝ≥0 → ℝ) p) :=
      hF.comp (measurable_glueFun_right a _)
    have hrev : Measurable fun v : C(ℝ≥0, ℝ) =>
        upcrossRev c' (firstUpcrossPiece c' (v : ℝ≥0 → ℝ)) :=
      measurable_upcrossRev_firstUpcrossPiece hc'
    calc ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ) (firstUpcrossPiece c' (w : ℝ≥0 → ℝ))) ∂M
        = ∫⁻ p, F (glueFun a (y : ℝ≥0 → ℝ) p)
            ∂(M.map fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece c' (v : ℝ≥0 → ℝ)) :=
          (lintegral_map hg hpiece).symm
      _ = ∫⁻ p, F (glueFun a (y : ℝ≥0 → ℝ) p)
            ∂(M.map fun v : C(ℝ≥0, ℝ) =>
              upcrossRev c' (firstUpcrossPiece c' (v : ℝ≥0 → ℝ))) := by
          rw [map_upcrossRev_firstUpcrossPiece_driftLaw hB hm hcont hmu hc']
      _ = _ := lintegral_map hg hrev
  simp only [hL1]
  rw [← driftLaw_map_neg hB hm hcont mu,
    setLIntegral_map (measurableSet_levelFailure a c') hK measurable_neg_pathSpace,
    ← legSuccess_add_eq_preimage_levelFailure c' a]
  have hΦ : ∀ w v : C(ℝ≥0, ℝ), reflGlueFunctional c' a F (w, v) =
      (legSuccess c' (c' + a)).indicator
        (fun v : C(ℝ≥0, ℝ) => F (glueC a (-v) (revPieceC c' w) : ℝ≥0 → ℝ)) v := by
    intro w v
    unfold reflGlueFunctional
    by_cases hv : v ∈ legSuccess c' (c' + a) <;> simp [hv]
  calc ∫⁻ w, ∫⁻ v in legSuccess c' (c' + a), F (glueFun a (-(v : ℝ≥0 → ℝ))
          (upcrossRev c' (firstUpcrossPiece c' (w : ℝ≥0 → ℝ)))) ∂M ∂M
      = ∫⁻ w, ∫⁻ v, reflGlueFunctional c' a F (w, v) ∂M ∂M := by
        refine lintegral_congr fun w => ?_
        simp only [hΦ]
        exact (lintegral_indicator hLS _).symm
    _ = ∫⁻ v, ∫⁻ w, reflGlueFunctional c' a F (w, v) ∂M ∂M :=
        lintegral_lintegral_swap (measurable_reflGlueFunctional hc' a hF).aemeasurable
    _ = ∫⁻ v, (legSuccess c' (c' + a)).indicator
          (fun v : C(ℝ≥0, ℝ) => ∫⁻ w, F (glueC a (-v) (revPieceC c' w) : ℝ≥0 → ℝ) ∂M) v ∂M := by
        refine lintegral_congr fun v => ?_
        by_cases hv : v ∈ legSuccess c' (c' + a) <;> simp [hΦ, hv]
    _ = _ := lintegral_indicator hLS _

/-- **The attempt at `c'` succeeds with probability `R(H')`.** -/
theorem driftLaw_attemptSuccess_eq_neg_levelFailure [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c' a : ℝ} (hc' : 0 < c')
    (ha : 0 < a) :
    driftLaw P B hcont mu (attemptSuccess c' (c' + a)) =
      driftLaw P B hcont (-mu) (levelFailure a c') := by
  have h1 := lintegral_attemptSuccess_rev_driftLaw hB hm hcont mu hc' ha
    (F := fun _ => 1) measurable_const
  rw [Measure.restrict_eq_self_of_ae_mem (ae_mem_hitFrom_lt_top hB hm hcont hmu hc')] at h1
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    MeasureTheory.measure_univ, mul_one] at h1
  rw [← driftLaw_map_neg hB hm hcont mu, Measure.map_apply measurable_neg_pathSpace
    (measurableSet_levelFailure a c'), ← legSuccess_add_eq_preimage_levelFailure c' a]
  rw [← h1]

/-- **Renewal identity for the reversed up-crossing pieces.**  For Brownian motion with drift
`mu > 0` (law `M`), `R` the law of Brownian motion with drift `-mu`, levels `0 < c'`, `0 < a`, and
`F ≤ 1` a measurable functional of a path:
`R(H') · ∫ F(piece_{c'+a}) dM = ∫_{H'} ∫ F(glueFun a y (piece_{c'})) dM dR(y)`, with
`H' = levelFailure a c'`. -/
theorem mul_lintegral_piece_eq_levelFailure_glue [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {c' a : ℝ} (hc' : 0 < c')
    (ha : 0 < a) {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) (hF1 : ∀ p, F p ≤ 1) :
    driftLaw P B hcont (-mu) (levelFailure a c') *
        ∫⁻ w, F (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) =
      ∫⁻ y in levelFailure a c', ∫⁻ w, F (glueFun a (y : ℝ≥0 → ℝ)
          (firstUpcrossPiece c' (w : ℝ≥0 → ℝ))) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont (-mu)) := by
  have hb : 0 < c' + a := hc'.trans (lt_add_of_pos_right c' ha)
  have h6b := driftLaw_mul_lintegral_piece_eq_setLIntegral hB hm hcont hmu hc'
    (lt_add_of_pos_right c' ha) (f := fun p => F (upcrossRev (c' + a) p))
    (hF.comp (measurable_upcrossRev_firstUpcrossPiece hb)) (fun p => hF1 _)
  have hpiece : Measurable fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece (c' + a) (v : ℝ≥0 → ℝ) :=
    measurable_firstUpcrossPiece (c' + a)
  have hrev : Measurable fun v : C(ℝ≥0, ℝ) =>
      upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (v : ℝ≥0 → ℝ)) :=
    measurable_upcrossRev_firstUpcrossPiece hb
  have hL1 : ∫⁻ w, F (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) =
      ∫⁻ w, F (upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)))
        ∂(driftLaw P B hcont mu) := by
    calc ∫⁻ w, F (firstUpcrossPiece (c' + a) (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
        = ∫⁻ p, F p ∂((driftLaw P B hcont mu).map
            fun v : C(ℝ≥0, ℝ) => firstUpcrossPiece (c' + a) (v : ℝ≥0 → ℝ)) :=
          (lintegral_map hF hpiece).symm
      _ = ∫⁻ p, F p ∂((driftLaw P B hcont mu).map fun v : C(ℝ≥0, ℝ) =>
            upcrossRev (c' + a) (firstUpcrossPiece (c' + a) (v : ℝ≥0 → ℝ))) := by
          rw [map_upcrossRev_firstUpcrossPiece_driftLaw hB hm hcont hmu hb]
      _ = _ := lintegral_map hF hrev
  rw [← lintegral_rev_glue_eq_driftLaw_neg hB hm hcont hmu hc' hF,
    ← lintegral_attemptSuccess_rev_driftLaw hB hm hcont mu hc' ha hF,
    ← driftLaw_attemptSuccess_eq_neg_levelFailure hB hm hcont hmu hc' ha, hL1]
  exact h6b

end Renewal

end LatticeProb
