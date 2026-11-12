import Mathlib
import LatticeProb.Prob.UpcrossGluePathwise
import LatticeProb.Prob.UpcrossGlueMeasure
import LatticeProb.Prob.UpcrossStrongMarkov
import LatticeProb.Prob.UpcrossPieceLaw
import LatticeProb.Prob.UpcrossDriftLawNeg
import LatticeProb.Prob.StopFunctionalHit

/-!
# The glued path on the level-success event: the law of its stopped path

Let `R` be the law of Brownian motion with drift `-mu` (`mu > 0`), `M` that with drift `mu`, and
`0 < a < b`.  For `y` in the level-success event `H = {y hits b - a before -a}`, the glued path of
`y` and any continuation `z` stopped at its first hit of `b` is the time reversal of the first
up-crossing piece to `b` of the negated increments of `y` after its first hit of `b - a`
(`stopAt_glueC_of_levelSuccess`); it does not depend on `z`.  By the strong Markov property at
the first hit of `b - a` the increments after it are independent of `H` and, negated, have law `M`;
the reversal of the up-crossing piece does not change its law.  Hence

`∫_H ∫ F(stopped glued path) dν dR = R(H) · ∫ F(piece_b) dM`

for every probability law `ν` of continuations started at `0`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Success

variable {a b : ℝ}

/-- Stopping a path at its first hit of `c` (which is finite) gives a path that never hits `-a`
exactly when the original path hits `c` before `-a`. -/
lemma hitFrom_stopAt_eq_top_iff {y : C(ℝ≥0, ℝ)} {c : ℝ} (hτ : hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤) :
    hitFrom (-a) 0 ((stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) = ⊤ ↔
      y ∈ levelSuccess a c := by
  set τ := hitFrom c 0 (y : ℝ≥0 → ℝ) with hτdef
  constructor
  · intro h
    by_contra hnot
    have hnot' : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≤ τ := not_lt.1 hnot
    obtain ⟨T, hTe, -, hyT, -⟩ := exists_hitFrom_eq y.continuous (ne_top_of_le_ne_top hτ hnot')
    have hT_le : (T : ℝ≥0∞) ≤ τ := hTe ▸ hnot'
    have hpT : ((stopAt τ y : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) T = -a := by
      show y (min (T : ℝ≥0∞) τ).toNNReal = -a
      rw [min_eq_left hT_le, ENNReal.toNNReal_coe]
      exact hyT
    have := hitFrom_le (r := 0) zero_le hpT
    rw [h] at this
    exact ENNReal.coe_ne_top (top_le_iff.1 this)
  · intro hlt
    refine top_le_iff.1 (le_iInf₂ fun s hs => ?_)
    exfalso
    have hs2 : y (min (s : ℝ≥0∞) τ).toNNReal = -a := hs.2
    have hle := hitFrom_le (r := 0) zero_le hs2
    have hne : min (s : ℝ≥0∞) τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    have : (((min (s : ℝ≥0∞) τ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ := by
      rw [ENNReal.coe_toNNReal hne]; exact min_le_right _ _
    exact absurd (hle.trans this) (not_le.2 hlt)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The reversal of the first up-crossing piece does not change the integral of a measurable
functional against Brownian motion with positive drift. -/
lemma lintegral_comp_upcrossRev_piece_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    {c : ℝ} (hc : 0 < c) {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w, F (upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) ∂(driftLaw P B hcont mu) =
      ∫⁻ w, F (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  rw [← lintegral_map hF (measurable_upcrossRev_firstUpcrossPiece hc),
    map_upcrossRev_firstUpcrossPiece_driftLaw hB hm hcont hmu hc,
    lintegral_map hF (measurable_firstUpcrossPiece c)]

/-- The indicator of "never hits `-a`" on the path stopped at its first hit of `c` is the indicator
of the level-success event. -/
lemma indicator_hitFrom_top_stopAt {y : C(ℝ≥0, ℝ)} {c : ℝ}
    (hy : hitFrom c 0 (y : ℝ≥0 → ℝ) < ⊤) :
    {p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞))
        (stopAt (hitFrom c 0 (y : ℝ≥0 → ℝ)) y) =
      (levelSuccess a c).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  have hiff := hitFrom_stopAt_eq_top_iff (a := a) (y := y) (c := c) (ne_of_lt hy)
  by_cases h : y ∈ levelSuccess a c
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    exact hiff.2 h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    exact fun h' => h (hiff.1 h')

/-- **Independence of the increments after the first hit of `c` from the level-success event.** -/
lemma lintegral_levelSuccess_shift_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (mu : ℝ) (c : ℝ)
    {Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ y in levelSuccess a c, Ψ (shiftPath (hitFrom c 0 (y : ℝ≥0 → ℝ)).toNNReal y)
        ∂(driftLaw P B hcont mu) =
      driftLaw P B hcont mu (levelSuccess a c) * ∫⁻ v, Ψ v ∂(driftLaw P B hcont mu) := by
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c
  have hHm : MeasurableSet (levelSuccess a c) := measurableSet_levelSuccess a c
  have hHs : MeasurableSet {p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤} :=
    (measurable_hitFrom (r := fun _ => 0) measurable_const (-a)) (measurableSet_singleton ⊤)
  have hΦm : Measurable fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      {p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞)) q.1 *
        Ψ q.2 :=
    ((measurable_const.indicator hHs).comp measurable_fst).mul (hΨ.comp measurable_snd)
  have sm := lintegral_stopAt_shift_driftLaw hB hm hcont mu hτm (isStopFun_hitFrom_zero c) hΦm
  have hsub : levelSuccess a c ⊆ {w | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤} := by
    intro w hw
    show hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤
    exact lt_of_lt_of_le hw le_top
  have hTm : MeasurableSet {w : C(ℝ≥0, ℝ) | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤} :=
    measurableSet_lt hτm measurable_const
  have h1 : ∫⁻ w in {w | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤},
      ({p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞))
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
        Ψ (shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w)) ∂(driftLaw P B hcont mu) =
      ∫⁻ w in levelSuccess a c, Ψ (shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w)
        ∂(driftLaw P B hcont mu) := by
    have e : ∀ w ∈ {w : C(ℝ≥0, ℝ) | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤},
        ({p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞))
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
        Ψ (shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w)) =
          (levelSuccess a c).indicator
            (fun w => Ψ (shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w)) w := by
      intro w hw
      rw [indicator_hitFrom_top_stopAt hw]
      by_cases h : w ∈ levelSuccess a c
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [lintegral_congr_ae ((ae_restrict_iff' hTm).2 (ae_of_all _ e)),
      setLIntegral_indicator hHm, Set.inter_eq_left.2 hsub]
  have h2 : ∫⁻ w in {w | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤}, ∫⁻ v,
      ({p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞))
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) * Ψ v) ∂(driftLaw P B hcont mu)
        ∂(driftLaw P B hcont mu) =
      driftLaw P B hcont mu (levelSuccess a c) * ∫⁻ v, Ψ v ∂(driftLaw P B hcont mu) := by
    have e : ∀ w ∈ {w : C(ℝ≥0, ℝ) | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤}, ∫⁻ v,
        ({p : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (p : ℝ≥0 → ℝ) = ⊤}.indicator (fun _ => (1 : ℝ≥0∞))
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) * Ψ v) ∂(driftLaw P B hcont mu) =
        (levelSuccess a c).indicator (fun _ => ∫⁻ v, Ψ v ∂(driftLaw P B hcont mu)) w := by
      intro w hw
      rw [lintegral_const_mul _ hΨ, indicator_hitFrom_top_stopAt hw]
      by_cases h : w ∈ levelSuccess a c
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [lintegral_congr_ae ((ae_restrict_iff' hTm).2 (ae_of_all _ e)),
      setLIntegral_indicator hHm, Set.inter_eq_left.2 hsub, setLIntegral_const, mul_comm]
  rw [← h1, ← h2]
  exact sm

/-- **The level-success part of the gluing identity.** -/
theorem lintegral_levelSuccess_stop_glue_eq_mul [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) (hab : a < b) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν0 : ∀ᵐ z ∂ν, z 0 = 0) {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in levelSuccess a (b - a), ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ))
        (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν ∂(driftLaw P B hcont (-mu)) =
      driftLaw P B hcont (-mu) (levelSuccess a (b - a)) *
        ∫⁻ w, F (firstUpcrossPiece b (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  have hb : 0 < b := ha.trans hab
  have hΨm : Measurable fun v : C(ℝ≥0, ℝ) =>
      F (upcrossRev b (firstUpcrossPiece b ((-v : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ))) :=
    hF.comp ((measurable_upcrossRev_firstUpcrossPiece hb).comp measurable_neg_pathSpace)
  have step1 : ∫⁻ y in levelSuccess a (b - a), ∫⁻ z, F ((stopAt (hitFrom b 0
        (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν
        ∂(driftLaw P B hcont (-mu)) =
      ∫⁻ y in levelSuccess a (b - a), F (upcrossRev b (firstUpcrossPiece b
        ((-(shiftPath (hitFrom (b - a) 0 (y : ℝ≥0 → ℝ)).toNNReal y) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)))
        ∂(driftLaw P B hcont (-mu)) := by
    refine lintegral_congr_ae ((ae_restrict_iff' (measurableSet_levelSuccess a (b - a))).2 ?_)
    filter_upwards [ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hmu ha.le] with y ⟨hy, hT⟩ hyH
    have : ∀ᵐ z ∂ν, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ))
        (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) = F (upcrossRev b (firstUpcrossPiece b
        ((-(shiftPath (hitFrom (b - a) 0 (y : ℝ≥0 → ℝ)).toNNReal y) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ))) := by
      filter_upwards [hν0] with z hz
      rw [stopAt_glueC_of_levelSuccess ha hab hz hT hyH, ContinuousMap.coe_neg]
    rw [lintegral_congr_ae this, lintegral_const, measure_univ, mul_one]
  have step2 := lintegral_levelSuccess_shift_driftLaw (a := a) hB hm hcont (-mu) (b - a) hΨm
  have hneg : (driftLaw P B hcont (-mu)).map (fun v : C(ℝ≥0, ℝ) => -v) =
      driftLaw P B hcont mu := by
    have := driftLaw_map_neg hB hm hcont (-mu)
    rwa [neg_neg] at this
  have hGm : Measurable fun w : C(ℝ≥0, ℝ) =>
      F (upcrossRev b (firstUpcrossPiece b (w : ℝ≥0 → ℝ))) :=
    hF.comp (measurable_upcrossRev_firstUpcrossPiece hb)
  have hΨint : ∫⁻ v, F (upcrossRev b (firstUpcrossPiece b ((-v : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)))
      ∂(driftLaw P B hcont (-mu)) =
      ∫⁻ w, F (firstUpcrossPiece b (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
    rw [← lintegral_comp_upcrossRev_piece_driftLaw hB hm hcont hmu hb hF, ← hneg,
      lintegral_map hGm measurable_neg_pathSpace]
  rw [step1]
  exact step2.trans (by rw [hΨint])

end Success

end LatticeProb
