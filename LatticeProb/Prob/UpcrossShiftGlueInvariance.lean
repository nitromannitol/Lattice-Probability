import Mathlib
import LatticeProb.Prob.UpcrossGlueCocycle

/-!
# Invariance of the pair (path after the first hit, glued path)

Let `R` be the law of Brownian motion with drift `-mu` (`mu > 0`), `a > 0`, and `ν` a probability law
of paths as in `LatticeProb.map_glueC_prod_eq`.  Write `τ(y)` for the first hit of `-a` by `y`.  The
pair
`(y, z) ↦ (the increments of y after τ, the reversal of y up to τ glued to z)`
maps the product law `R ⊗ ν` to itself: the increments after the hitting time are independent of the
path before it (strong Markov property) and have law `R`, while the glued path has law `ν`
(`LatticeProb.map_glueC_prod_eq`).

* `LatticeProb.glueC_stopAt_hit`: the glued path depends on `y` only through `y` stopped at its first
  hit of `-a`.
* `LatticeProb.map_shiftGlue_prod_eq`: the invariance.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

section ShiftGlue

variable {a : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The glued path only depends on `y` up to its first hit of `-a`. -/
lemma glueC_stopAt_hit {y z : C(ℝ≥0, ℝ)} (hT : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤) :
    glueC a (stopAt (hitFrom (-a) 0 (y : ℝ≥0 → ℝ)) y) z = glueC a y z := by
  have hTT : glueTime a ((stopAt (hitFrom (-a) 0 (y : ℝ≥0 → ℝ)) y : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      glueTime a (y : ℝ≥0 → ℝ) := by
    unfold glueTime
    rw [hitFrom_stopAt_hit hT]
  ext s
  rw [glueC_apply, glueC_apply, hTT]
  congr 2
  have hcoe : hitFrom (-a) 0 (y : ℝ≥0 → ℝ) = ((glueTime a (y : ℝ≥0 → ℝ) : ℝ≥0) : ℝ≥0∞) := by
    unfold glueTime
    exact (ENNReal.coe_toNNReal hT).symm
  rw [hcoe]
  exact stopAt_coe_of_le y (tsub_le_self)

/-- The measurable path-valued map `y ↦` increments of `y` after its first hit of `-a`. -/
lemma measurable_shiftGlue (a : ℝ) :
    Measurable fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      (shiftPath (glueTime a (q.1 : ℝ≥0 → ℝ)) q.1, glueC a q.1 q.2) := by
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom (-a) 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const (-a)
  exact ((measurable_shiftPath_path hτm).comp measurable_fst).prodMk (measurable_glueC a)

/-- **The pair (increments after the first hit of `-a`, glued path) preserves `R ⊗ ν`.** -/
theorem map_shiftGlue_prod_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν] (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (driftLaw P B hcont mu).map (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    ((driftLaw P B hcont (-mu)).prod ν).map
        (fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
          (shiftPath (glueTime a (q.1 : ℝ≥0 → ℝ)) q.1, glueC a q.1 q.2)) =
      (driftLaw P B hcont (-mu)).prod ν := by
  set Lw := driftLaw P B hcont (-mu) with hR
  have hRprob : IsProbabilityMeasure Lw := isProbabilityMeasure_driftLaw hm hcont (-mu)
  have hglue := map_glueC_prod_eq hB hm hcont hmu ha hν0 hpiece
  have hΘ := measurable_shiftGlue a
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom (-a) 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const (-a)
  have hae := ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hmu ha.le
  symm
  refine Measure.prod_eq fun A B' hA hB' => ?_
  rw [Measure.map_apply hΘ (hA.prod hB'), Measure.prod_apply (hΘ (hA.prod hB'))]
  have hsh : Measurable fun y : C(ℝ≥0, ℝ) => shiftPath (glueTime a (y : ℝ≥0 → ℝ)) y :=
    measurable_shiftPath_path hτm
  have hgl : MeasurableSet {q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | glueC a q.1 q.2 ∈ B'} :=
    measurable_glueC a hB'
  set ψ : C(ℝ≥0, ℝ) → ℝ≥0∞ := fun u => ν {z | glueC a u z ∈ B'} with hψdef
  have hψ : Measurable ψ := measurable_measure_prodMk_left hgl
  have key : ∀ y : C(ℝ≥0, ℝ), ν (Prod.mk y ⁻¹'
      ((fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        (shiftPath (glueTime a (q.1 : ℝ≥0 → ℝ)) q.1, glueC a q.1 q.2)) ⁻¹' (A ×ˢ B'))) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) (shiftPath (glueTime a (y : ℝ≥0 → ℝ)) y) * ψ y := by
    intro y
    by_cases hy : shiftPath (glueTime a (y : ℝ≥0 → ℝ)) y ∈ A
    · simp [hy, ψ, Set.preimage]
    · have : Prod.mk y ⁻¹' ((fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
          (shiftPath (glueTime a (q.1 : ℝ≥0 → ℝ)) q.1, glueC a q.1 q.2)) ⁻¹' (A ×ˢ B')) = ∅ := by
        ext z; simp [hy]
      simp [hy, this]
  simp_rw [key]
  -- strong Markov at the first hit of `-a`
  have hΦm : Measurable fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      ψ q.1 * A.indicator (fun _ => (1 : ℝ≥0∞)) q.2 :=
    (hψ.comp measurable_fst).mul ((measurable_const.indicator hA).comp measurable_snd)
  have sm := lintegral_stopAt_shift_driftLaw hB hm hcont (-mu) hτm (isStopFun_hitFrom_zero (-a)) hΦm
  have hmem : ∀ᵐ w ∂Lw, w ∈ {w : C(ℝ≥0, ℝ) | hitFrom (-a) 0 (w : ℝ≥0 → ℝ) < ⊤} := by
    filter_upwards [hae] with w hw
    exact lt_top_iff_ne_top.2 hw.2
  rw [Measure.restrict_eq_self_of_ae_mem hmem] at sm
  have hLHS : ∫⁻ w : C(ℝ≥0, ℝ), ψ (stopAt (hitFrom (-a) 0 (w : ℝ≥0 → ℝ)) w) *
      A.indicator (fun _ => (1 : ℝ≥0∞)) (shiftPath (hitFrom (-a) 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂Lw =
      ∫⁻ y : C(ℝ≥0, ℝ), A.indicator (fun _ => (1 : ℝ≥0∞)) (shiftPath (glueTime a (y : ℝ≥0 → ℝ)) y) * ψ y ∂Lw := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with w hw
    simp only [hψdef, glueC_stopAt_hit hw.2, glueTime]
    rw [mul_comm]
  have hRHS : ∫⁻ w : C(ℝ≥0, ℝ), (∫⁻ v, ψ (stopAt (hitFrom (-a) 0 (w : ℝ≥0 → ℝ)) w) *
      A.indicator (fun _ => (1 : ℝ≥0∞)) v ∂Lw) ∂Lw = (∫⁻ w : C(ℝ≥0, ℝ), ψ w ∂Lw) * Lw A := by
    have h1 : ∀ᵐ w : C(ℝ≥0, ℝ) ∂Lw, ∫⁻ v, ψ (stopAt (hitFrom (-a) 0 (w : ℝ≥0 → ℝ)) w) *
        A.indicator (fun _ => (1 : ℝ≥0∞)) v ∂Lw = ψ w * Lw A := by
      filter_upwards [hae] with w hw
      simp only [hψdef, glueC_stopAt_hit hw.2]
      rw [lintegral_const_mul _ (measurable_const.indicator hA), lintegral_indicator_const hA, one_mul]
    rw [lintegral_congr_ae h1, lintegral_mul_const _ hψ]
  have hpsi : ∫⁻ w : C(ℝ≥0, ℝ), ψ w ∂Lw = ν B' := by
    have : ∫⁻ w : C(ℝ≥0, ℝ), ψ w ∂Lw = ((Lw.prod ν).map (fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC a q.1 q.2)) B' := by
      rw [Measure.map_apply (measurable_glueC a) hB', Measure.prod_apply (measurable_glueC a hB')]
      rfl
    rw [this, hglue]
  rw [hLHS, hRHS, hpsi] at sm
  rw [sm, mul_comm]

end ShiftGlue

end LatticeProb
