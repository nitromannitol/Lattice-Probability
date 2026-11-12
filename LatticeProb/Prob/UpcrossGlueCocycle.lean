import Mathlib
import LatticeProb.Prob.UpcrossGlueLaw
import LatticeProb.Prob.UpcrossGlueLawSuccess
import LatticeProb.Prob.ContinuousPathStopLevels

/-!
# The law of the glued path

Let `M`, `R` be the laws of Brownian motion with drift `mu > 0` and `-mu`, `a > 0`, and `ν` a
probability law on paths started at `0` such that, for Lebesgue-almost every level `c > 0`, the
first up-crossing piece to `c` under `M` has the law of a path stopped at its first hit of `c`
under `ν`.  The path `glueC a y z` is the reversal of `y` from its first hit of `-a` (read at level
`a`) followed by `z`.

* `LatticeProb.lintegral_stop_glue_eq`: for `b > a` such that the piece law holds at `b - a`, the
  integral of a measurable `F ≤ 1` of the glued path stopped at its first hit of `b`, against
  `R ⊗ ν`, equals the integral of `F` of the first up-crossing piece to `b` under `M`.  The proof
  splits `y` over the events that `y` hits `-a` before `b - a` or after, and uses the renewal
  identity and the strong Markov property.
* `LatticeProb.map_stop_glue_eq`: the same as an equality of laws on `ℝ≥0 → ℝ`.
* `LatticeProb.map_glueC_prod_eq`: if the piece law holds almost everywhere, then the law of the
  glued path under `R ⊗ ν` is `ν` itself.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

lemma coe_stopHit (b : ℝ) (w : C(ℝ≥0, ℝ)) :
    ((stopHit b w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) =
      ((stopAt (hitFrom b 0 (w : ℝ≥0 → ℝ)) w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) := by
  funext s
  rw [stopHit_apply, stopAt_apply]
  unfold stopHitTime
  split_ifs with h
  · rw [min_eq_left h, ENNReal.toNNReal_coe]
  · rw [min_eq_right (not_le.1 h).le]

lemma measurable_coeFn_path : Measurable fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ) :=
  measurable_pi_iff.2 fun s => (continuous_eval_const s).measurable

/-- Two laws on continuous paths with the same image under `w ↦ (w : ℝ≥0 → ℝ)` are equal. -/
lemma eq_of_map_coeFn_eq {μ ν : Measure C(ℝ≥0, ℝ)}
    (h : μ.map (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) = ν.map (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ))) :
    μ = ν := by
  have hmeq : (continuousMapMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.comap (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) MeasurableSpace.pi := by
    rw [ContinuousMapBorel.ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  refine Measure.ext fun s hs => ?_
  have hs' : MeasurableSet[MeasurableSpace.comap (fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ))
      MeasurableSpace.pi] s := by
    rw [← hmeq]; exact hs
  obtain ⟨T, hT, rfl⟩ := hs'
  have := congrArg (fun m => m T) h
  simpa only [Measure.map_apply measurable_coeFn_path hT] using this

section Cocycle

variable {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma measurable_stopGlue (a b : ℝ) :
    Measurable fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      ((stopAt (hitFrom b 0 (glueC a q.1 q.2 : ℝ≥0 → ℝ)) (glueC a q.1 q.2) :
        C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) :=
  (measurable_stopHitFun b).comp (measurable_glueC a)

/-- **Williams gluing at a fixed level.** -/
theorem lintegral_stop_glue_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) (hab : a < b) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : (driftLaw P B hcont mu).map
        (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) (hF1 : ∀ p, F p ≤ 1) :
    ∫⁻ y, ∫⁻ z, F ((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ)) (glueC a y z) :
        C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) ∂ν ∂(driftLaw P B hcont (-mu)) =
      ∫⁻ w, F (firstUpcrossPiece b (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  have hc' : 0 < b - a := sub_pos.2 hab
  have hHm := measurableSet_levelSuccess a (b - a)
  have hH'm := measurableSet_levelFailure a (b - a)
  have hdisj := disjoint_levelSuccess_levelFailure a (b - a)
  have hsum := driftLaw_neg_levelSuccess_add_levelFailure hB hm hcont hmu ha hc'
  have hRprob : IsProbabilityMeasure (driftLaw P B hcont (-mu)) :=
    isProbabilityMeasure_driftLaw hm hcont (-mu)
  have hae : ∀ᵐ y ∂(driftLaw P B hcont (-mu)),
      y ∈ levelSuccess a (b - a) ∪ levelFailure a (b - a) := by
    have h1 : driftLaw P B hcont (-mu) (levelSuccess a (b - a) ∪ levelFailure a (b - a)) = 1 := by
      rw [measure_union hdisj hH'm, hsum]
    exact ae_iff.2 ((prob_compl_eq_zero_iff (hHm.union hH'm)).2 h1)
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_union hH'm hdisj,
    lintegral_levelSuccess_stop_glue_eq_mul hB hm hcont hmu ha hab hν0 hF,
    lintegral_levelFailure_stop_glue_eq_mul hB hm hcont hmu ha hab hν0 hpiece hF hF1,
    ← add_mul, hsum, one_mul]

/-- **Williams gluing at a fixed level, as an equality of laws.** -/
theorem map_stop_glue_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) (hab : a < b) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν]
    (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : (driftLaw P B hcont mu).map
        (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece (b - a) (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom (b - a) 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)))
    (hpieceb : (driftLaw P B hcont mu).map
        (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece b (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom b 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    (((driftLaw P B hcont (-mu)).prod ν).map fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        ((stopAt (hitFrom b 0 (glueC a q.1 q.2 : ℝ≥0 → ℝ)) (glueC a q.1 q.2) :
          C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom b 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ)) := by
  have hRprob : IsProbabilityMeasure (driftLaw P B hcont (-mu)) :=
    isProbabilityMeasure_driftLaw hm hcont (-mu)
  refine Measure.ext fun s hs => ?_
  have hF : Measurable (s.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞)) := measurable_one.indicator hs
  have hF1 : ∀ p, s.indicator (1 : (ℝ≥0 → ℝ) → ℝ≥0∞) p ≤ 1 := fun p => by
    by_cases h : p ∈ s <;> simp [h]
  have hmeas := measurable_stopGlue a b
  calc (((driftLaw P B hcont (-mu)).prod ν).map _) s
      = ∫⁻ p, s.indicator 1 p ∂(((driftLaw P B hcont (-mu)).prod ν).map _) :=
        (lintegral_indicator_one hs).symm
    _ = ∫⁻ q, s.indicator 1 (((stopAt (hitFrom b 0 (glueC a q.1 q.2 : ℝ≥0 → ℝ))
          (glueC a q.1 q.2) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)) ∂((driftLaw P B hcont (-mu)).prod ν) :=
        lintegral_map hF hmeas
    _ = ∫⁻ y, ∫⁻ z, s.indicator 1 (((stopAt (hitFrom b 0 (glueC a y z : ℝ≥0 → ℝ))
          (glueC a y z) : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)) ∂ν ∂(driftLaw P B hcont (-mu)) :=
        lintegral_prod _ (hF.comp hmeas).aemeasurable
    _ = ∫⁻ w, s.indicator 1 (firstUpcrossPiece b (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) :=
        lintegral_stop_glue_eq hB hm hcont hmu ha hab hν0 hpiece hF hF1
    _ = ∫⁻ p, s.indicator 1 p ∂((driftLaw P B hcont mu).map
          (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece b (w : ℝ≥0 → ℝ))) :=
        (lintegral_map hF (measurable_firstUpcrossPiece b)).symm
    _ = ∫⁻ p, s.indicator 1 p ∂(ν.map
          (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom b 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) := by
        rw [hpieceb]
    _ = (ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom b 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) s :=
        lintegral_indicator_one hs

/-- A conull set of levels contains, beyond every bound, a level `c` with `c - a` also in it. -/
lemma exists_levels_pair {p : ℝ → Prop} (hp : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))), p c)
    (ha : 0 < a) (n : ℕ) : ∃ c : ℝ, (n : ℝ) + a < c ∧ p c ∧ p (c - a) := by
  have h1 : ∀ᵐ c ∂(volume : Measure ℝ), c ∈ Ioi (0 : ℝ) → p c :=
    (ae_restrict_iff' measurableSet_Ioi).1 hp
  have h2 : ∀ᵐ c ∂(volume : Measure ℝ), c - a ∈ Ioi (0 : ℝ) → p (c - a) :=
    (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae h1
  by_contra hno
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnull : volume (Ioi ((n : ℝ) + a)) = 0 := by
    refine measure_mono_null (fun c hc => ?_) (ae_iff.1 (h1.and h2))
    intro hgood
    exact hno ⟨c, hc, hgood.1 (by simp only [mem_Ioi] at hc ⊢; linarith),
      hgood.2 (by simp only [mem_Ioi] at hc ⊢; linarith)⟩
  rw [Real.volume_Ioi] at hnull
  exact ENNReal.top_ne_zero hnull

/-- **The glued path has the law `ν`.**  If the first up-crossing piece to the level `c` under
Brownian motion with drift `mu > 0` has the law of a `ν`-path stopped at its first hit of `c` for
almost every `c > 0`, and `ν`-almost every path starts at `0`, then gluing the reversal of
Brownian motion with drift `-mu` (from its first hit of `-a`, read at level `a`) with a `ν`-path
gives a `ν`-path. -/
theorem map_glueC_prod_eq [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    (ha : 0 < a) {ν : Measure C(ℝ≥0, ℝ)} [IsProbabilityMeasure ν] (hν0 : ∀ᵐ z ∂ν, z 0 = 0)
    (hpiece : ∀ᵐ c ∂(volume.restrict (Ioi (0 : ℝ))),
      (driftLaw P B hcont mu).map (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
        ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) :
    ((driftLaw P B hcont (-mu)).prod ν).map (fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC a q.1 q.2) =
      ν := by
  have hRprob : IsProbabilityMeasure (driftLaw P B hcont (-mu)) :=
    isProbabilityMeasure_driftLaw hm hcont (-mu)
  have hgm := measurable_glueC a
  have : IsProbabilityMeasure (((driftLaw P B hcont (-mu)).prod ν).map
      (fun q : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC a q.1 q.2)) := isProb_map hgm.aemeasurable
  choose b hb using exists_levels_pair (a := a) (p := fun c =>
    (driftLaw P B hcont mu).map (fun w : C(ℝ≥0, ℝ) => firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
      ν.map (fun z : C(ℝ≥0, ℝ) => (stopAt (hitFrom c 0 (z : ℝ≥0 → ℝ)) z : ℝ≥0 → ℝ))) hpiece ha
  refine map_eq_of_map_stopHit_eq _ _ b
    (tendsto_atTop_mono (fun n => by linarith [(hb n).1]) tendsto_natCast_atTop_atTop) fun n => ?_
  have key := map_stop_glue_eq hB hm hcont hmu ha (by linarith [(hb n).1, Nat.cast_nonneg (α := ℝ) n]
    : a < b n) hν0 (hb n).2.2 (hb n).2.1
  have e2 : (fun w : C(ℝ≥0, ℝ) => ((stopHit (b n) w : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ)) =
      fun z : C(ℝ≥0, ℝ) => ((stopAt (hitFrom (b n) 0 (z : ℝ≥0 → ℝ)) z : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) :=
    funext (coe_stopHit (b n))
  refine eq_of_map_coeFn_eq ?_
  rw [Measure.map_map measurable_coeFn_path (measurable_stopHit (b n)),
    Measure.map_map (measurable_coeFn_path.comp (measurable_stopHit (b n))) hgm,
    Measure.map_map measurable_coeFn_path (measurable_stopHit (b n))]
  have e3 : ((fun w : C(ℝ≥0, ℝ) => (w : ℝ≥0 → ℝ)) ∘ stopHit (b n)) =
      fun z : C(ℝ≥0, ℝ) => ((stopAt (hitFrom (b n) 0 (z : ℝ≥0 → ℝ)) z : C(ℝ≥0, ℝ)) : ℝ≥0 → ℝ) :=
    e2
  rw [e3]
  exact key

end Cocycle

end LatticeProb
