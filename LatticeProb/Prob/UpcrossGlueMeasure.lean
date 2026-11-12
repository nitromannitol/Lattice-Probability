import Mathlib
import LatticeProb.Prob.UpcrossGlue
import LatticeProb.Prob.UpcrossLevel
import LatticeProb.Prob.UpcrossDriftLawNeg
import LatticeProb.Prob.StopHitContinuity

/-!
# Measurability of the glued path and the dichotomy at the junction level

* `LatticeProb.measurable_glueC`: the glued path depends measurably on the pair of paths.
* `LatticeProb.levelFailure`: the path hits `-δ` before `c`.
* `LatticeProb.driftLaw_neg_levelSuccess_add_levelFailure`: under Brownian motion with negative
  drift, almost every path either hits `c` before `-δ` or hits `-δ` before `c`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The path hits `-δ` strictly before `c`. -/
def levelFailure (δ c : ℝ) : Set C(ℝ≥0, ℝ) :=
  {w | hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) < hitFrom c 0 (w : ℝ≥0 → ℝ)}

lemma measurableSet_levelFailure (δ c : ℝ) : MeasurableSet (levelFailure δ c) :=
  measurableSet_lt (measurable_hitFrom (r := fun _ => 0) measurable_const (-δ))
    (measurable_hitFrom (r := fun _ => 0) measurable_const c)

lemma disjoint_levelSuccess_levelFailure (δ c : ℝ) :
    Disjoint (levelSuccess δ c) (levelFailure δ c) :=
  Set.disjoint_left.2 fun w h1 h2 =>
    lt_asymm (a := hitFrom c 0 (w : ℝ≥0 → ℝ)) h1 h2

theorem measurable_glueC (a : ℝ) :
    Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueC a p.1 p.2 := by
  rw [ContinuousMap.measurable_iff_eval]
  intro s
  have hT : Measurable fun y : C(ℝ≥0, ℝ) => glueTime a y :=
    (measurable_hitFrom (r := fun _ => 0) measurable_const (-a)).ennreal_toNNReal
  have hT' : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => glueTime a p.1 := hT.comp measurable_fst
  have hev : Measurable fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2 :=
    (continuous_eval : Continuous fun q : C(ℝ≥0, ℝ) × ℝ≥0 => q.1 q.2).measurable
  have h1 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => p.1 (glueTime a p.1 - s) :=
    hev.comp (measurable_fst.prodMk (hT'.sub_const s))
  have h2 : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => p.2 (s - glueTime a p.1) :=
    hev.comp (measurable_snd.prodMk (measurable_const.sub hT'))
  simp only [glueC_apply]
  exact (h1.const_add a).add h2

/-- Under Brownian motion with negative drift, almost every path starts at `0` and hits `-a`
at a finite time (for `a ≥ 0`). -/
theorem ae_hitFrom_neg_ne_top_driftLaw_neg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ y : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont (-mu)),
      y 0 = 0 ∧ hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤ := by
  rw [← driftLaw_map_neg hB hm hcont mu]
  have hp : MeasurableSet {y : C(ℝ≥0, ℝ) | y 0 = 0 ∧ hitFrom (-a) 0 (y : ℝ≥0 → ℝ) ≠ ⊤} :=
    (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
      ((measurable_hitFrom (r := fun _ => 0) measurable_const (-a))
        (measurableSet_singleton ⊤).compl)
  rw [ae_map_iff measurable_neg_pathSpace.aemeasurable hp]
  filter_upwards [ae_start_hitFrom_driftLaw hB hm hcont hmu ha] with w ⟨h0, hf⟩
  refine ⟨by simp [h0], ?_⟩
  rw [ContinuousMap.coe_neg, hitFrom_neg]
  exact hf

/-- Under Brownian motion with negative drift, for `0 < a` and `0 < c`, almost every path hits `c`
before `-a` or `-a` before `c`: the two events have total probability `1`. -/
theorem driftLaw_neg_levelSuccess_add_levelFailure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ}
    (hmu : 0 < mu) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    driftLaw P B hcont (-mu) (levelSuccess a c) + driftLaw P B hcont (-mu) (levelFailure a c) =
      1 := by
  have hprob : IsProbabilityMeasure (driftLaw P B hcont (-mu)) :=
    isProbabilityMeasure_driftLaw hm hcont (-mu)
  rw [← measure_union (disjoint_levelSuccess_levelFailure a c) (measurableSet_levelFailure a c)]
  have hae : ∀ᵐ y : C(ℝ≥0, ℝ) ∂(driftLaw P B hcont (-mu)),
      y ∈ levelSuccess a c ∪ levelFailure a c := by
    filter_upwards [ae_hitFrom_neg_ne_top_driftLaw_neg hB hm hcont hmu ha.le] with y ⟨_, hT⟩
    obtain ⟨s, hs, -, hys, -⟩ := exists_hitFrom_eq y.continuous hT
    rcases lt_trichotomy (hitFrom c 0 (y : ℝ≥0 → ℝ)) (hitFrom (-a) 0 (y : ℝ≥0 → ℝ)) with h | h | h
    · exact Or.inl h
    · exfalso
      have hne : hitFrom c 0 (y : ℝ≥0 → ℝ) ≠ ⊤ := by rw [h]; exact hT
      obtain ⟨s', hs', -, hys', -⟩ := exists_hitFrom_eq y.continuous hne
      have hss : s' = s := ENNReal.coe_injective (by rw [← hs', h, hs])
      rw [hss] at hys'
      linarith
    · exact Or.inr h
  exact (prob_compl_eq_zero_iff ((measurableSet_levelSuccess a c).union
    (measurableSet_levelFailure a c))).1 (ae_iff.1 hae)

end LatticeProb
