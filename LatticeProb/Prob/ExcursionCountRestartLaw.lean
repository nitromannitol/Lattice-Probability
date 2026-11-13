import LatticeProb.Analysis.ExcursionCountMeasurable
import LatticeProb.Prob.BrownianDriftRestartHit

/-!
# The excursion count of a Brownian motion restarted at a stopping time

For a path `f : ℝ≥0 → ℝ`, `pathExcursionCount f b ε` is the number of excursions of `f` above its running minimum
from time `0`, of length larger than `ε`, completed before the first passage of `f` below the level `f 0 - b`: the
excursion count of the forward ladder set from `0` of the extension `nnExtend f` of `f` to `ℝ` (constant on
`(-∞, 0]`), on the interval from `0` to the first-passage time.

* `exists_measurableSet_le_pathExcursionCount`: a measurable set of paths `Γ` with `f ∈ Γ ↔ k ≤ pathExcursionCount f b ε`
  for every continuous path `f`;
* `measurableSet_le_pathExcursionCount`, `measurable_pathExcursionCount`: for a process with measurable coordinates and
  continuous paths the excursion count is a random variable;
* `restart_le_pathExcursionCount`: for a real Brownian motion with continuous paths and a finite stopping time `τ` of
  its natural filtration, the excursion count of the restarted motion `B (τ + ·) - B τ` is independent of the
  σ-algebra at `τ` and has the law of the excursion count of `B`; `restart_pathExcursionCount_law` is the case of the
  whole space.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- The extension of a path `f : ℝ≥0 → ℝ` to `ℝ`, constant on `(-∞, 0]`. -/
def nnExtend (f : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  f t.toNNReal

theorem continuous_nnExtend {f : ℝ≥0 → ℝ} (hf : Continuous f) : Continuous (nnExtend f) :=
  hf.comp continuous_real_toNNReal

/-- The excursion count of a path `f : ℝ≥0 → ℝ`: the number of excursions of `f` above its running minimum from
time `0`, of length larger than `ε`, completed before the first passage below `f 0 - b`. -/
noncomputable def pathExcursionCount (f : ℝ≥0 → ℝ) (b ε : ℝ) : ℕ :=
  excursionCount (forwardLadderSet (nnExtend f) 0) 0 (firstPassageBelow (nnExtend f) 0 b) ε

/-- **The excursion count as a measurable condition on paths.** For `ε > 0` there is a measurable set `Γ` of paths
`ℝ≥0 → ℝ` such that a continuous path `f` lies in `Γ` iff `k ≤ pathExcursionCount f b ε`. -/
theorem exists_measurableSet_le_pathExcursionCount (b : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∃ Γ : Set (ℝ≥0 → ℝ), MeasurableSet Γ ∧
      ∀ f : ℝ≥0 → ℝ, Continuous f → (f ∈ Γ ↔ k ≤ pathExcursionCount f b ε) := by
  obtain ⟨Γ, hΓ, hΓP⟩ := exists_measurableSet_le_excursionCount (fun f : ℝ≥0 → ℝ => nnExtend f)
    (fun q => measurable_pi_apply ((q : ℝ).toNNReal)) 0 b ε hε k
  refine ⟨Γ, hΓ, fun f hf => ?_⟩
  have h := hΓP f (continuous_nnExtend hf)
  rw [Rat.cast_zero] at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For a process with measurable coordinates and continuous paths, `{k ≤ pathExcursionCount (B · ω) b ε}` is
measurable. -/
theorem measurableSet_le_pathExcursionCount (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (b : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    MeasurableSet {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  obtain ⟨Γ, hΓ, hΓP⟩ := exists_measurableSet_le_pathExcursionCount b hε k
  have hmeas : Measurable fun ω => fun t => B t ω := Measurable.of_eval hm
  convert hmeas hΓ using 1
  ext ω
  exact (hΓP _ (hcont ω)).symm

/-- For a process with measurable coordinates and continuous paths, the excursion count is a random variable. -/
theorem measurable_pathExcursionCount (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Measurable fun ω => pathExcursionCount (fun t => B t ω) b ε := by
  refine measurable_to_countable' fun k => ?_
  have : (fun ω => pathExcursionCount (fun t => B t ω) b ε) ⁻¹' {k} =
      {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} \ {ω | k + 1 ≤ pathExcursionCount (fun t => B t ω) b ε} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_sdiff, mem_ofPred_eq]
    omega
  rw [this]
  exact (measurableSet_le_pathExcursionCount hm hcont b hε k).diff
    (measurableSet_le_pathExcursionCount hm hcont b hε (k + 1))

/-- **The restarted excursion count.** For a real Brownian motion `B` with continuous paths, a finite stopping time
`τ` of the natural filtration and an event `E` of the σ-algebra at `τ`, the excursion count of the restarted motion
`B (τ + ·) - B τ` is independent of `E` and has the law of the excursion count of `B`. -/
theorem restart_le_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E) (b : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    P (E ∩ {ω | k ≤ pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε})
      = P E * P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  obtain ⟨Γ, hΓ, hΓP⟩ := exists_measurableSet_le_pathExcursionCount b hε k
  have h1 : {ω | k ≤ pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε} =
      {ω | (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ Γ} := by
    ext ω
    have hc : Continuous fun t => B (τ ω + t) ω - B (τ ω) ω :=
      ((hcont ω).comp (continuous_const.add continuous_id)).sub continuous_const
    exact (hΓP _ hc).symm
  have h2 : {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} = {ω | (fun t => B t ω) ∈ Γ} := by
    ext ω
    exact (hΓP _ (hcont ω)).symm
  rw [h1, h2]
  exact restart_real hB hm hcont τ hτ E hE Γ hΓ

/-- **The law of the restarted excursion count.** For a real Brownian motion with continuous paths and a finite
stopping time `τ` of the natural filtration, the excursion count of `B (τ + ·) - B τ` has the law of the excursion
count of `B`. -/
theorem restart_pathExcursionCount_law [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞))
    (b : ℝ) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    P {ω | k ≤ pathExcursionCount (fun t => B (τ ω + t) ω - B (τ ω) ω) b ε}
      = P {ω | k ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  have h := restart_le_pathExcursionCount hB hm hcont τ hτ univ MeasurableSet.univ b hε k
  rwa [univ_inter, measure_univ, one_mul] at h

end LatticeProb.LadderSet
