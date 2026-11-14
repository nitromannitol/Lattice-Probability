import Mathlib
import LatticeProb.Prob.PathSpaceTightness
import LatticeProb.Prob.PathSpaceDUnif

/-!
# Compact sets of path laws from a modulus bound at a countable family of levels

Let `E` be a proper metric space and `x₀ ∈ E`.  Fix scales `δ k > 0`, `k ∈ ℕ`.  The set of probability
measures `μ` on `C(ℝ≥0, E)` that are carried by paths starting within distance `1` of `x₀` and that
satisfy, for every `k`, the modulus bound
`μ (pathModulusFailure (k + 1) (δ k)) ≤ 1 / (k + 1)`
is tight, hence relatively compact for the Lévy–Prokhorov metric (Prokhorov's theorem).  The
modulus event is increasing in the level `L`, so the bounds at the levels `k + 1` give the bound at
every level `L > 0` (at scale `δ ⌈L⌉`).
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

attribute [local instance] dUnifMetricSpace

variable {E : Type*}

/-- The modulus event is increasing in the level `L`. -/
theorem pathModulusFailure_mono_level [MetricSpace E] {L L' : ℝ} (hL : 0 < L) (hLL' : L ≤ L')
    (δ : ℝ≥0) : pathModulusFailure (E := E) L δ ⊆ pathModulusFailure L' δ := by
  rintro f ⟨s, t, hs, ht, hst, hlt⟩
  exact ⟨s, t, hs.trans hLL', ht.trans hLL', hst,
    lt_of_le_of_lt (one_div_le_one_div_of_le hL hLL') hlt⟩

/-- **Compact sets of path laws.**  For a proper metric space `E`, `x₀ : E` and positive scales
`δ k`, there is a compact set `K` of probability measures on the path space (Lévy–Prokhorov metric)
containing every probability measure `μ` that charges only paths starting within `1` of `x₀` and has
`μ (pathModulusFailure (k + 1) (δ k)) ≤ 1 / (k + 1)` for all `k`. -/
theorem exists_isCompact_pathLaws [MetricSpace E] [ProperSpace E] [MeasurableSpace C(ℝ≥0, E)]
    [BorelSpace C(ℝ≥0, E)] (x₀ : E) (δ : ℕ → ℝ≥0) (hδ : ∀ k, 0 < δ k) :
    ∃ K : Set (LevyProkhorov (ProbabilityMeasure C(ℝ≥0, E))), IsCompact K ∧
      ∀ μ : ProbabilityMeasure C(ℝ≥0, E),
        (μ : Measure C(ℝ≥0, E)) {f : C(ℝ≥0, E) | 1 < dist (f 0) x₀} = 0 →
        (∀ k : ℕ, (μ : Measure C(ℝ≥0, E)) (pathModulusFailure ((k : ℝ) + 1) (δ k)) ≤
          ENNReal.ofReal (1 / ((k : ℝ) + 1))) →
        LevyProkhorov.probabilityMeasureHomeomorph μ ∈ K := by
  set S : Set (ProbabilityMeasure C(ℝ≥0, E)) := {μ |
    (μ : Measure C(ℝ≥0, E)) {f : C(ℝ≥0, E) | 1 < dist (f 0) x₀} = 0 ∧
    ∀ k : ℕ, (μ : Measure C(ℝ≥0, E)) (pathModulusFailure ((k : ℝ) + 1) (δ k)) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1))} with hS
  have hSt : IsTightMeasureSet {((ν : ProbabilityMeasure C(ℝ≥0, E)) : Measure C(ℝ≥0, E)) | ν ∈ S} := by
    refine isTightMeasureSet_of_pathModuli _ x₀ ?_ ?_
    · intro ζ _
      refine ⟨1, ?_⟩
      rintro _ ⟨ν, hν, rfl⟩
      rw [hν.1]
      exact zero_le
    · intro L hL
      refine ⟨δ ⌈L⌉₊, hδ _, ?_⟩
      rintro _ ⟨ν, hν, rfl⟩
      have hk : L ≤ ((⌈L⌉₊ : ℝ) + 1) := (Nat.le_ceil L).trans (le_add_of_nonneg_right zero_le_one)
      refine (measure_mono (pathModulusFailure_mono_level hL hk (δ ⌈L⌉₊))).trans
        ((hν.2 ⌈L⌉₊).trans ?_)
      exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hL hk)
  have hcl : IsCompact (closure S) := isCompact_closure_of_isTightMeasureSet (E := C(ℝ≥0, E)) (S := S) hSt
  refine ⟨LevyProkhorov.probabilityMeasureHomeomorph '' closure S,
    hcl.image LevyProkhorov.probabilityMeasureHomeomorph.continuous, fun μ h0 hk => ?_⟩
  exact ⟨μ, subset_closure ⟨h0, hk⟩, rfl⟩

end LatticeProb
