import LatticeProb.Topology.ContinuousMapBorel

/-!
# Sample paths as continuous maps

For a process `B : ℝ≥0 → Ω → E` whose sample paths are continuous, `pathMap B hcont ω` is the
path `t ↦ B t ω` regarded as an element of `C(ℝ≥0, E)`. When every `B t` is measurable, the
map `ω ↦ pathMap B hcont ω` is measurable for the Borel sigma-algebra of the compact-open
topology on `C(ℝ≥0, E)`.
-/

open scoped NNReal

namespace LatticeProb

/-- The sample path `t ↦ B t ω` of the process `B` at `ω`, as a continuous map `ℝ≥0 → E`. -/
noncomputable def pathMap {Ω E : Type*} [TopologicalSpace E] (B : ℝ≥0 → Ω → E)
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) (ω : Ω) : C(ℝ≥0, E) :=
  ⟨fun t ↦ B t ω, hcont ω⟩

/-- The value of `pathMap B hcont ω` at `t` is `B t ω`. -/
@[simp]
lemma pathMap_apply {Ω E : Type*} [TopologicalSpace E] (B : ℝ≥0 → Ω → E)
    (hcont : ∀ ω, Continuous fun t ↦ B t ω) (ω : Ω) (t : ℝ≥0) :
    pathMap B hcont ω t = B t ω :=
  rfl

/-- If every `B t` is measurable and the sample paths are continuous, then the map
`ω ↦ pathMap B hcont ω` into `C(ℝ≥0, E)` is measurable for the Borel sigma-algebra. -/
theorem measurable_pathMap {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [RegularSpace E]
    (B : ℝ≥0 → Ω → E) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t ↦ B t ω) :
    Measurable (pathMap B hcont) := by
  rw [ContinuousMapBorel.ContinuousMap.measurable_iff_eval]
  intro t
  exact hm t

-- Nonvacuity examples for `measurable_pathMap`.
namespace BrownianPathMapExample

/-- The process `B t ω = t * ω` on `ℝ`, whose sample paths are continuous in `t`. -/
noncomputable def B : ℝ≥0 → ℝ → ℝ := fun t ω ↦ (t : ℝ) * ω

/-- Each `B t` is measurable. -/
lemma measurable_B (t : ℝ≥0) : Measurable (B t) := by
  unfold B
  fun_prop

/-- The sample paths of `B` are continuous in `t`. -/
lemma continuous_B (ω : ℝ) : Continuous fun t ↦ B t ω := by
  unfold B
  fun_prop

/-- The sample path map of the process `B` is measurable. -/
theorem measurable_pathMap_B : Measurable (pathMap B continuous_B) :=
  measurable_pathMap B measurable_B continuous_B

/-- A constant map into `C(ℝ≥0, ℝ)` is measurable, by `measurable_iff_eval`. -/
theorem measurable_const_contMap {Z : Type*} [MeasurableSpace Z] (f : C(ℝ≥0, ℝ)) :
    Measurable fun _ : Z ↦ f :=
  ContinuousMapBorel.ContinuousMap.measurable_iff_eval.2 fun _ ↦ measurable_const

end BrownianPathMapExample

end LatticeProb
