/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TransitionRightContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.StrongMarkov

/-! Right continuity of actual reflected-walk vertex transition probabilities.
Reuse the existing pathwise constancy of each vertex predicate and finite-measure
dominated convergence for indicators. -/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16

universe u
variable {V Ω : Type u} [MeasurableSpace Ω]

/-- Vertex-event probabilities inherit right continuity from the reflected path
conditions at vertices and at infinity. -/
theorem continuousWithinAt_vertexProbability {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (hii : Theorem16.RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (t : ℝ≥0) (y : V) :
    ContinuousWithinAt (fun s : ℝ≥0 => P {ω | X s ω = some y}) (Ici t) t := by
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝[≥] t)
    (hX t (measurableSet_option {some y}))
    (fun s => hX s (measurableSet_option {some y}))
  filter_upwards [hii, hR] with ω hωi hωR
  obtain ⟨ε, hε, hconst⟩ := exists_Ico_iff_of_rightContinuous hωi hωR t y
  exact mem_nhdsGE_iff_exists_Ico_subset.mpr
    ⟨t + ε, lt_add_of_pos_right t hε, hconst⟩

/-- The real-valued version needed for scalar occupation resolvents. -/
theorem continuousWithinAt_vertexProbability_toReal {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (hii : Theorem16.RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (t : ℝ≥0) (y : V) :
    ContinuousWithinAt (fun s : ℝ≥0 => (P {ω | X s ω = some y}).toReal) (Ici t) t := by
  have hto : ContinuousAt ENNReal.toReal (P {ω | X t ω = some y}) :=
    ENNReal.continuousAt_toReal (measure_ne_top P _)
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun s : ℝ≥0 => P {ω | X s ω = some y}) hto
    (continuousWithinAt_vertexProbability hX hii hR t y)

/-- Compose with the standard nonnegative-time conversion used by the analytic
semigroup's real-time Laplace integral. -/
theorem continuousWithinAt_vertexProbability_realTime {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → Option V} (hX : ∀ t, Measurable (X t))
    (hii : Theorem16.RightContinuous P X)
    (hR : RightContinuousAtInfty P X) (t : ℝ) (y : V) :
    ContinuousWithinAt
      (fun s : ℝ => (P {ω | X (Real.toNNReal s) ω = some y}).toReal) (Ici t) t := by
  apply (continuousWithinAt_vertexProbability_toReal hX hii hR (Real.toNNReal t) y).comp
    continuous_real_toNNReal.continuousWithinAt
  exact fun s hs => Real.toNNReal_mono hs

/-- A one-sided continuous time function is Borel measurable. This reuses the
library criterion for sets that are right neighborhoods of their points. -/
theorem measurable_of_rightContinuous {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] {f : ℝ → E}
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) : Measurable f := by
  apply measurable_of_isOpen
  intro U hU
  apply MeasurableSet.of_mem_nhdsGT
  intro t ht
  exact ((hf t).mono Ioi_subset_Ici_self) (hU.mem_nhds ht)

/-- Actual transition probabilities of a family satisfying the existing
reflected-walk contract are right continuous. -/
theorem reflected_vertexProbability_rightContinuous
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {𝓧 : ProcessFamily V} (h : IsReflectedWalk G w hmin 𝓧)
    (x y : V) (t : ℝ) :
    ContinuousWithinAt
      (fun s : ℝ => (𝓧.P x {ω | 𝓧.X (Real.toNNReal s) ω = some y}).toReal) (Ici t) t :=
  continuousWithinAt_vertexProbability_realTime 𝓧.measurable_X
    (h x).2.2.1 (h x).2.2.2.1 t y

theorem measurable_reflected_vertexProbability
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {𝓧 : ProcessFamily V} (h : IsReflectedWalk G w hmin 𝓧) (x y : V) :
    Measurable (fun s : ℝ => (𝓧.P x {ω | 𝓧.X (Real.toNNReal s) ω = some y}).toReal) :=
  measurable_of_rightContinuous (reflected_vertexProbability_rightContinuous h x y)

theorem reflected_vertexProbability_mem_Icc (𝓧 : ProcessFamily V) (x y : V) (t : ℝ) :
    (𝓧.P x {ω | 𝓧.X (Real.toNNReal t) ω = some y}).toReal ∈ Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

end ReflectedGMS
