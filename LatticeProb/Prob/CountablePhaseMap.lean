import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.Pi

/-! Measurable phase maps on a countable union of finite-dimensional spaces. -/

open MeasureTheory Set

namespace LatticeProb

/-- A marked coordinate vector with a finite, variable number of coordinates. -/
abbrev CountablePhaseSpace (E : Type*) := Σ n : ℕ, E × (Fin n → ℝ)

/-- Apply a coordinate phase while keeping the mark and the coordinate count. -/
noncomputable def countablePhaseMap {E : Type*} (a : ℝ) (θ : ∀ n, E → (Fin n → ℝ)) :
    CountablePhaseSpace E → CountablePhaseSpace E
  | ⟨n, e, x⟩ => ⟨n, e, fun i => Int.fract (a * x i - θ n e i)⟩

/-- The coordinate count is unchanged by the phase map. -/
theorem countablePhaseMap_fst {E : Type*} (a : ℝ) (θ : ∀ n, E → (Fin n → ℝ))
    (x : CountablePhaseSpace E) : (countablePhaseMap a θ x).1 = x.1 := by
  cases x
  rfl

/-- Each set of vectors of a fixed coordinate count is measurable. -/
theorem measurableSet_countablePhase_count {E : Type*} [MeasurableSpace E] (n : ℕ) :
    MeasurableSet {x : CountablePhaseSpace E | x.1 = n} := by
  change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
    (Sigma.mk i)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  change MeasurableSet {x : E × (Fin i → ℝ) | i = n}
  by_cases h : i = n
  · simp only [h, ofPred_true]
    exact MeasurableSet.univ
  · simp only [h, ofPred_false]
    exact MeasurableSet.empty

/-- A phase map with measurable mark-dependent shifts is measurable. -/
theorem measurable_countablePhaseMap {E : Type*} [MeasurableSpace E] (a : ℝ)
    (θ : ∀ n, E → (Fin n → ℝ)) (hθ : ∀ n, Measurable (θ n)) :
    Measurable (countablePhaseMap a θ) := by
  intro s hs
  change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
    (Sigma.mk i)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro i
  change MeasurableSet ((fun x : E × (Fin i → ℝ) =>
    (x.1, fun j => Int.fract (a * x.2 j - θ i x.1 j))) ⁻¹' ((@Sigma.mk ℕ (fun n => E × (Fin n → ℝ)) i) ⁻¹' s))
  have hs' : MeasurableSet ((@Sigma.mk ℕ (fun n => E × (Fin n → ℝ)) i) ⁻¹' s) := by
    change MeasurableSet[⨅ j : ℕ, (inferInstance : MeasurableSpace (E × (Fin j → ℝ))).map
      (Sigma.mk j)] s at hs
    exact (MeasurableSpace.measurableSet_iInf.mp hs) i
  apply hs'.preimage
  refine measurable_fst.prodMk (Measurable.of_eval fun j => ?_)
  exact measurable_fract.comp ((measurable_const.mul (measurable_pi_apply j |>.comp measurable_snd)).sub
    ((measurable_pi_apply j).comp ((hθ i).comp measurable_fst)))

end LatticeProb
