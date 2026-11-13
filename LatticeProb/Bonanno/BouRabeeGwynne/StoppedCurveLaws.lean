/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.StoppedCurveLaws at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.CurveSpace
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedWalk
import LatticeProb.Bonanno.BouRabeeGwynne.TilingNetwork
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The actual laws occurring in Theorem A

These definitions fix the processes, interpolation, exit convention and measures.
They assume no convergence statement. Existence and measurability assertions in
the main target remain proof obligations, not fields of an assumed model.
-/

open scoped BigOperators ENNReal NNReal unitInterval
open MeasureTheory ProbabilityTheory

namespace BouRabeeGwynne

noncomputable instance curveSpaceMeasurableSpace (d : ℕ) : MeasurableSpace (CurveSpace d) :=
  borel (CurveSpace d)

instance curveSpaceBorelSpace (d : ℕ) : BorelSpace (CurveSpace d) := ⟨rfl⟩

/-- A continuous Euclidean path on all nonnegative times. -/
abbrev BrownianPath (d : ℕ) := C(ℝ≥0, Euc d)

instance brownianPathMeasurableSpace (d : ℕ) : MeasurableSpace (BrownianPath d) :=
  borel (BrownianPath d)

instance brownianPathBorelSpace (d : ℕ) : BorelSpace (BrownianPath d) := ⟨rfl⟩

/-- Standard zero-start Brownian law: independent whole coordinate processes,
each having the actual mathlib Brownian finite-dimensional Gaussian laws. -/
def IsStandardBrownianLaw {d : ℕ} (μ : Measure (BrownianPath d)) : Prop :=
  IsProbabilityMeasure μ ∧
  (∀ i : Fin d, IsBrownianReal (fun t ω => ω t i) μ) ∧
  iIndepFun (fun (i : Fin d) (ω : BrownianPath d) => fun t : ℝ≥0 => ω t i) μ

/-- Uniform-time polygonal interpolation of the first `m` steps, normalized to
`[0,1]`. The clamped increments give a continuous formula also when `m = 0`. -/
noncomputable def polygonalCurve {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) (m : ℕ) : C(unitInterval, Euc d) where
  toFun t := pos (ω 0) + ∑ k ∈ Finset.range m,
    max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k))
  continuous_toFun := by fun_prop

@[simp] lemma polygonalCurve_zero {d : ℕ} {V : Type*} (pos : V → Euc d)
    (ω : ℕ → V) : polygonalCurve pos ω 0 = ContinuousMap.const _ (pos (ω 0)) := by
  ext t
  simp [polygonalCurve]

/-- Stop at the first discrete vertex exit and include the segment to that exit
vertex. The value on never-exiting paths is a totalization only; the theorem
separately requires that such paths have probability zero. -/
noncomputable def stoppedPolygonalCurve {d : ℕ} {V : Type*} (pos : V → Euc d)
    (A : Set V) (ω : ℕ → V) : CurveSpace d :=
  CurveSpace.project (polygonalCurve pos ω
    ((FiniteConductanceNetwork.exitTime A ω).untopD 0))

/-- First continuous exit from `U` of the path shifted to start at `z`.
An empty set of exit times has infimum infinity. -/
noncomputable def continuousExitTime {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) : ℝ≥0∞ :=
  ⨅ t : {t : ℝ≥0 // z + ω t ∉ U}, (t.val : ℝ≥0∞)

/-- A stopped Brownian representative, with its actual exit time normalized to
`[0,1]`. Infinity is totalized to duration zero and excluded almost surely in
the main statement. -/
noncomputable def stoppedBrownianRepresentative {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) : C(unitInterval, Euc d) where
  toFun t := z + ω (⟨(t : ℝ) * ((continuousExitTime U z ω).toNNReal : ℝ),
    mul_nonneg t.property.1 (continuousExitTime U z ω).toNNReal.property⟩ : ℝ≥0)
  continuous_toFun := by
    apply continuous_const.add
    apply ω.continuous.comp
    fun_prop

noncomputable def stoppedBrownianCurve {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (ω : BrownianPath d) : CurveSpace d :=
  CurveSpace.project (stoppedBrownianRepresentative U z ω)

/-- The target stopped law is the pushforward of the specified Brownian law. -/
noncomputable def stoppedBrownianLaw {d : ℕ} (U : Set (Euc d)) (z : Euc d)
    (μ : Measure (BrownianPath d)) : Measure (CurveSpace d) :=
  μ.map (stoppedBrownianCurve U z)

/-- A measure is the actual stopped conductance-walk curve law. The finite
region contains the entire closed graph region and the selected initial vertex;
the latter matters when the nearest vertex already lies outside `U`.

Positive normalization, finite exit and measurable interpolation are required
as parts of this predicate. Theorem A asserts existence of a measure satisfying
it from the geometric hypotheses; they are not added hypotheses of Theorem A.
-/
def IsStoppedTilingWalkLaw {d : ℕ} (T : OrthogonalTiling d) (U : Set (Euc d))
    (v₀ : T.V) (μ : Measure (CurveSpace d)) : Prop := by
  classical
  exact ∃ (R : Finset T.V) (hR : (R : Set T.V) = T.closedVertices U ∪ {v₀}),
    letI : MeasurableSpace R := ⊤
    let A : Set R := {v | T.pos v.val ∈ U}
    let N := T.finiteNetwork (R : Set T.V)
    ∃ (hpos : ∀ v ∈ A, 0 < N.totalConductance v)
      (start : R), start.val = v₀ ∧
      let law := N.trajectoryLaw A hpos start
      let curve := stoppedPolygonalCurve (fun v : R => T.pos v.val) A
      AEMeasurable curve law ∧
      (∀ᵐ ω ∂law, FiniteConductanceNetwork.exitTime A ω ≠ ⊤) ∧
      IsProbabilityMeasure μ ∧ μ = law.map curve

end BouRabeeGwynne
