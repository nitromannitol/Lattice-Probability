/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCUpper.Model at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma47
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail

/-!
# Model-specific inputs for [18] Lemma 4.7

The event in `UpperMassBoundModel` uses the dyadic LQG area of the actual
`γ`-quantum-cone field in the frozen mating-of-trees coupling. The event in
`CircleAverageSupBoundModel` uses a jointly continuous version of the circle
averages of a normalized whole-plane GFF. These definitions record the
distributional data absent from the abstract G4b interfaces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCUpper

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.GMSLemma27

/-- The canonical GMC measure of a normalized whole-plane GFF. -/
def wholePlaneArea {Ω : Type} [MeasurableSpace Ω] (γ : ℝ)
    (Y : Ω → LQGMetric.DistC) (ω : Ω) : Measure ℂ :=
  CellScaling.lqgArea γ (Y ω)

/-- The area of the frozen coupling's 0-quantum cone, with its own radial
Brownian motions and no free area measure. -/
def zeroConeArea {Ω : Type} [MeasurableSpace Ω] (γ : ℝ)
    (X₀ : Ω → Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℂ :=
  CellScaling.lqgArea γ
    (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)))

/-- The upper-mass event for the actual normalized whole-plane GMC area. -/
def UpperMassBoundWholePlaneModel {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → LQGMetric.DistC} {γ : ℝ}
    (_hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_hY : LQGMetric.IsNormalizedWPGFF Y P) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < wholePlaneArea γ Y ω (ball z δ)} ≤
      ENNReal.ofReal (C * δ ^ β)

/-- The upper-mass event for the frozen coupling's actual 0-cone GMC area. -/
def UpperMassBoundZeroConeModel {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (_hγ : γ ∈ Ioo (0 : ℝ) 2)
    (_D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) : Prop :=
  ∃ ξ β : ℝ, 0 < ξ ∧ 0 < β ∧ ∀ ρ ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ z ∈ ball (0 : ℂ) ρ,
      ENNReal.ofReal (δ ^ ξ) < zeroConeArea γ X₀ B₀ B₀' ω (ball z δ)} ≤
      ENNReal.ofReal (C * δ ^ β)

/-- The sharp supremum estimate for a jointly continuous version of the
circle averages of a normalized whole-plane GFF. -/
def CircleAverageSupBoundModel {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → LQGMetric.DistC)
    (H : ℝ → ℂ → Ω → ℝ)
    (_hX : LQGMetric.IsNormalizedWPGFF X P)
    (_hH : LQGMetric.DFGPS.IsCircleAvgVersion X P H) : Prop :=
  GMS4b.CircleAverageSupBound P H

/-- Every normalized whole-plane GFF has a jointly continuous circle-average
version satisfying the pinned Gaussian covariance interface. -/
theorem exists_circleAvgVersion_normalized {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → LQGMetric.DistC}
    (hX : LQGMetric.IsNormalizedWPGFF X P) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGMetric.DFGPS.IsCircleAvgVersion X P H ∧
        LQGDimension.IsGFFCircleAverage H P := by
  obtain ⟨H, hG, hcont, hae⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hX
  exact ⟨H, ⟨hcont, hae⟩, hG⟩

/-- The normalized GFF model estimate is exactly the circle-average input
consumed by G4b. -/
theorem circleAverageSupBound_of_model {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → LQGMetric.DistC}
    {H : ℝ → ℂ → Ω → ℝ}
    (hX : LQGMetric.IsNormalizedWPGFF X P)
    (hH : LQGMetric.DFGPS.IsCircleAvgVersion X P H)
    (hbound : CircleAverageSupBoundModel P X H hX hH) :
    GMS4b.CircleAverageSupBound P H := hbound

end MatedCRTHarmonic.GMCUpper
