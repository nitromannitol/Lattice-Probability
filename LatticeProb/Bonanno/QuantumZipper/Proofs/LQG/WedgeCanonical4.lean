/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeCanonical4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FiniteArea
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity

/-!
# M4-A5-WEDGE (TASKS R23): assembly of (a), (b), (c) from the two analytic inputs

* `continuous_wedgePath`, `ae_continuous_wedgeProcess`: the wedge radial path is continuous for
  continuous driving paths started at `0` (the two branches glue at `t = 0` because the
  backward path vanishes at its last zero; if the zero set is unbounded, `lastZero` is the junk
  value `0` and the backward path vanishes there too).
* `ae_qAreaMeasure_wedgeField_eq`: the local density rule `μ_W = e^{γ g} μ_X` of
  `WedgeCan.qAreaMeasure_wedgeField_eq` holds almost surely, together with the free-field inputs
  (no circle atoms, positivity) and continuity of the profile `g` on `ℍ`.
* `ae_hasAreaProfile_wedgeField_of`: R23 (a) from the two analytic inputs (finite area of
  `B(0,a) ∩ ℍ`, infinite total area), via `AreaProfile.hasAreaProfile_of`.
* `ae_wedge_canonical_spec_of_profile`: R23 (b) from (a) (`CanonicalGood.scaleParam_spec`,
  `CanonicalGood.canonical_spec`, `LogSingGood.wedgeRefGoodAS_holds`).
* `ae_unitArea_of_fieldLawFull_eq`: transfer of the event
  `IsLQGGood γ x ∧ μ_x(B(0,1) ∩ ℍ) = 1` through an identity of `fieldLawFull` laws (the event
  is a measurable function of `coordsFull`).

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6, p. 21
("a finite amount of µ_h mass in each bounded neighborhood of 0 and an infinite amount in each
neighborhood of ∞", and the normalization `µ_h(B₁(0) ∩ ℍ) = 1`). The assembly steps are
elementary (own arguments).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeCan4

/-! ## 1. Continuity of the wedge radial path -/

/-- A continuous path with `g 0 = 0` vanishes at its last zero (also in the junk case of an
unbounded zero set, where `lastZero g = 0`). -/
theorem apply_lastZero_eq_zero {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0) :
    g (lastZero g) = 0 := by
  unfold lastZero
  by_cases hb : BddAbove {s : ℝ | 0 ≤ s ∧ g s = 0}
  · have hc : IsClosed {s : ℝ | 0 ≤ s ∧ g s = 0} :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hg continuous_const)
    exact (hc.csSup_mem ⟨0, le_rfl, h0⟩ hb).2
  · rw [Real.sSup_of_not_bddAbove hb]; exact h0

/-- **The wedge radial path is continuous** for continuous driving paths started at `0`. -/
theorem continuous_wedgePath {α Q : ℝ} {b b' : ℝ≥0 → ℝ} (hb : Continuous b)
    (hb' : Continuous b') (h0 : b 0 = 0) (h0' : b' 0 = 0) :
    Continuous (wedgePath α Q b b') := by
  set Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s with hBt
  have hBtc : Continuous Bt :=
    (continuous_const.mul (hb'.comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hBt0 : Bt 0 = 0 := by simp [hBt, h0']
  have hz : Bt (lastZero Bt) = 0 := apply_lastZero_eq_zero hBtc hBt0
  show Continuous fun t : ℝ => if 0 ≤ t then Real.sqrt 2 * b t.toNNReal + (α - Q) * t
    else Bt (-t + lastZero Bt)
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact (continuous_const.mul (hb.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  · exact hBtc.comp (continuous_neg.add continuous_const)
  · intro t ht
    have ht' : t = 0 := ht.symm
    subst ht'
    simp [h0, hz]

/-- **A wedge radial process has a.s. continuous paths.** -/
theorem ae_continuous_wedgeProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α Q : ℝ}
    {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) : ∀ᵐ ω ∂P, Continuous fun t => A t ω := by
  obtain ⟨B, B', hB, hB', -, hAe⟩ := hA
  filter_upwards [hB.cont, hB'.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    hB'.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2 h3 h4
  have e : (fun t => A t ω) = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) :=
    funext fun t => hAe ω t
  rw [e]
  exact continuous_wedgePath h1 h2 h3 h4

/-! ## 2. The density rule, almost surely -/

variable {γ α : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}

/-! ## 2b. Input (i) reduces to the unit half-disc -/

/-! ## 3. Transfer of the unit-area event through `fieldLawFull` -/

section Transfer

open Factorization CoordsFull

end Transfer

/-! ## 4. (a), (b), (c) from the two analytic inputs -/

end WedgeCan4

end QuantumZipper
