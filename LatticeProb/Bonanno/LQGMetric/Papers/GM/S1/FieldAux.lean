/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.FieldAux at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgLaw
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Field-layer helpers for GM §1.4 (GM.S1.16a, GM.S1.18′)

* `isWholePlaneGFF_id_map`, `normGFFLaw_eq`: `normGFFLaw` is the law of every normalized
  whole-plane GFF (law uniqueness `CircleAvg.map_eq_of_isNormalizedWPGFF`, tasks P2-FINV,
  P2-FCIRC);
* `measure_addFun_preimage_eq_zero` (DEC-A node `GFF.CM-wp`, null-set form): for `φ ∈ 𝓓(ℂ)` with
  zero average over `∂𝔻` and `h` a normalized whole-plane GFF, `P[h ∈ A] = 0 ⇒ P[h + φ ∈ A] = 0`.
  Proof: both `h` and `h + φ` are normalized, hence `sigma0`-measurable functions of their
  mean-zero pairings (`GFFLaw` recentering), whose laws are mutually absolutely continuous by the
  whole-plane Cameron–Martin theorem `lawPair0_addFun_ac` (Bogachev, *Gaussian Measures*,
  Thm 2.4.5; Berestycki–Powell, arXiv:2404.16642, Prop. `lem:CMGFF`);
* `exists_noGap_test`: the test function `f = φ − (φ_1(0)/ψ_1(0)) ψ` of DEC-A D-A2 (iii)
  (`φ ≡ 1` near `L`, `ψ ≥ 0` a bump at `−1`), with `f ≥ 1` within distance `1/4` of the left side
  `L` and zero average over `∂𝔻`;
* `xiGamma_pos`: `ξ > 0` for `γ > 0`.

Sources: DEC-A D-A2 (iii) (`decisions/DEC-A.md`); the test-function construction and the
positivity of a circle average are own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM
open GFFInv

/-- the law of a whole-plane GFF, as a field on `𝒟'(ℂ)` -/
theorem isWholePlaneGFF_id_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsWholePlaneGFF id (P.map h) where
  measurable := measurable_id
  gaussian := ⟨fun I => by
    have hm : Measurable fun g : DistC => I.restrict fun φ : TestC0 => g φ.1 :=
      measurable_pi_iff.2 fun _ => GFFInv.measurable_pair _
    refine ⟨hm.aemeasurable, ?_⟩
    have e := Measure.map_map hm hh.measurable (μ := P)
    change IsGaussian ((P.map h).map fun g : DistC => I.restrict fun φ : TestC0 => g φ.1)
    rw [e]
    exact (hh.gaussian.hasGaussianLaw I).isGaussian_map⟩
  centered := fun φ => by
    have e := integral_map (μ := P) hh.measurable.aemeasurable
      (f := fun g : DistC => g φ.1) (GFFInv.measurable_pair _).aestronglyMeasurable
    change ∫ g, g φ.1 ∂(P.map h) = 0
    rw [e]
    exact hh.centered φ
  covariance_eq := fun φ ψ => by
    have e := covariance_map (μ := P) (X := fun g : DistC => g φ.1) (Y := fun g : DistC => g ψ.1)
      (GFFInv.measurable_pair _).aestronglyMeasurable
      (GFFInv.measurable_pair _).aestronglyMeasurable hh.measurable.aemeasurable
    change cov[fun g : DistC => g φ.1, fun g : DistC => g ψ.1; P.map h] = _
    rw [e]
    exact hh.covariance_eq φ ψ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### The test function of DEC-A D-A2 (iii) -/

lemma chiDZZ_pos (γ : ℝ) : 0 < chiDZZ γ := by
  unfold chiDZZ
  split_ifs with h
  · exact h.choose_spec.1
  · norm_num

lemma xiGamma_pos {γ : ℝ} (hγ : 0 < γ) : 0 < xiGamma γ :=
  div_pos hγ (div_pos two_pos (chiDZZ_pos γ))

end GM
end LQGMetric
