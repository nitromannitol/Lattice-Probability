/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.WedgeLawRef at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LocalRule
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Logic.Equiv.List
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.BoundaryExistence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceAS
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodMeasurableReg
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Basic
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasND
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeTranslation
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.FractionalMoments
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularClosure
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSampleKolmogorov
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.LogSingularity
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaOffsets
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AllOffsetsModulus
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.RealDeriv
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AtomlessUncond
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaLogSing
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.SetAlgebra

/-!
`Prop16Asm.RefWedgeLawUnique γ α`: for two reference tuples `(X, A)` on `(Ω, P)` and `(X', A')`
on `(Ω', P')` (free field modulo constants, independent `α`-wedge radial process), the reference
fields `canonical γ (h† + Q(−log|·|) + A_{−log|·|})` have the same `fieldLawFull H` law.
In the paper this is implicit in the definition of the wedge (Sheffield, arXiv:1012.4797,
§1.6, (1.10); Duplantier–Miller–Sheffield, arXiv:1409.7055, Def. 4.5: the wedge is *defined* by
the law of this construction). The Lean proof, for `0 < γ < 2`, `α < Q`:

1. **Canonical data from coordinates.** On the a.s. good event (`LogSingGood.wedgeRefGoodAS_holds`)
   the data of `canonical γ W` is `Dγ (coordsFull W)` for a fixed measurable `Dγ`
   (`WedgeMeas.canonical_eq_resc`, `WedgeMeas.scaleG_coords`).
2. **Coordinates from (lateral Gaussian family, radial path).** A.s.
   `coordsFull W = Φ (L, A)` where `L n = X(fcN n) − X(radSmear (fcN n))` is a countable family
   of balanced Gaussian differences (`WedgeTK.latCoords_X_ae`) and `A` is the (a.s. continuous)
   radial path, read through the measurable dyadic extension `extP` (own elementary device).
3. **Laws.** `L` and `A` are independent (functions of `X` and of `A`); the law of `L` is fixed by
   its covariances (`WedgeRes.map_gaussFam_eq₂`: finite-dimensional distributions determine the
   law, Kallenberg, *Foundations of Modern Probability*, 2nd ed., Prop. 3.2 / Thm. 6.16, used
   through mathlib's projective-limit uniqueness); the law of `A` is the image of two independent
   Brownian path laws (`WedgeRes.map_path_eq`) under `wedgePath`, measurable on pairs of
   continuous paths (`WedgeMeas.measurable_wedgePath_joint`).

Own bookkeeping on top of the cited project results (the law identities are the standard
"finite-dimensional distributions determine the law" and "independence gives the product law").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace WedgeLaw

open CoordsFull

/-! ## 1. A measurable continuous extension of a path from dyadic points -/

/-- The path `a` read at the dyadic roundings `dyadicRound k t → t`. Equal to `a` for
continuous `a`, and jointly measurable in `(a, t)` for the product σ-algebra on paths. -/
def extP (a : ℝ → ℝ) (t : ℝ) : ℝ := limUnder atTop fun k : ℕ => a (dyadicRound k t)

theorem measurable_extP : Measurable fun p : (ℝ → ℝ) × ℝ => extP p.1 p.2 := by
  have hk : ∀ k : ℕ, Measurable fun p : (ℝ → ℝ) × ℝ => p.1 (dyadicRound k p.2) := by
    intro k
    have hg : Measurable fun q : (ℝ → ℝ) × ℤ => q.1 ((q.2 : ℝ) / (2 : ℝ) ^ k) :=
      measurable_from_prod_countable_left fun m => by
        exact measurable_pi_apply ((m : ℝ) / (2 : ℝ) ^ k)
    have hfl : Measurable fun t : ℝ => ⌊(2 : ℝ) ^ k * t⌋ :=
      Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ k))
    exact hg.comp (measurable_fst.prodMk (hfl.comp measurable_snd))
  exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable

theorem extP_of_continuous {a : ℝ → ℝ} (ha : Continuous a) : extP a = a := by
  funext t
  exact ((ha.tendsto t).comp (GoodMeas.tendsto_dyadicRound' t)).limUnder_eq

/-! ## 2. The coordinate map `Φ` and the canonical data map `Dγ` -/

/-! ## 3. Per-witness representation -/

/-- The radial path. -/
def pathA {Ω : Type*} (A : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun t => A t ω

/-- Pairs of continuous paths (the natural domain of `wedgePath`). -/
abbrev CPair : Type := {q : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) // Continuous q.1 ∧ Continuous q.2}

/-- The wedge path of a pair of continuous paths. -/
def wS (α Q : ℝ) (q : CPair) : ℝ → ℝ := wedgePath α Q q.1.1 q.1.2

theorem measurable_wS (α Q : ℝ) : Measurable (wS α Q) := by
  have h := WedgeMeas.measurable_wedgePath_joint (Ω := CPair) α Q
    (B := fun s q => q.1.1 s) (B' := fun s q => q.1.2 s) (fun q => q.2.1) (fun q => q.2.2)
    (fun s => (measurable_pi_apply s).comp (measurable_fst.comp measurable_subtype_coe))
    (fun s => (measurable_pi_apply s).comp (measurable_snd.comp measurable_subtype_coe))
  exact measurable_pi_iff.2 fun t => h.comp (measurable_id.prodMk measurable_const)

section Witness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A measurable reading of the radial path through a pair of continuous Brownian paths. -/
theorem exists_path_rep {A : ℝ → Ω → ℝ} {α Q : ℝ} (hA : IsWedgeProcess α Q A P) :
    ∃ ι : Ω → CPair, Measurable ι ∧ (pathA A =ᵐ[P] wS α Q ∘ ι) ∧
      ∃ B B' : ℝ≥0 → Ω → ℝ, IsPreBrownianReal B P ∧ IsPreBrownianReal B' P ∧
        Measurable (fun ω s => B s ω) ∧ Measurable (fun ω s => B' s ω) ∧
        IndepFun (fun ω s => B s ω) (fun ω s => B' s ω) P ∧
        ∀ ω, (ι ω).1 = ((fun s => B s ω), (fun s => B' s ω)) := by
  obtain ⟨B, B', hB, hB', hind, hAB⟩ := hA
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hB
  obtain ⟨Bt', hBtm', hBtc', hBtB'⟩ := WedgeRes.exists_good_version hB'
  have hpm : Measurable fun ω s => Bt s ω :=
    measurable_pi_iff.2 fun s => hBtm.comp (measurable_const.prodMk measurable_id)
  have hpm' : Measurable fun ω s => Bt' s ω :=
    measurable_pi_iff.2 fun s => hBtm'.comp (measurable_const.prodMk measurable_id)
  refine ⟨fun ω => ⟨((fun s => Bt s ω), (fun s => Bt' s ω)), hBtc ω, hBtc' ω⟩,
    (hpm.prodMk hpm').subtype_mk, ?_, Bt, Bt', ?_, ?_, hpm, hpm', ?_, fun ω => rfl⟩
  · filter_upwards [hBtB, hBtB'] with ω h1 h2
    funext t
    have e1 : (fun s => B s ω) = fun s => Bt s ω := funext fun s => (h1 s).symm
    have e2 : (fun s => B' s ω) = fun s => Bt' s ω := funext fun s => (h2 s).symm
    show A t ω = wedgePath α Q (fun s => Bt s ω) (fun s => Bt' s ω) t
    rw [hAB ω t, e1, e2]
  · exact hB.toIsPreBrownianReal.congr fun s => (hBtB.mono fun ω h => (h s).symm)
  · exact hB'.toIsPreBrownianReal.congr fun s => (hBtB'.mono fun ω h => (h s).symm)
  · exact hind.congr (hBtB.mono fun ω h => funext fun s => (h s).symm)
      (hBtB'.mono fun ω h => funext fun s => (h s).symm)

theorem aemeasurable_pathA {A : ℝ → Ω → ℝ} {α Q : ℝ} (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (pathA A) P := by
  obtain ⟨ι, hι, hae, -⟩ := exists_path_rep hA
  exact ((measurable_wS α Q).comp hι).aemeasurable.congr hae.symm

end Witness

/-! ## 4. Cross-witness law identities -/

section Cross

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

end Cross

end WedgeLaw

end QuantumZipper
