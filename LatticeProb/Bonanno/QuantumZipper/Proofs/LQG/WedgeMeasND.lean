/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.WedgeMeasND at commit fdb5cad; only the module paths of local imports are changed.
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
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeCanonical4
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMLLN
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
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
# WEDGE-MEAS: wedge data are a.e.-measurable, wedges are a.s. good, R23 (c)

At the pinned mathlib, `Measure.map f P` for a non-a.e.-measurable `f` and `P ≠ 0` is a Dirac
mass (`Measure.map_of_not_aemeasurable_of_ne_zero`). So `IsQuantumWedge` forces the data map of
`Y` to be a.e.-measurable as soon as the **reference wedge law is not a Dirac mass**
(`fieldLawFull_wedgeRef_ne_dirac`). Proof (own argument, no published source needed; it only uses
Sheffield, arXiv:1012.4797, §1.6: the semicircle average of the wedge field at radius `e^{-t}` is
`A_t + Q t`, and the last-exit description of `A` on `t < 0`):

* the radial averages about `0` of the canonical wedge field `canonical γ W` are read by the full
  coordinates (`CoordsFull.radAvgReg_congr_full`) and equal `Q(−log r) + A(−log r − log s)`,
  `s = scaleParam γ W > 0` (`WedgeMeasCoord.radAvgReg_rescale_wedgeField`);
* if the law were `δ_c`, two a.s.-typical samples `ω₁, ω₂` would give
  `A(t − ℓ₁)(ω₁) = A(t − ℓ₂)(ω₂)` for all `t`; since `A(0) = 0` and `A > 0` on `(−∞,0)` a.s.
  (the backward process `B̃_s = √2 b'_s + (Q−α)s → +∞` by the Brownian law of large numbers
  `BMLLN.ae_tendsto_div_atTop`, Le Gall 2016, Exercise 2.25, so after its last zero it is
  positive), `ℓ₁ = ℓ₂` (`shift_eq_of_pos`) and `A(1)` would be a.s. constant, contradicting
  `A(1) = √2 b_1 + α − Q` with `b_1 ∼ N(0,1)`.

`s > 0` a.s. is where the two analytic inputs `WedgeCan4.WedgeFiniteNearZero` /
`WedgeInfiniteTotal` enter (via `WedgeCan4.ae_wedge_canonical_spec_of_inputs`); without them the
canonicalization may degenerate (`scaleParam = 0`), and then the reference data can be
deterministic junk, so the inputs are genuinely needed for this route.

Main results (all conditional on the two analytic inputs, `0 < γ < 2`):
`aemeasurable_dataFull_of_isQuantumWedge`, `wedgeDataAEMeasStmt_of_inputs`,
`wedgeGoodStmt_of_inputs`, `IsQuantumWedge.ae_unitArea` (TASKS R23 (c) form, without `hm`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace WedgeMeasND

/-! ## 1. Deterministic lemmas -/

/-- A continuous path with `g 0 = 0` and `g → +∞` is positive after its last zero. -/
theorem pos_of_lastZero_lt {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0)
    (hinf : Tendsto g atTop atTop) {s : ℝ} (hs : lastZero g < s) : 0 < g s := by
  obtain ⟨M, hM⟩ := (hinf.eventually_gt_atTop 0).exists_forall_of_atTop
  have hbdd : BddAbove {s | 0 ≤ s ∧ g s = 0} := ⟨M, fun t ht => by
    by_contra hlt; push Not at hlt; exact (hM t hlt.le).ne' ht.2⟩
  have hL0 : 0 ≤ lastZero g := le_csSup hbdd ⟨le_rfl, h0⟩
  have hnz : ∀ t, lastZero g < t → g t ≠ 0 := fun t ht hz =>
    absurd (le_csSup hbdd ⟨hL0.trans ht.le, hz⟩) (not_le.2 ht)
  rcases lt_or_gt_of_ne (hnz s hs) with hneg | hpos
  · exfalso
    set s' := max M s with hs'
    have hss' : s ≤ s' := le_max_right _ _
    have hgs' : 0 < g s' := hM s' (le_max_left _ _)
    obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hss' hg.continuousOn
      (show (0 : ℝ) ∈ Icc (g s) (g s') from ⟨hneg.le, hgs'.le⟩)
    exact hnz c (hs.trans_le hc.1) hgc
  · exact hpos

/-- The wedge path is positive on `(−∞,0)` when `b'` is continuous, starts at `0` and
`b'_t / t → 0`. -/
theorem wedgePath_pos_of_neg {α Q : ℝ} (hαQ : α < Q) {b b' : ℝ≥0 → ℝ} (hb' : Continuous b')
    (hb'0 : b' 0 = 0) (hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * b' t) atTop (𝓝 0))
    {u : ℝ} (hu : u < 0) : 0 < wedgePath α Q b b' u := by
  set Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s with hBt
  have hc : Continuous Bt :=
    (continuous_const.mul (hb'.comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have h0 : Bt 0 = 0 := by simp [hBt, hb'0]
  have hinf : Tendsto Bt atTop atTop := by
    have he : Tendsto (fun s : ℝ => ((s.toNNReal : ℝ))⁻¹ * b' s.toNNReal) atTop (𝓝 0) :=
      hlim.comp tendsto_real_toNNReal_atTop
    have hl : Tendsto (fun s : ℝ => Real.sqrt 2 * (((s.toNNReal : ℝ))⁻¹ * b' s.toNNReal) +
        (Q - α)) atTop (𝓝 (Q - α)) := by
      simpa using (he.const_mul (Real.sqrt 2)).add_const (Q - α)
    refine (tendsto_id.atTop_mul_pos (by linarith) hl).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [id, hBt, Real.coe_toNNReal _ hs.le]
    field_simp
    ring
  have hw : wedgePath α Q b b' u = Bt (-u + lastZero Bt) := by
    simp only [wedgePath, not_le.2 hu, ↓reduceIte, hBt]
  rw [hw]
  exact pos_of_lastZero_lt hc h0 hinf (by linarith)

/-! ## 2. Almost-sure properties of the wedge process -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_wedgeProcess_landmark {α Q : ℝ} (hαQ : α < Q) {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) : ∀ᵐ ω ∂P, A 0 ω = 0 ∧ ∀ u < 0, 0 < A u ω := by
  obtain ⟨B, B', hB, hB', -, hAe⟩ := hA
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero, hB'.cont,
    hB'.toIsPreBrownianReal.eval_zero_ae_eq_zero, BMLLN.ae_tendsto_div_atTop hB']
    with ω h0 h1 h2 h3
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hAe]; exact wedgePath_zero_of_start h0
  · rw [hAe]; exact wedgePath_pos_of_neg hαQ h1 h2 h3 hu

/-! ## 3. The reference wedge law is not a Dirac mass -/

/-! ## 4. Consequences -/

end WedgeMeasND

end QuantumZipper
