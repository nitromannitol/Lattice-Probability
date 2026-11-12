/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Function.L2Space
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux2
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimates
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import Mathlib.Topology.Path
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic
import LatticeProb.Bonanno.LQGMetric.Statement.Metric
import Mathlib.Algebra.Order.Round
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.MetricSpace.Polish
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Rat
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Metric.Internal

/-!
# GM Lemma 3.7, the Weyl-scaling step (task P2-M2E2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, proof
of Lemma 3.7, l. 1346–1347: "By Axiom III (Weyl scaling) subtracting `h_{4r}(0)` from `h` results
in scaling `D_h` and `D̃_h` by the same factor, so does not affect the occurrence of `𝖤_r(z)`.
Hence it suffices to prove (3.?) with `h|_{𝔸_{r/2,2r}(z)}` in place of
`(h − h_{4r}(z))|_{𝔸_{r/2,2r}(z)}`."

* `len_of_scale`, `internal_of_scale`, `setDist_of_scale`: lengths, internal metrics and set
  distances of `D₂ = e·D₁` are `e` times those of `D₁` (from `curveLength_comp_of_edist_eq` and
  `internalEDist_image_of_edist_eq`, LM S-int (d)).
* `mem_goodAnnulus_iff_of_scale`: `𝖤_r(z)` is invariant under multiplying `D_h`, `D̃_h` by the
  same `e > 0`.
* `L3_7loc`: GM's reduced statement (Lemma 3.7 with `h|_{𝔸_{r/2,2r}(z)}`), and
  `gm_L3_7_of_loc : L3_7loc → L3_7`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

section Scale
variable {D₁ D₂ : ContMetric} {e : ℝ}

lemma edist_of_scale (he : 0 < e) (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (a b : ℂ) :
    edist (D₂.pt a) (D₂.pt b) = ENNReal.ofReal e * edist (D₁.pt a) (D₁.pt b) := by
  rw [ContMetric.edist_pt, ContMetric.edist_pt, h, ENNReal.ofReal_mul he.le]

lemma internal_of_scale (he : 0 < e) (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (V : Set ℂ)
    (u v : ℂ) : D₂.internal V u v = ENNReal.ofReal e * D₁.internal V u v := by
  have := internalEDist_image_of_edist_eq (X := D₁.Space) (Z := D₂.Space) (Equiv.refl ℂ)
    (c := ENNReal.ofReal e) (ENNReal.ofReal_pos.2 he).ne' ENNReal.ofReal_ne_top
    (fun a b => edist_of_scale he h a b) (D₁.pt '' V) u v
  unfold ContMetric.internal
  convert this using 2
  all_goals first
    | rfl
    | (ext x; exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => hyx ▸ hy⟩)

lemma setDist_eq_iInf (D : ContMetric) (A B : Set ℂ) :
    setDist D A B = ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (D.1 (x, y)) := by
  rw [setDist, setEDist_eq_iInf, iInf_image]
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  rw [iInf_image]
  exact iInf_congr fun y => iInf_congr fun _ => ContMetric.edist_pt D x y

lemma setDist_of_scale (he : 0 < e) (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (A B : Set ℂ) :
    setDist D₂ A B = ENNReal.ofReal e * setDist D₁ A B := by
  have hc0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  simp only [setDist_eq_iInf, h, ENNReal.ofReal_mul he.le,
    ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]

end Scale

/-! ## Lengths of paths in `V` are determined by the internal metric of `V` -/

/-- **GM l. 1348** (the distance across the annulus in condition 3 is determined by `h|_V`):
if the closed annulus `{ρ₁ ≤ |w − z| ≤ ρ₂}` lies in `V`, then `D(∂B_{ρ₁}(z), ∂B_{ρ₂}(z))` is the
infimum of the internal distances `D(x, y; V)`. A near-geodesic from `x` to `y` contains a
segment in the closed annulus from its last visit of `B̄_{ρ₁}(z)` before its first visit of
`{|w − z| ≥ ρ₂}` (own elementary argument). -/
theorem setDist_spheres_eq_internal (D : ContMetric) (hD : D.IsLength) {V : Set ℂ} {z : ℂ}
    {ρ₁ ρ₂ : ℝ} (h12 : ρ₁ < ρ₂) (hsub : ∀ w : ℂ, ρ₁ ≤ ‖w - z‖ → ‖w - z‖ ≤ ρ₂ → w ∈ V) :
    setDist D (sphere z ρ₁) (sphere z ρ₂) =
      ⨅ x ∈ sphere z ρ₁, ⨅ y ∈ sphere z ρ₂, D.internal V x y := by
  rw [setDist_eq_iInf]
  refine le_antisymm (iInf₂_mono fun x _ => iInf₂_mono fun y _ => ?_)
    (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  · rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hab, hPc, hPa, hPb, hlen⟩ :=
    isLengthSpace_iff_curves.1 hD (D.pt x) (D.pt y) ε (by exact_mod_cast hε)
  set f : ℝ → ℝ := fun t => ‖D.unpt (P t) - z‖ with hf
  have hfc : ContinuousOn f (Icc a b) :=
    (continuous_norm.comp (D.continuous_unpt.sub continuous_const)).comp_continuousOn hPc
  have hfa : f a = ρ₁ := by simp only [hf, hPa]; exact mem_sphere_iff_norm.1 hx
  have hfb : f b = ρ₂ := by simp only [hf, hPb]; exact mem_sphere_iff_norm.1 hy
  -- first time `t₂` with `f ≥ ρ₂`
  obtain ⟨t₂, ht₂, hft₂, hbef⟩ := exists_first_hit (P := f) hfc (isClosed_Ici (a := ρ₂))
    ⟨b, ⟨hab, le_rfl⟩, by rw [hfb]; exact mem_Ici.2 le_rfl⟩
  have hft₂' : ρ₂ ≤ f t₂ := hft₂
  have hat₂ : a < t₂ := by
    rcases ht₂.1.eq_or_lt with h | h
    · rw [← h, hfa] at hft₂'; linarith
    · exact h
  have hf2 : f t₂ = ρ₂ := by
    refine le_antisymm ?_ hft₂'
    have hne : (𝓝[Ico a t₂] t₂).NeBot := right_nhdsWithin_Ico_neBot hat₂
    have hcw : ContinuousWithinAt f (Ico a t₂) t₂ :=
      (hfc t₂ ht₂).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht₂.2))
    exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht =>
      (not_le.1 fun h => hbef t ht (mem_Ici.2 h)).le)
  -- last time `t₁ ≤ t₂` with `f ≤ ρ₁`
  set S : Set ℝ := Icc a t₂ ∩ f ⁻¹' Iic ρ₁ with hS
  have hSc : IsClosed S :=
    (hfc.mono (Icc_subset_Icc le_rfl ht₂.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hat₂.le⟩, by rw [mem_preimage, hfa]; exact mem_Iic.2 le_rfl⟩
  have hSb : BddAbove S := ⟨t₂, fun t ht => ht.1.2⟩
  set t₁ := sSup S with ht₁def
  have ht₁S : t₁ ∈ S := hSc.csSup_mem hSne hSb
  have hft₁ : f t₁ ≤ ρ₁ := ht₁S.2
  have hafter : ∀ t ∈ Ioc t₁ t₂, ρ₁ < f t := fun t ht => by
    by_contra hc
    exact absurd (le_csSup hSb ⟨⟨ht₁S.1.1.trans ht.1.le, ht.2⟩, mem_Iic.2 (not_lt.1 hc)⟩)
      (not_le.2 ht.1)
  have ht₁₂ : t₁ < t₂ := by
    rcases ht₁S.1.2.eq_or_lt with h | h
    · rw [h, hf2] at hft₁; linarith
    · exact h
  have hf1 : f t₁ = ρ₁ := by
    refine le_antisymm hft₁ ?_
    have hne : (𝓝[Ioc t₁ t₂] t₁).NeBot := left_nhdsWithin_Ioc_neBot ht₁₂
    have hcw : ContinuousWithinAt f (Ioc t₁ t₂) t₁ :=
      (hfc t₁ ⟨ht₁S.1.1, ht₁S.1.2.trans ht₂.2⟩).mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁S.1.1 ht₂.2))
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun t ht => (hafter t ht).le)
  have hsub12 : Icc t₁ t₂ ⊆ Icc a b := Icc_subset_Icc ht₁S.1.1 ht₂.2
  have hmaps : MapsTo P (Icc t₁ t₂) (D.pt '' V) := fun t ht => by
    refine ⟨D.unpt (P t), hsub _ ?_ ?_, rfl⟩
    · rcases ht.1.eq_or_lt with h | h
      · rw [← h]; exact hf1.ge
      · exact (hafter t ⟨h, ht.2⟩).le
    · rcases ht.2.eq_or_lt with h | h
      · rw [h]; exact hf2.le
      · exact (not_le.1 fun hc => hbef t ⟨(ht₁S.1.1.trans ht.1), h⟩ (mem_Ici.2 hc)).le
  have hx' : D.unpt (P t₁) ∈ sphere z ρ₁ := mem_sphere_iff_norm.2 hf1
  have hy' : D.unpt (P t₂) ∈ sphere z ρ₂ := mem_sphere_iff_norm.2 hf2
  calc ⨅ x ∈ sphere z ρ₁, ⨅ y ∈ sphere z ρ₂, D.internal V x y
      ≤ D.internal V (D.unpt (P t₁)) (D.unpt (P t₂)) := iInf₂_le_of_le _ hx' (iInf₂_le _ hy')
    _ ≤ curveLength P t₁ t₂ :=
        internalEDist_le_curveLength ht₁₂.le (hPc.mono hsub12) hmaps
    _ ≤ curveLength P a b := eVariationOn.mono _ hsub12
    _ ≤ edist (D.pt x) (D.pt y) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (D.1 (x, y)) + ε := by
        rw [ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal]

/-! ## The hypothesis of condition 2 through the internal metric (GM l. 1350–1353) -/

end LQGMetric.GM
