/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusMeas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusL38Trans
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
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
import LatticeProb.Bonanno.LQGMetric.Metric.WeylLQG
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

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

lemma len_of_scale (he : 0 < e) (h : ∀ u v, D₂.1 (u, v) = e * D₁.1 (u, v)) (P : ℝ → ℂ)
    (a b : ℝ) : D₂.len P a b = ENNReal.ofReal e * D₁.len P a b :=
  curveLength_comp_of_edist_eq (f := fun x : D₁.Space => D₂.pt x)
    (fun a b => edist_of_scale he h a b)
    (D₁.pt ∘ P) a b

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

/-- **GM l. 1346**: `𝖤_r(z)` is invariant under multiplying `D_h` and `D̃_h` by the same `e > 0`. -/
theorem mem_goodAnnulus_iff_of_scale {D D' : DistC → ContMetric} {α A C' r : ℝ} {z : ℂ}
    {g₁ g₂ : DistC} {e : ℝ} (he : 0 < e) (h1 : ∀ u v, (D g₂).1 (u, v) = e * (D g₁).1 (u, v))
    (h2 : ∀ u v, (D' g₂).1 (u, v) = e * (D' g₁).1 (u, v)) :
    g₂ ∈ goodAnnulus D D' α A C' r z ↔ g₁ ∈ goodAnnulus D D' α A C' r z := by
  have hc0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  have hct : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlt : ∀ x y : ℝ≥0∞, ENNReal.ofReal e * x < ENNReal.ofReal e * y ↔ x < y :=
    fun x y => ENNReal.mul_lt_mul_iff_right hc0 hct
  have hle : ∀ x y : ℝ≥0∞, ENNReal.ofReal e * x ≤ ENNReal.ofReal e * y ↔ x ≤ y :=
    fun x y => ENNReal.mul_le_mul_iff_right hc0 hct
  have hL : g₂ ∈ gaLong D D' α r z ↔ g₁ ∈ gaLong D D' α r z := by
    simp only [gaLong, mem_ofPred_eq, setDist_of_scale he h1, setDist_of_scale he h2,
      internal_of_scale he h1, len_of_scale he h1, h1, h2, ENNReal.ofReal_mul he.le, hlt]
  have hA : g₂ ∈ gaAround D α A r z ↔ g₁ ∈ gaAround D α A r z := by
    simp only [gaAround, mem_ofPred_eq, setDist_of_scale he h1, len_of_scale he h1,
      mul_left_comm (ENNReal.ofReal A), hle]
  simp only [goodAnnulus, mem_inter_iff, mem_gaCompare_iff_of_scale he h1 h2, hL, hA]

/-! ## Lengths of paths in `V` are determined by the internal metric of `V` -/

/-- the length of `P` on `[a,b]` computed with a function `J` in place of a metric -/
def lenFun (J : ℂ → ℂ → ℝ≥0∞) (P : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
    ∑ i ∈ Finset.range p.1, J (P (p.2.1 (i + 1))) (P (p.2.1 i))

/-- **GM l. 1348** (lengths in condition 3 are determined by `h|_V`, via Axiom II): the
`D`-length of a path in an open set `V` equals its length computed with `D(·,·;V)`. -/
theorem lenFun_internal (D : ContMetric) {V : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hV : MapsTo P (Icc a b) V) :
    lenFun (D.internal V) P a b = D.len P a b := by
  have hPc : ContinuousOn (D.pt ∘ P) (Icc a b) := D.continuous_pt.comp_continuousOn hP
  refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun p => ?_)
  · obtain ⟨n, u, hu, hus⟩ := p
    calc ∑ i ∈ Finset.range n, D.internal V (P (u (i + 1))) (P (u i))
        ≤ ∑ i ∈ Finset.range n, curveLength (D.pt ∘ P) (u i) (u (i + 1)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [ContMetric.internal, internalEDist_comm]
          have hsub : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
            Icc_subset_Icc (hus i).1 (hus (i + 1)).2
          exact internalEDist_le_curveLength (hu (Nat.le_succ i)) (hPc.mono hsub)
            fun t ht => ⟨P t, hV (hsub ht), rfl⟩
      _ = curveLength (D.pt ∘ P) (u 0) (u n) := sum_curveLength_eq _ hu n
      _ ≤ D.len P a b := eVariationOn.mono _ (Icc_subset_Icc (hus 0).1 (hus n).2)
  · exact le_iSup_of_le p (Finset.sum_le_sum fun i _ => edist_le_internalEDist _ _ _)

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

/-- **GM l. 1350–1353**: for `u, v ∈ V` (open) in a proper length metric, `D(u,v) > D(u, ∂V)` iff
`D(u,v; V) > D(u, ∂V)`: if `D(u,v) ≤ D(u,∂V)`, then `D(u,v;V) = D(u,v)` (GM S3.1 (b),
`internalEDist_eq_edist_of_le_infEDist`). -/
theorem setDist_frontier_lt_iff (D : ContMetric) (hD : D.IsLength) [ProperSpace D.Space]
    {V : Set ℂ} (hV : IsOpen V) {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V) :
    setDist D {u} (frontier V) < ENNReal.ofReal (D.1 (u, v)) ↔
      setDist D {u} (frontier V) < D.internal V u v := by
  have hs : setDist D {u} (frontier V) = Metric.infEDist (D.pt u) (D.pt '' frontier V) := by
    rw [setDist, image_singleton, setEDist, iInf_singleton]
  constructor
  · intro h
    exact h.trans_le (by rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _)
  · intro h
    by_contra hc
    push Not at hc
    rw [hs, ← ContMetric.edist_pt] at hc
    have hfr : D.pt '' frontier V = frontier (D.pt '' V) := D.ptHomeomorph.image_frontier V
    rw [hfr] at hc
    have heq := internalEDist_eq_edist_of_le_infEDist hD (D.isOpen_image_pt hV)
      ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ hc
    rw [hs, hfr] at h
    exact absurd (heq ▸ h : Metric.infEDist (D.pt u) (frontier (D.pt '' V)) <
      edist (D.pt u) (D.pt v)) (not_lt.2 hc)

/-- the points of `V` within Euclidean distance `δ` of `∂V` -/
def nearFrontier (V : Set ℂ) (δ : ℝ) : Set ℂ := {y | y ∈ V ∧ Metric.infDist y (frontier V) < δ}

/-- **GM l. 1350** ("`D_h(u, ∂𝔸_{r/2,2r}(z))` is clearly determined by this internal metric"):
for `u` in a bounded open `V`, `D(u, ∂V) = sup_n inf {D(u, y; V) : y ∈ V, dist(y, ∂V) < 1/(n+1)}`
(own elementary argument: near-geodesics to `∂V` up to their first hitting time of `∂V`, and
uniform continuity of `D` near the compact `∂V`). -/
theorem setDist_frontier_eq_iSup (D : ContMetric) (hD : D.IsLength) {V : Set ℂ} (hV : IsOpen V)
    (hVb : Bornology.IsBounded V) {u : ℂ} (hu : u ∈ V) :
    setDist D {u} (frontier V) =
      ⨆ n : ℕ, ⨅ y ∈ nearFrontier V (1 / (n + 1)), D.internal V u y := by
  have hs : setDist D {u} (frontier V) = ⨅ x ∈ frontier V, ENNReal.ofReal (D.1 (u, x)) := by
    rw [setDist_eq_iInf]; simp only [mem_singleton_iff, iInf_iInf_eq_left]
  have hfrc : IsCompact (frontier V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hVb.closure.subset frontier_subset_closure)
  have huf : u ∉ frontier V := fun h => h.2 (by rwa [hV.interior_eq])
  have hne : (frontier V).Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at he
    rcases isClopen_iff.1 he with h | h
    · rw [h] at hu; exact hu
    · rw [h] at hVb; exact NormedSpace.unbounded_univ ℝ ℂ hVb
  rw [hs]
  refine le_antisymm ?_ (iSup_le fun n => le_iInf₂ fun x hx => ?_)
  · -- uniform continuity of `D` near `∂V`
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set K := Metric.cthickening 1 (frontier V)
    have hK : IsCompact K := hfrc.cthickening
    have huc := (hK.prod hK).uniformContinuousOn_of_continuous D.1.continuous.continuousOn
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc ε (by exact_mod_cast hε)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδ one_pos)
    refine le_trans ?_ (add_le_add (le_iSup _ n) le_rfl)
    rw [ENNReal.iInf_add]
    refine le_iInf fun y => ?_
    rw [ENNReal.iInf_add]
    refine le_iInf fun hy => ?_
    obtain ⟨x, hx, hxy⟩ := (Metric.infDist_lt_iff hne).1 hy.2
    have hxK : x ∈ K := Metric.self_subset_cthickening _ hx
    have hyK : y ∈ K := Metric.mem_cthickening_of_dist_le y x 1 _ hx
      (hxy.le.trans ((le_of_lt hn).trans (min_le_right _ _)))
    have hd := hδ' (x, y) ⟨hxK, hyK⟩ (x, x) ⟨hxK, hxK⟩ (by
      rw [Prod.dist_eq]
      simp only [dist_self]
      exact max_lt hδ (hxy.trans (hn.trans_le (min_le_left _ _))))
    rw [Real.dist_eq, D.2.self_eq_zero, sub_zero] at hd
    have hxy' : D.1 (y, x) < ε := by
      rw [D.2.symm]; exact (le_abs_self _).trans_lt hd
    calc ⨅ x ∈ frontier V, ENNReal.ofReal (D.1 (u, x)) ≤ ENNReal.ofReal (D.1 (u, x)) :=
          iInf₂_le x hx
      _ ≤ ENNReal.ofReal (D.1 (u, y) + D.1 (y, x)) :=
          ENNReal.ofReal_le_ofReal (D.2.triangle u y x)
      _ ≤ ENNReal.ofReal (D.1 (u, y)) + ENNReal.ofReal (D.1 (y, x)) := ENNReal.ofReal_add_le
      _ ≤ D.internal V u y + ε := by
          refine add_le_add ?_ ?_
          · rw [← ContMetric.edist_pt]; exact edist_le_internalEDist _ _ _
          · rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hxy'.le
  · -- near-geodesics to `x ∈ ∂V`, stopped before their first hitting time of `∂V`
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨P, a, b, hab, hPc, hPa, hPb, hlen⟩ :=
      isLengthSpace_iff_curves.1 hD (D.pt u) (D.pt x) ε (by exact_mod_cast hε)
    set Q : ℝ → ℂ := fun t => D.unpt (P t) with hQ
    have hQc : ContinuousOn Q (Icc a b) := D.continuous_unpt.comp_continuousOn hPc
    obtain ⟨s, hs, hQs, hbef⟩ := exists_first_hit hQc isClosed_frontier
      ⟨b, ⟨hab, le_rfl⟩, by show D.unpt (P b) ∈ _; rw [hPb]; exact hx⟩
    have hQa : Q a = u := by show D.unpt (P a) = u; rw [hPa]; rfl
    have has : a < s := by
      rcases hs.1.eq_or_lt with h | h
      · rw [← h, hQa] at hQs; exact absurd hQs huf
      · exact h
    have hinV : ∀ t ∈ Ico a s, Q t ∈ V := by
      have hpc : IsPreconnected (Q '' Ico a s) :=
        isPreconnected_Ico.image Q (hQc.mono (Ico_subset_Icc_self.trans
          (Icc_subset_Icc le_rfl hs.2)))
      have hsub := hpc.subset_left_of_subset_union (u := V) (v := (closure V)ᶜ) hV
        isClosed_closure.isOpen_compl
        (disjoint_compl_right_iff_subset.2 subset_closure) (by
          rintro _ ⟨t, ht, rfl⟩
          by_cases hQt : Q t ∈ V
          · exact Or.inl hQt
          · exact Or.inr fun hcl => hbef t ht ⟨hcl, by rwa [hV.interior_eq]⟩)
        (show (Q '' Ico a s ∩ V).Nonempty from ⟨u, ⟨a, ⟨le_rfl, has⟩, hQa⟩, hu⟩)
      exact fun t ht => hsub ⟨t, ht, rfl⟩
    have hg : ContinuousWithinAt (fun t => Metric.infDist (Q t) (frontier V)) (Ico a s) s :=
      ((Metric.continuous_infDist_pt _).comp_continuousOn hQc s hs).mono
        (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hs.2))
    have hg0 : Metric.infDist (Q s) (frontier V) = 0 := Metric.infDist_zero_of_mem hQs
    have hnb : (𝓝[Ico a s] s).NeBot := right_nhdsWithin_Ico_neBot has
    obtain ⟨t, htn, ht⟩ := ((hg.eventually (gt_mem_nhds (show
      Metric.infDist (Q s) (frontier V) < 1 / ((n : ℝ) + 1) by
        rw [hg0]; positivity))).and self_mem_nhdsWithin).exists
    have hmaps : MapsTo P (Icc a t) (D.pt '' V) := fun τ hτ =>
      ⟨Q τ, hinV τ ⟨hτ.1, hτ.2.trans_lt ht.2⟩, rfl⟩
    have htb : t ≤ b := ht.2.le.trans hs.2
    calc ⨅ y ∈ nearFrontier V (1 / (n + 1)), D.internal V u y ≤ D.internal V u (Q t) :=
          iInf₂_le (Q t) ⟨hinV t ht, htn⟩
      _ ≤ curveLength P a t := by
          have := internalEDist_le_curveLength ht.1 (hPc.mono (Icc_subset_Icc le_rfl htb)) hmaps
          rwa [hPa] at this
      _ ≤ curveLength P a b := eVariationOn.mono _ (Icc_subset_Icc le_rfl htb)
      _ ≤ edist (D.pt u) (D.pt x) + ENNReal.ofReal ε := hlen
      _ = ENNReal.ofReal (D.1 (u, x)) + ε := by
          rw [ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal]

/-- GM's reduced form of Lemma 3.7 (l. 1347): `𝖤_r(z)` is a.s. an event of
`σ(h|_{𝔸_{r/2,2r}(z)})` (for every whole-plane GFF `h`). -/
def L3_7loc : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∀ {α : ℝ}, 1 / 2 < α → α < 1 → ∀ A C' : ℝ, ∀ (z : ℂ) (r : ℝ), 0 < r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma h (annulus z (r / 2) (2 * r))) (h ⁻¹' goodAnnulus D D' α A C' r z)

/-- **GM Lemma 3.7 from its reduced form** (l. 1346–1347, Weyl scaling): apply `L3_7loc` to the
whole-plane GFF `h − h_{4r}(z)`. -/
theorem gm_L3_7_of_loc (H : L3_7loc) : L3_7 := by
  intro γ D D' c hPS α hα hα1 A C' z r hr Ω _ P _ h hh
  obtain ⟨-, -, hD, hD'⟩ := id hPS
  have hm : Measurable fun ω => -circleAvg (h ω) (4 * r) z :=
    ((measurable_circleAvg_left (4 * r) z).comp hh.measurable).neg
  have hX := hh.addConst hm
  obtain ⟨F, hF, hFae⟩ := H hPS hα hα1 A C' z r hr P _ hX
  refine ⟨F, hF, EventuallyEq.trans ?_ hFae⟩
  filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
    hD'.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh)] with ω hw hw'
  exact propext (mem_goodAnnulus_iff_of_scale (Real.exp_pos _) (hw _) (hw' _)).symm

end LQGMetric.GM
