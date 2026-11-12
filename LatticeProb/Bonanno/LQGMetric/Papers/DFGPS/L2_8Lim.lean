/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8Lim at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8LimMid
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, third conjunct: subsequential limits are length metrics, given positivity

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:875, T:887–889): "any subsequential
limit of these laws is supported on length metrics which induce the Euclidean topology on `S`",
obtained by "combining … with Lemma 2.7" (`lem-bbi` = BBI Exercise 2.4.19).

We split the conclusion as BBI's proof does (BBI Lemma 2.4.10, Theorem 2.4.16(2), Corollary
2.4.17): the approximating metrics `𝔞_ε⁻¹ D_h^ε(·,·;S)` are continuous pseudo-metrics with
`ε`-midpoints (`lfppDOn_approxMid`), hence lie in the closed set `lenPmetSet S` of continuous
symmetric pseudo-metrics with exact midpoints; by the portmanteau theorem (mathlib
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`) every subsequential limit law is
supported on `lenPmetSet S`; a continuous member of `lenPmetSet S` that is positive off the
diagonal is a length metric (Menger, BBI Theorem 2.4.16(2), `isLengthSpace_of_hasApproxMidpoints`;
`(S, d)` is compact, hence complete). The portmanteau formulation replaces the Skorokhod-coupling
reading of "combining with Lemma 2.7" (same content; proposed DEVIATIONS entry DF-L28-LIM).

* `ae_mem_lenPmetSet`: every subsequential limit law is supported on `lenPmetSet`;
* `lem2_8_lim_of_pos`: the third conjunct of `Lem2_8`, given a.s. positivity off the diagonal of
  the limit (positivity is the remaining input: DDDF Theorem 1 bi-Hölder limits via DDDF Prop 29,
  T:880–889).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry LFPP

/-- continuous symmetric pseudo-metrics with exact midpoints on `X` (a closed set) -/
def lenPmetSet (X : Type*) [TopologicalSpace X] : Set C(X × X, ℝ) :=
  pmetSet X ∩ symmSet X ∩ midSet X

theorem isClosed_lenPmetSet (X : Type*) [MetricSpace X] [CompactSpace X] :
    IsClosed (lenPmetSet X) :=
  ((isClosed_pmetSet X).inter (isClosed_symmSet X)).inter (isClosed_midSet X)

/-- the rescaled internal LFPP metric on a square lies in `lenPmetSet` (continuous `h*_ε`) -/
theorem lfppSqC_mem_lenPmetSet {ξ ε : ℝ} {g : DistC} (hc : Continuous (heatMollify ε g))
    {a : ℂ} {s : ℝ} (hs : 0 < s) : lfppSqC ξ ε g (closedSq a s) ∈ lenPmetSet (closedSq a s) := by
  have : CompactSpace (closedSq a s) :=
    isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  set c := (aEpsDF ξ ε)⁻¹ with hcdef
  have hc0 : 0 ≤ c := inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
  have hap := lfppSqC_apply_of_continuous (ξ := ξ) hc (a := a) hs
  have hfin : ∀ x y : closedSq a s,
      lfppDOn ξ (heatMollify ε g) (closedSq a s) x y ≠ ⊤ := by
    obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hc (convex_closedSq a s)
      (closedSq_subset_closedBall a hs.le)
    exact fun x y => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x x.2 y y.2)
  refine ⟨⟨⟨fun x => ?_, fun x y z => ?_⟩, fun x y => ?_⟩,
    mem_midSet_of_approx _ fun x y ε' hε' => ?_⟩
  · rw [hap]; simp [lfppDOn_self (convex_closedSq a s) x.2]
  · simp only [hap]
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [← ENNReal.toReal_add (hfin x y) (hfin y z)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩)
      (lfppDOn_triangle _ _ _)
  · simp only [hap]; rw [lfppDOn_comm]
  · simp only [hap]
    rcases hc0.eq_or_lt with h0 | h0
    · refine ⟨x, ?_, ?_⟩ <;> rw [← hcdef, ← h0] <;> simp <;> linarith
    · obtain ⟨z, hz, h1, h2⟩ := lfppDOn_approxMid (ξ := ξ) hc (convex_closedSq a s)
        (closedSq_subset_closedBall a hs.le) x.2 y.2 (div_pos hε' h0)
      have key : c * ((lfppDOn ξ (heatMollify ε g) (closedSq a s) x y).toReal / 2 + ε' / c) =
          c * (lfppDOn ξ (heatMollify ε g) (closedSq a s) x y).toReal / 2 + ε' := by
        field_simp
      refine ⟨⟨z, hz⟩, ?_, ?_⟩
      · exact (mul_le_mul_of_nonneg_left h1 hc0).trans key.le
      · exact (mul_le_mul_of_nonneg_left h2 hc0).trans key.le

/-- **Subsequential limit laws are supported on `lenPmetSet`** (portmanteau, closed set). -/
theorem ae_mem_lenPmetSet {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closedSq a s))
    (hlim : Tendsto ν atTop (𝓝 μ)) :
    ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), d ∈ lenPmetSet (closedSq a s) := by
  have : CompactSpace (closedSq a s) :=
    isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  have hF := isClosed_lenPmetSet (closedSq a s)
  have hνF : ∀ n, (ν n : Measure _) (lenPmetSet (closedSq a s)) = 1 := by
    intro n
    obtain ⟨hεn, hνn⟩ := hν n
    have hc := hh.ae_tendstoLocallyUniformly_heatMollify (εn n) hεn.1.ne'
    rw [hνn, Measure.map_apply_of_aemeasurable
      (aemeasurable_lfppSqC hh.1 (hc.mono fun ω hω => hω.2) hs) hF.measurableSet]
    have hae : ∀ᵐ ω ∂P, ω ∈ (fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closedSq a s)) ⁻¹'
        lenPmetSet (closedSq a s) := hc.mono fun ω hω => lfppSqC_mem_lenPmetSet hω.2 hs
    exact (measure_congr (eventuallyEqSet_univ.2 hae)).trans measure_univ
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simp only [hνF, limsup_const] at hle
  have h1 : (μ : Measure C(closedSq a s × closedSq a s, ℝ)) (lenPmetSet (closedSq a s)) =
      (μ : Measure C(closedSq a s × closedSq a s, ℝ)) univ := by
    rw [measure_univ]; exact le_antisymm prob_le_one hle
  exact (ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).2 h1

/-- a continuous symmetric pseudo-metric with midpoints, positive off the diagonal, on a compact
metric space is a length metric (Menger, BBI Theorem 2.4.16(2)) -/
theorem isLengthMetric_of_mem_lenPmetSet {X : Type*} [MetricSpace X] [CompactSpace X]
    {d : C(X × X, ℝ)} (hd : d ∈ lenPmetSet X) (hpos : ∀ x y, x ≠ y → 0 < d (x, y)) :
    ∃ hm : IsMetricFun (⇑d), IsLengthMetricFun (⇑d) hm := by
  obtain ⟨⟨⟨h0, htri⟩, hsymm⟩, hmid⟩ := hd
  have hm : IsMetricFun (⇑d) :=
    ⟨h0, fun x y hxy => by_contra fun hne => (hpos x y hne).ne' hxy, hsymm, htri⟩
  have := compactSpace_metricFunSpace hm d.continuous
  refine ⟨hm, isLengthSpace_of_hasApproxMidpoints fun x y ε hε => ?_⟩
  obtain ⟨z, h1, h2⟩ := hmid x y
  refine ⟨z, ?_, ?_⟩
  · change d (x, z) ≤ d (x, y) / 2 + ε; linarith
  · change d (y, z) ≤ d (x, y) / 2 + ε; exact (hsymm y z).le.trans (by linarith)

/-- **Third conjunct of DFGPS Lemma 2.8, given positivity of the limit** (T:875, T:887–889):
every subsequential limit law is supported on length metrics (continuous on `S × S`, hence
inducing the Euclidean topology), provided it is supported on functions positive off the
diagonal. -/
theorem lem2_8_lim_of_pos {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusBddCont h P)
    (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (μ : ProbabilityMeasure C(closedSq a s × closedSq a s, ℝ))
    (hν : ∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
      (ν n : Measure _) = P.map fun ω => lfppSqC (xiGamma γ) (εn n) (h ω) (closedSq a s))
    (hlim : Tendsto ν atTop (𝓝 μ))
    (hpos : ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)),
      ∀ x y, x ≠ y → 0 < d (x, y)) :
    ∀ᵐ d ∂(μ : Measure C(closedSq a s × closedSq a s, ℝ)), IsSqLengthMetric d := by
  have : CompactSpace (closedSq a s) :=
    isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  filter_upwards [ae_mem_lenPmetSet hs hh εn ν μ hν hlim, hpos] with d hd hp
  exact isLengthMetric_of_mem_lenPmetSet hd hp

end LQGMetric.DFGPS
