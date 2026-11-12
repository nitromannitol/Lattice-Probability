/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8ProofF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofMeas
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofTight
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8: from a whole-plane GFF to a GFF plus a bounded continuous function (tightness)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:897–898): "If `h` is a whole-plane GFF
and `f` is a bounded continuous function, then the metrics `D_{h+f}^ε` and `D_h^ε` are
bi-Lipschitz equivalent, with Lipschitz constants `e^{±ξ‖f‖_∞}`. Hence the case of a whole-plane
GFF implies the case of a whole-plane GFF plus a continuous function."

Here: the tightness conjunct of Lemma 2.8 for `h = g + f` follows from that for `g`
(`lem2_8_tight_of_gff`), via the bi-Lipschitz bound and the tightness transfer
`isTightMeasureSet_of_le_mul` (random constant `e^{|ξ| ‖f‖_∞}`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- DFGPS's `𝔞_ε` is nonnegative (copy of `GM.aEpsDF_nonneg`, avoiding a heavy import) -/
lemma aEpsDF_nonneg_sq (ξ ε : ℝ) : 0 ≤ aEpsDF ξ ε := by
  refine Real.sInf_nonneg fun m hm => ?_
  by_contra hneg
  have he : {x | lfppCrossIn ξ ε x ≤ m} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx =>
      hneg (le_trans ENNReal.toReal_nonneg (show lfppCrossIn ξ ε x ≤ m from hx))
  have hm' : (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {x | lfppCrossIn ξ ε x ≤ m} := hm
  rw [he, measure_empty] at hm'
  exact absurd hm' (not_le.2 inv_two_pos')

/-- `heatMollify` is additive on `g + f` once the limit for `g` exists (copy of
`DFGPS.heatMollify_add_ofCont` of `L2_1Bdd`, a file under active edit by another task). -/
lemma heatMollify_add_ofCont' (g : DistC) (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) {L : ℝ}
    (hg : Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) :
    heatMollify ε (g + ofCont f) z = heatMollify ε g z + heatMollify ε (ofCont f) z := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have hf := tendsto_ofCont_heatTrunc f _ hs z (integrable_heatKernel_mul_of_bdd f M hM _ hs z)
  have hsum : Tendsto (fun n : ℕ => (g + ofCont f) (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (L + ∫ w, heatKernel (ε ^ 2 / 2) z w * f w)) := by
    simpa only [ContinuousLinearMap.add_apply] using hg.add hf
  unfold heatMollify
  rw [hsum.limUnder_eq, hg.limUnder_eq, hf.limUnder_eq]

/-- a measurable bound for `sup |f|` -/
def supAbs (f : C(ℂ, ℝ)) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal |f (TopologicalSpace.denseSeq ℂ n)|).toReal

theorem measurable_supAbs {Ω : Type*} [MeasurableSpace Ω] {f : Ω → C(ℂ, ℝ)} (hf : Measurable f) :
    Measurable fun ω => supAbs (f ω) :=
  ENNReal.measurable_toReal.comp (Measurable.iSup fun n =>
    (continuous_abs.measurable.comp ((continuous_eval_const _).measurable.comp hf)).ennreal_ofReal)

theorem abs_le_supAbs {f : C(ℂ, ℝ)} {M : ℝ} (hM : ∀ z, |f z| ≤ M) (z : ℂ) :
    |f z| ≤ supAbs f := by
  have hfin : (⨆ n : ℕ, ENNReal.ofReal |f (TopologicalSpace.denseSeq ℂ n)|) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun n => ENNReal.ofReal_le_ofReal (hM _))
  have hseq : ∀ n, |f (TopologicalSpace.denseSeq ℂ n)| ≤ supAbs f := fun n => by
    unfold supAbs
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
    exact le_iSup (fun n : ℕ => ENNReal.ofReal |f (TopologicalSpace.denseSeq ℂ n)|) n
  exact (TopologicalSpace.denseRange_denseSeq ℂ).induction_on z
    (isClosed_le (continuous_abs.comp f.continuous) continuous_const) hseq

/-- **DFGPS T:897–898, tightness part**: the tightness conjunct of Lemma 2.8 for a whole-plane
GFF plus a bounded continuous function follows from the whole-plane GFF case. -/
theorem lem2_8_tight_of_gff {ξ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P)
    (hG : ∀ g : Ω → DistC, IsWholePlaneGFF g P → IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => lfppSqC ξ ε (g ω) (closedSq a s)}) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => lfppSqC ξ ε (h ω) (closedSq a s)} := by
  obtain ⟨hhm, f, hf, hfb, hg⟩ := hh
  set S := closedSq a s
  set g : Ω → DistC := fun ω => h ω - ofCont (f ω)
  have : CompactSpace S := isCompact_iff_compactSpace.1 (isCompact_closedSq a hs.le)
  have : ConnectedSpace S := isConnected_iff_connectedSpace.1
    ((convex_closedSq a s).isConnected ⟨a, by simp [closedSq]; exact hs.le⟩)
  have hgm : Measurable g := hg.measurable
  have hhc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, Continuous (heatMollify ε (h ω)) := fun ε hε =>
    (IsGFFPlusBddCont.ae_tendstoLocallyUniformly_heatMollify ⟨hhm, f, hf, hfb, hg⟩ ε
      hε.1.ne').mono fun ω hω => hω.2
  have hgc : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P,
      TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => g ω (heatTrunc (ε ^ 2 / 2) z n))
        (heatMollify ε (g ω)) atTop ∧ Continuous (heatMollify ε (g ω)) := fun ε hε =>
    hg.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'
  set c : ℝ → ℝ := fun ε => (aEpsDF ξ ε)⁻¹
  have hc0 : ∀ ε, 0 ≤ c ε := fun ε => inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
  refine isTightMeasureSet_of_le_mul (Ioo (0 : ℝ) 1)
    (fun ε ω => lfppSqC ξ ε (g ω) S) (fun ε ω => lfppSqC ξ ε (h ω) S)
    (fun ω => Real.exp (|ξ| * supAbs (f ω)))
    (Real.measurable_exp.comp ((measurable_supAbs hf).const_mul _)) (hG g hg)
    (fun ε hε => aemeasurable_lfppSqC hgm ((hgc ε hε).mono fun ω hω => hω.2) hs)
    (fun ε hε => aemeasurable_lfppSqC hhm (hhc ε hε) hs) ?_ ?_ ?_
  · intro ε hε
    filter_upwards [hgc ε hε] with ω hω x
    rw [lfppSqC_apply_of_continuous hω.2 hs, lfppDOn_self (convex_closedSq a s) x.2,
      ENNReal.toReal_zero, mul_zero]
  · intro ε hε
    filter_upwards [hhc ε hε] with ω hω
    obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hω (convex_closedSq a s)
      (closedSq_subset_closedBall a hs.le)
    have hfin : ∀ x y : S, lfppDOn ξ (heatMollify ε (h ω)) S x y ≠ ⊤ := fun x y =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x x.2 y y.2)
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [lfppSqC_apply_of_continuous hω hs, lfppDOn_self (convex_closedSq a s) x.2,
        ENNReal.toReal_zero, mul_zero]
    · rw [lfppSqC_apply_of_continuous hω hs (x, z), lfppSqC_apply_of_continuous hω hs (x, y),
        lfppSqC_apply_of_continuous hω hs (y, z)]
      rw [← mul_add, ← ENNReal.toReal_add (hfin x y) (hfin y z)]
      exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hfin x y, hfin y z⟩) (lfppDOn_triangle _ _ _)) (hc0 ε)
  · intro ε hε
    filter_upwards [hgc ε hε, hhc ε hε] with ω hωg hωh p
    obtain ⟨M, hM⟩ := hfb ω
    have hMs := abs_le_supAbs hM
    have hdiff : ∀ x ∈ S, |heatMollify ε (h ω) x - heatMollify ε (g ω) x| ≤ supAbs (f ω) := by
      intro x _
      have hadd := heatMollify_add_ofCont' (g ω) (f ω) M hM hε.1 x
        ((tendstoLocallyUniformlyOn_univ.2 hωg.1).tendsto_at (mem_univ x))
      have e : g ω + ofCont (f ω) = h ω := sub_add_cancel _ _
      rw [e] at hadd
      rw [hadd, add_sub_cancel_left]
      exact abs_heatMollify_ofCont_le (f ω) hMs hε.1.ne' x
    obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hωg.2 (convex_closedSq a s)
      (closedSq_subset_closedBall a hs.le)
    have hle := lfppDOn_toReal_le_of_abs_sub_le (ξ := ξ) hdiff
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB p.1 p.1.2 p.2 p.2.2))
    rw [lfppSqC_apply_of_continuous hωh hs p, lfppSqC_apply_of_continuous hωg.2 hs p]
    calc c ε * (lfppDOn ξ (heatMollify ε (h ω)) S p.1 p.2).toReal
        ≤ c ε * (Real.exp (|ξ| * supAbs (f ω)) *
            (lfppDOn ξ (heatMollify ε (g ω)) S p.1 p.2).toReal) :=
          mul_le_mul_of_nonneg_left hle (hc0 ε)
      _ = _ := by ring

end LQGMetric.DFGPS
