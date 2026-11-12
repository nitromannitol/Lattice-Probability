/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinCmp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinSupMain
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1RadialMain
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.LFPP.ChainInf
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.MeasureTheory.Integral.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8: per-`ε` comparison of `h*_ε` with the zero-boundary field (T:883–887)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:883–887) compares `D_h^ε` with
`D_{h̊}^ε` through the localized metrics: `D_h^ε ≍ D̂_h^ε` (Lemma 2.1), `D̂_h^ε ≍ D̂_{h̊}^ε` with
random `ε`-independent constants (eqn-localized-property), `D̂_{h̊}^ε ≍ D_{h̊}^ε` (Lemma 2.1 for
`h̊`). DDDF's versions `Y δ` are chosen per `δ`, so (handoff P2-DFB34d) we need these comparisons
as per-`ε` statements with probability bounds uniform in `ε`:

* `prob_lt_of_ae_eventually`: a.s. eventual absence from measurable events gives uniform small
  probabilities (dominated convergence, `tendsto_measure_of_ae_tendsto_indicator`);
* `gff_heatLoc_prob`: Lemma 2.1 for the whole-plane GFF in this form (measurable events through
  the countable dense set `gaussRat` and continuity in `z`);
* `gff_zbLoc_prob`: `sup_{ε ≤ 1/4, x ∈ [0,1]²} |ĥ*_ε(x) − h̊̂*_ε(x)|` is tight (the random constant
  `|c| + sup_K |𝔥|` of `abs_locMollify_sub_le`; measurable events through rational `ε`, `gaussRat`
  and the joint continuity `lem2_1_cont`).

The measurability bookkeeping is own (the paper works with a.s. statements); proposed
DEVIATIONS entry DEV-DFGPS-L28-CMP.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open LFPP HeatSq Blueprint

/-- **From a.s. eventual absence to uniform small probabilities.** -/
lemma prob_lt_of_ae_eventually {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {B : ℝ → Set Ω} (hB : ∀ ε, MeasurableSet (B ε))
    (h : ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ω ∉ B ε) :
    ∀ ζ > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → P (B ε) ≤ ENNReal.ofReal ζ := by
  intro ζ hζ
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝[>] (0 : ℝ))
    MeasurableSet.empty hB (h.mono fun ω hω => hω.mono fun ε hε => by simp [hε])
  rw [measure_empty] at ht
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hζ))
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact ⟨ε₁, hε₁, fun ε h0 h1 => (hsub ⟨h0, h1⟩ : P (B ε) < _).le⟩

lemma isGFFPlusBddCont_of_wp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → DistC}
    (hg : IsWholePlaneGFF g P) : IsGFFPlusBddCont g P := by
  refine ⟨hg.measurable, fun _ => 0, measurable_const, fun _ => ⟨0, by simp⟩, ?_⟩
  simpa [GM.ofCont_zero_eq] using hg

/-- **Lemma 2.1 for the whole-plane GFF, per `ε`** (T:688–699 in the form needed at T:888). -/
theorem gff_heatLoc_prob {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P) :
    ∀ δ > 0, ∀ ζ > 0, ∃ ε₁ > 0, ∀ ε (hε : 0 < ε), ε < ε₁ →
      P {ω | ∃ z ∈ closedUnitSquare,
        δ < |heatMollify ε (g ω) z - locMollify ε hε (g ω) z|} ≤ ENNReal.ofReal ζ := by
  intro δ hδ ζ hζ
  set D := gaussRat ∩ closedUnitSquare
  have hDc : D.Countable := gaussRat_countable.mono inter_subset_left
  set B : ℝ → Set Ω := fun ε => if hε : 0 < ε then
    ⋃ q ∈ D, {ω | δ < |heatMollify ε (g ω) q - locMollify ε hε (g ω) q|} else ∅
  have hBm : ∀ ε, MeasurableSet (B ε) := by
    intro ε
    by_cases hε : 0 < ε
    · simp only [B, dif_pos hε]
      refine MeasurableSet.biUnion hDc fun q _ => measurableSet_lt measurable_const ?_
      exact continuous_abs.measurable.comp (((measurable_heatMollify_left ε q).comp
        hg.measurable).sub ((measurable_locMollify ε hε).comp
          (hg.measurable.prodMk measurable_const)))
    · simp only [B, dif_neg hε]; exact MeasurableSet.empty
  have hU : Bornology.IsBounded closedUnitSquare :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset (by
      intro z hz; obtain ⟨h1, h2, h3, h4⟩ := hz
      rw [mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith)
  have hL := lem2_1_uncond (isGFFPlusBddCont_of_wp hg) hU 0
  have hae : ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ω ∉ B ε := by
    filter_upwards [hL] with ω hω
    filter_upwards [hω.2.1 δ hδ] with ε hε
    by_cases h0 : 0 < ε
    · simp only [B, dif_pos h0, mem_iUnion, mem_setOf_eq, not_exists, not_lt]
      intro q hq
      exact hε h0 q (subset_closure hq.2)
    · simp [B, dif_neg h0]
  obtain ⟨ε₁, hε₁, hP⟩ := prob_lt_of_ae_eventually hBm hae ζ hζ
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  have hcont := (isGFFPlusBddCont_of_wp hg).ae_tendstoLocallyUniformly_heatMollify ε hε.ne'
  set N := {ω | ¬ Continuous (heatMollify ε (g ω))}
  have hN : P N = 0 := measure_eq_zero_iff_ae_notMem.2 (hcont.mono fun ω hω h => h hω.2)
  have hsub : {ω | ∃ z ∈ closedUnitSquare,
      δ < |heatMollify ε (g ω) z - locMollify ε hε (g ω) z|} ⊆ B ε ∪ N := by
    rintro ω ⟨z, hz, hlt⟩
    by_cases hc : Continuous (heatMollify ε (g ω))
    · left
      simp only [B, dif_pos hε, mem_iUnion, mem_setOf_eq]
      have hF : Continuous fun y => |heatMollify ε (g ω) y - locMollify ε hε (g ω) y| :=
        (hc.sub (continuous_locMollify ε hε (g ω))).abs
      have hO : IsOpen {y | δ < |heatMollify ε (g ω) y - locMollify ε hε (g ω) y|} :=
        isOpen_lt continuous_const hF
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO z hlt
      obtain ⟨q, hq, hqz⟩ := gaussRat_square_dense hz hρ
      exact ⟨q, hq, hball (by rw [mem_ball, dist_eq_norm]; exact hqz)⟩
    · right; exact hc
  calc P _ ≤ P (B ε ∪ N) := measure_mono hsub
    _ ≤ P (B ε) + P N := measure_union_le _ _
    _ = P (B ε) := by rw [hN, add_zero]
    _ ≤ _ := hP ε hε hεε

/-- the compact `[-1/2, 3/2]²` inside `(-1,2)²` -/
lemma exists_bound_harm_sq {f : ℂ → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f (sqOpen (-1) 3)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε (_ : 0 < ε), ε ≤ 1 / 4 → ∀ x ∈ closedUnitSquare,
      closedBall x (Real.sqrt ε) ⊆
        {y : ℂ | -1 / 2 ≤ y.re ∧ y.re ≤ 3 / 2 ∧ -1 / 2 ≤ y.im ∧ y.im ≤ 3 / 2} ∧
      ∀ y ∈ {y : ℂ | -1 / 2 ≤ y.re ∧ y.re ≤ 3 / 2 ∧ -1 / 2 ≤ y.im ∧ y.im ≤ 3 / 2}, |f y| ≤ B := by
  set K : Set ℂ := {y : ℂ | -1 / 2 ≤ y.re ∧ y.re ≤ 3 / 2 ∧ -1 / 2 ≤ y.im ∧ y.im ≤ 3 / 2}
  have hKV : K ⊆ sqOpen (-1) 3 := fun y ⟨h1, h2, h3, h4⟩ =>
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hKc : IsCompact K := by
    have e : K = (Complex.re ⁻¹' Icc (-1 / 2) (3 / 2)) ∩ (Complex.im ⁻¹' Icc (-1 / 2) (3 / 2)) := by
      ext y; simp only [K, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc]; tauto
    refine Metric.isCompact_of_isClosed_isBounded ?_ ((isBounded_sqOpen (-1) 3).subset hKV)
    rw [e]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have hgc : ContinuousOn f K := fun y hy => ((hf y (hKV hy)).1.continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hgc
  refine ⟨max B 0, le_max_right _ _, fun ε hε hε4 x hx => ⟨?_, fun y hy =>
    (by simpa [Real.norm_eq_abs] using hB y hy : |f y| ≤ B).trans (le_max_left _ _)⟩⟩
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hs : Real.sqrt ε ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hε4
  have hy' := mem_closedBall.1 hy
  rw [dist_eq_norm] at hy'
  have hre := (Complex.abs_re_le_norm (y - x)).trans (hy'.trans hs)
  have him := (Complex.abs_im_le_norm (y - x)).trans (hy'.trans hs)
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-- **The localized fields of `h` and `h̊` are uniformly close in probability** (T:886–887 in
per-`ε` form, `ε ≤ 1/4`). -/
theorem gff_zbLoc_prob {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g hh hz : Ω → DistC} {c : Ω → ℝ} (hg : IsWholePlaneGFF g P)
    (hsum : ∀ ω, addConst (g ω) (c ω) = hh ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f (sqOpen (-1) 3) ∧
      ∀ φ : TestOn (sqOpens (-1) 3), restrictTo _ (hh ω) φ = ∫ x, f x * φ x)
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hXm : ∀ ρ, Measurable (Xh ρ))
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ) :
    ∀ ζ > 0, ∃ M : ℝ, ∀ ε (hε : 0 < ε), ε ≤ 1 / 4 →
      P {ω | ∃ x ∈ closedUnitSquare,
        M < |locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x|} ≤ ENNReal.ofReal ζ := by
  intro ζ hζ
  set D := gaussRat ∩ closedUnitSquare
  have hDc : D.Countable := gaussRat_countable.mono inter_subset_left
  -- a.e.-measurability of the differences at fixed `(ε, x)`
  have hFm : ∀ ε (hε : 0 < ε), ε ≤ 1 / 4 → ∀ x ∈ closedUnitSquare, AEMeasurable
      (fun ω => |locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x|) P := by
    intro ε hε hε4 x hx
    have hsq : Real.sqrt ε < 1 := by
      rw [Real.sqrt_lt' one_pos]; nlinarith
    have hsupp : tsupport (locTest ε hε x : ℂ → ℝ) ⊆ (sqOpens (-1) 3 : Set ℂ) :=
      (tsupport_locTest_subset ε hε x).trans (closedBall_subset_sqOpen hx hsq)
    have h1 : AEMeasurable (fun ω => locMollify ε hε (hz ω) x) P :=
      (hXm (testOnOf _ (locTest ε hε x) hsupp).toBddOn).aemeasurable.congr
        ((hlink (testOnOf _ (locTest ε hε x) hsupp)).mono
          fun ω hω => hω.trans (restrictTo_testOnOf _ (hz ω) _ hsupp))
    have h2 : Measurable (fun ω => locMollify ε hε (g ω) x) :=
      (measurable_locMollify ε hε).comp (hg.measurable.prodMk measurable_const)
    exact continuous_abs.measurable.comp_aemeasurable (h2.aemeasurable.sub h1)
  set U : ℕ → Set Ω := fun M => ⋃ r : ℚ, ⋃ q ∈ D, {ω | ∃ hr : 0 < (r : ℝ), (r : ℝ) ≤ 1 / 4 ∧
    (M : ℝ) < |locMollify r hr (g ω) q - locMollify r hr (hz ω) q|}
  have hUm : ∀ M, NullMeasurableSet (U M) P := by
    intro M
    refine NullMeasurableSet.iUnion fun r => NullMeasurableSet.biUnion hDc fun q hq => ?_
    by_cases hr : 0 < (r : ℝ) ∧ (r : ℝ) ≤ 1 / 4
    · have e : {ω | ∃ hr : 0 < (r : ℝ), (r : ℝ) ≤ 1 / 4 ∧
          (M : ℝ) < |locMollify r hr (g ω) q - locMollify r hr (hz ω) q|} =
          {ω | (M : ℝ) < |locMollify r hr.1 (g ω) q - locMollify r hr.1 (hz ω) q|} := by
        ext ω; exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hr.1, hr.2, h⟩⟩
      rw [e]
      exact nullMeasurableSet_lt aemeasurable_const (hFm r hr.1 hr.2 q hq.2)
    · have e : {ω | ∃ hr : 0 < (r : ℝ), (r : ℝ) ≤ 1 / 4 ∧
          (M : ℝ) < |locMollify r hr (g ω) q - locMollify r hr (hz ω) q|} = ∅ := by
        ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩; exact hr ⟨h1, h2⟩
      rw [e]; exact MeasurableSet.empty.nullMeasurableSet
  have hUa : Antitone U := by
    intro M M' hMM' ω hω
    simp only [U, mem_iUnion] at hω ⊢
    obtain ⟨r, q, hq, hr, hr4, hlt⟩ := hω
    exact ⟨r, q, hq, hr, hr4, lt_of_le_of_lt (by exact_mod_cast hMM') hlt⟩
  have hU0 : P (⋂ M, U M) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hharm)
    intro ω hω
    simp only [mem_ofPred_eq]
    intro hgood
    obtain ⟨f, hfh, hf⟩ := hgood
    obtain ⟨B, hB0, hB⟩ := exists_bound_harm_sq hfh
    obtain ⟨M, hM⟩ := exists_nat_gt (|c ω| + B)
    have := mem_iInter.1 hω M
    simp only [U, mem_iUnion] at this
    obtain ⟨r, q, hq, hr, hr4, hlt⟩ := this
    obtain ⟨hball, hfB⟩ := hB r hr hr4 q hq.2
    have hb := abs_locMollify_sub_le (V := sqOpens (-1) 3) (hsum ω) hf hB0 hfB
      (fun y ⟨h1, h2, h3, h4⟩ => ⟨by linarith, by linarith, by linarith, by linarith⟩) hr hball
    linarith
  have ht := tendsto_measure_iInter_atTop hUm hUa ⟨0, measure_ne_top _ _⟩
  rw [hU0] at ht
  obtain ⟨M, hM⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hζ))).exists
  refine ⟨M, fun ε hε hε4 => ?_⟩
  refine (measure_mono ?_).trans (hM : P (U M) < _).le
  rintro ω ⟨x, hx, hlt⟩
  set F : ℝ × ℂ → ℝ := fun p => (if hp : 0 < p.1 then locMollify p.1 hp (g ω) p.2 else 0) -
    (if hp : 0 < p.1 then locMollify p.1 hp (hz ω) p.2 else 0)
  have hFc : ContinuousOn (fun p => |F p|) (Ioi 0 ×ˢ univ) :=
    continuous_abs.comp_continuousOn ((lem2_1_cont (g ω)).sub (lem2_1_cont (hz ω)))
  have hO := hFc.isOpen_inter_preimage (isOpen_Ioi.prod isOpen_univ) (isOpen_Ioi (a := (M : ℝ)))
  have hmem : ((ε, x) : ℝ × ℂ) ∈ (Ioi 0 ×ˢ univ) ∩ (fun p => |F p|) ⁻¹' Ioi (M : ℝ) := by
    refine ⟨⟨hε, mem_univ _⟩, ?_⟩
    simp only [mem_preimage, mem_Ioi, F, dif_pos hε]
    exact hlt
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max 0 (ε - ρ) < ε from
    max_lt hε (by linarith))
  have hr0 : 0 < (r : ℝ) := lt_of_le_of_lt (le_max_left _ _) hr1
  obtain ⟨q, hq, hqx⟩ := gaussRat_square_dense hx hρ
  have hin : ((r : ℝ), q) ∈ ball ((ε, x) : ℝ × ℂ) ρ := by
    rw [mem_ball, Prod.dist_eq]
    refine max_lt ?_ (by rw [dist_eq_norm]; exact hqx)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right 0 (ε - ρ)]
  have h2 := (hball hin).2
  simp only [mem_preimage, mem_Ioi, F, dif_pos hr0] at h2
  simp only [U, mem_iUnion]
  exact ⟨r, q, hq, hr0, by linarith, h2⟩

/-- **Per-`ε` comparison of `h*_ε` with DDDF's zero-boundary versions** (T:883–887): for every
`ζ > 0` there are `M` and `ε₁ > 0` such that for `ε < ε₁`, with probability `≥ 1 − ζ`,
`sup_{[0,1]²} |h*_ε − Y_{ε²}| ≤ M`. -/
theorem gff_zb_field_prob {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g hh hz : Ω → DistC} {c : Ω → ℝ} (hg : IsWholePlaneGFF g P)
    (hsum : ∀ ω, addConst (g ω) (c ω) = hh ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f (sqOpen (-1) 3) ∧
      ∀ φ : TestOn (sqOpens (-1) 3), restrictTo _ (hh ω) φ = ∫ x, f x * φ x)
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {Y : ℝ → ℂ → Ω → ℝ}
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P) :
    ∀ ζ > 0, ∃ M : ℝ, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      P {ω | ∃ x ∈ closedUnitSquare, M < |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|} ≤
        ENNReal.ofReal ζ := by
  intro ζ hζ
  have hζ3 : 0 < ζ / 3 := by positivity
  obtain ⟨M₂, hM₂⟩ := gff_zbLoc_prob hg hsum hharm hX.measurable hlink (ζ / 3) hζ3
  obtain ⟨εa, hεa, ha⟩ := gff_heatLoc_prob hg 1 one_pos (ζ / 3) hζ3
  obtain ⟨εb, hεb, hb⟩ := zbLoc_sup_tail hX hlink hY 1 one_pos (ζ / 3) hζ3
  refine ⟨M₂ + 2, min (min εa εb) (1 / 4), by positivity, fun ε hε hεε => ?_⟩
  have h1 : ε < εa := lt_of_lt_of_le hεε ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε < εb := lt_of_lt_of_le hεε ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε ≤ 1 / 4 := (lt_of_lt_of_le hεε (min_le_right _ _)).le
  set E1 := {ω | ∃ z ∈ closedUnitSquare,
    1 < |heatMollify ε (g ω) z - locMollify ε hε (g ω) z|}
  set E2 := {ω | ∃ x ∈ closedUnitSquare,
    M₂ < |locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x|}
  set E3 := {ω | ∃ x ∈ closedUnitSquare, 1 < |Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x|}
  have hsub : {ω | ∃ x ∈ closedUnitSquare, M₂ + 2 < |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|} ⊆
      E1 ∪ E2 ∪ E3 := by
    rintro ω ⟨x, hx, hlt⟩
    by_contra hn
    simp only [E1, E2, E3, mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hn
    obtain ⟨⟨n1, n2⟩, n3⟩ := hn
    have a1 := n1 x hx
    have a2 := n2 x hx
    have a3 := n3 x hx
    have : |heatMollify ε (g ω) x - Y (ε ^ 2) x ω| ≤ M₂ + 2 := by
      calc |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|
          = |(heatMollify ε (g ω) x - locMollify ε hε (g ω) x) +
              (locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x) -
              (Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x)| := by ring_nf
        _ ≤ |(heatMollify ε (g ω) x - locMollify ε hε (g ω) x) +
              (locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x)| +
              |Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x| := abs_sub _ _
        _ ≤ (|heatMollify ε (g ω) x - locMollify ε hε (g ω) x| +
              |locMollify ε hε (g ω) x - locMollify ε hε (hz ω) x|) +
              |Y (ε ^ 2) x ω - locMollify ε hε (hz ω) x| := by gcongr; exact abs_add_le _ _
        _ ≤ M₂ + 2 := by linarith
    linarith
  calc P _ ≤ P (E1 ∪ E2 ∪ E3) := measure_mono hsub
    _ ≤ P E1 + P E2 + P E3 := (measure_union_le _ _).trans (add_le_add
          (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (ζ / 3) + ENNReal.ofReal (ζ / 3) + ENNReal.ofReal (ζ / 3) :=
        add_le_add (add_le_add (ha ε hε h1) (hM₂ ε hε h3)) (hb ε hε h2)
    _ = ENNReal.ofReal ζ := by
        rw [← ENNReal.ofReal_add hζ3.le hζ3.le, ← ENNReal.ofReal_add (by positivity) hζ3.le]
        congr 1; ring

/-- the corresponding bi-Lipschitz bound of the internal LFPP metrics on `[0,1]²` -/
lemma lfppDOn_biLip_of_sup_le {ξ M : ℝ} {φ ψ : ℂ → ℝ}
    (h : ∀ x ∈ closedUnitSquare, |φ x - ψ x| ≤ M) (z w : ℂ) :
    lfppDOn ξ φ closedUnitSquare z w ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppDOn ξ ψ closedUnitSquare z w ∧
      lfppDOn ξ ψ closedUnitSquare z w ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) * lfppDOn ξ φ closedUnitSquare z w :=
  ⟨lfppDOn_le_of_abs_sub_le h z w,
    lfppDOn_le_of_abs_sub_le (fun x hx => by rw [abs_sub_comm]; exact h x hx) z w⟩

end LQGMetric.DFGPS
