/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8FinMed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCross
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `𝔞_ε / λ_ε` is bounded above and below (DFGPS T:888–891)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:888–891): "In particular, this implies
that `λ_ε` is bounded above and below by `ε`-independent constants times the median
`D̂_h^ε`-distance between the left and right sides of `[0,1]²`. By Lemma 2.1 (for `h`), we now get
that `{𝔞_ε/λ_ε}_{ε ∈ (0,1)}` is bounded above and below by positive, finite constants".

`aEps_lambda_bounds`: for a normalized whole-plane GFF `g` with the Markov coupling data on
`(-1,2)²` and DDDF's zero-boundary versions `Y` (tight, limits positive off the diagonal:
`zb_step`), there are `C > 0`, `ε₁ > 0` with `λ_ε > 0` and `C⁻¹ λ_ε ≤ 𝔞_ε ≤ C λ_ε` for
`ε < ε₁` (only small `ε` are needed: the range `[ε₁, 1)` is handled by `lem2_8_tight_far'`).

Proof: with probability `≥ 3/4`, `D_g^ε ≍_K D_{Y_{ε²}}` (`gff_zb_field_prob`), and the crossing
value `crossPhi(λ_ε⁻¹ D_{Y_{ε²}})` lies in `(c, C]` (`lower_quantile_of_pos`,
`upper_quantile_of_tight`); hence `lfppCrossIn(g) ∈ [K⁻¹ λ_ε c, K λ_ε C]` with probability `≥ 3/4`
(`le_lfppCrossIn_of_dom`, `lfppCrossIn_le_of_dom`), and `normGFFLaw = P.map g`
(`GM.normGFFLaw_eq`) bounds the lower median. Own bookkeeping of the paper's sketch.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP HeatSq WhiteNoise DDDF

lemma prob_compl_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Set Ω} (hT : P Tᶜ ≤ ENNReal.ofReal (1 / 4)) : (2 : ℝ≥0∞)⁻¹ ≤ P T := by
  have h1 : (1 : ℝ≥0∞) ≤ P T + ENNReal.ofReal (1 / 4) := by
    calc (1 : ℝ≥0∞) = P (T ∪ Tᶜ) := by rw [union_compl_self, measure_univ]
      _ ≤ P T + P Tᶜ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hT
  have h2 : 1 - ENNReal.ofReal (1 / 4) ≤ P T := tsub_le_iff_right.2 h1
  refine le_trans ?_ h2
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
    show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

lemma lfppCrossIn_nonneg (ξ ε : ℝ) (h : DistC) : 0 ≤ lfppCrossIn ξ ε h := ENNReal.toReal_nonneg

/-- **`𝔞_ε ≍ λ_ε`** (DFGPS T:888–891), small `ε`. -/
theorem aEps_lambda_bounds {ξ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W' : WNSpace → Ω' → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g hh hz : Ω → DistC} {c : Ω → ℝ} (hg : IsNormalizedWPGFF g P)
    (hsum : ∀ ω, addConst (g ω) (c ω) = hh ω + hz ω)
    (hharm : ∀ᵐ ω ∂P, ∃ f : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd f (sqOpen (-1) 3) ∧
      ∀ φ : TestOn (sqOpens (-1) 3), restrictTo _ (hh ω) φ = ∫ x, f x * φ x)
    {Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ} (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P)
    (hlink : ∀ φ : TestOn (sqOpens (-1) 3), Xh φ.toBddOn =ᵐ[P]
      fun ω => restrictTo (sqOpens (-1) 3) (hz ω) φ)
    {Y : ℝ → ℂ → Ω → ℝ}
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P)
    (hT : IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω =>
        sqMetricC ξ (lambdaDelta ξ W' P' (Real.sqrt δ)) (fun x => Y δ x ω)})
    (hpos : ∀ (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
        (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ)),
        (∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map fun ω =>
          sqMetricC ξ (lambdaDelta ξ W' P' (Real.sqrt (δn n))) (fun x => Y (δn n) x ω)) →
        Tendsto δn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsPosOffDiag d) :
    ∃ C > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → 0 < lambdaDelta ξ W' P' ε ∧
      C⁻¹ * lambdaDelta ξ W' P' ε ≤ aEpsDF ξ ε ∧ aEpsDF ξ ε ≤ C * lambdaDelta ξ W' P' ε := by
  set A : ℝ → Ω → C(closedUnitSquare × closedUnitSquare, ℝ) := fun δ ω =>
    sqMetricC ξ (lambdaDelta ξ W' P' (Real.sqrt δ)) (fun x => Y δ x ω)
  have hAm : ∀ δ ∈ Ioo (0 : ℝ) 1, AEMeasurable (A δ) P := fun δ hδ =>
    ((measurable_sqFun ξ _).comp (measurable_pathC (hY δ hδ).1 (hY δ hδ).2.1)).aemeasurable
  have h8 : (0 : ℝ) < 1 / 8 := by norm_num
  obtain ⟨M, εa, hεa, hcmp⟩ := gff_zb_field_prob hg.1 hsum hharm hX hlink hY (1 / 8) h8
  obtain ⟨Cu, hCu⟩ := upper_quantile_of_tight A hAm hT crossPhi continuous_crossPhi (1 / 8) h8
  obtain ⟨cl, hcl, δ₀, hδ₀, hlow⟩ := lower_quantile_of_pos A hAm hT hpos crossPhi
    continuous_crossPhi (fun d hd => crossPhi_pos hd) (1 / 8) h8
  set K : ℝ := Real.exp (|ξ| * M)
  have hK : 0 < K := Real.exp_pos _
  set Cu' : ℝ := max Cu 1
  refine ⟨max (K * Cu') (K / cl), by positivity, min εa (min (Real.sqrt δ₀) 1),
    by have := Real.sqrt_pos.2 hδ₀; positivity, fun ε hε hεε => ?_⟩
  have hεa' : ε < εa := lt_of_lt_of_le hεε (min_le_left _ _)
  have hε0 : ε < Real.sqrt δ₀ := lt_of_lt_of_le hεε ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := lt_of_lt_of_le hεε ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : ε ^ 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hδδ : ε ^ 2 ∈ Ioo (0 : ℝ) δ₀ := ⟨by positivity, by
    have := Real.sq_sqrt hδ₀.le
    nlinarith [Real.sqrt_nonneg δ₀]⟩
  have hsq : Real.sqrt (ε ^ 2) = ε := Real.sqrt_sq hε.le
  set lam := lambdaDelta ξ W' P' ε
  have hAe : ∀ ω, A (ε ^ 2) ω = sqMetricC ξ lam (fun x => Y (ε ^ 2) x ω) := fun ω => by
    simp only [A, hsq, lam]
  have hYc : ∀ ω, Continuous fun x => Y (ε ^ 2) x ω := (hY _ hδ).1
  -- the events
  set Ebad := {ω | ∃ x ∈ closedUnitSquare, M < |heatMollify ε (g ω) x - Y (ε ^ 2) x ω|}
  set Eup := {ω | Cu < crossPhi (A (ε ^ 2) ω)}
  set Elow := {ω | crossPhi (A (ε ^ 2) ω) ≤ cl}
  set N := {ω | ¬ Continuous (heatMollify ε (g ω))}
  have hPbad : P Ebad ≤ ENNReal.ofReal (1 / 8) := hcmp ε hε hεa'
  have hPup : P Eup ≤ ENNReal.ofReal (1 / 8) := hCu _ hδ
  have hPlow : P Elow ≤ ENNReal.ofReal (1 / 8) := hlow _ hδδ
  have hN : P N = 0 := measure_eq_zero_iff_ae_notMem.2
    (((isGFFPlusBddCont_of_wp hg.1).ae_tendstoLocallyUniformly_heatMollify ε hε.ne').mono
      fun ω hω h => h hω.2)
  have hsum2 : ∀ {E : Set Ω}, P E ≤ ENNReal.ofReal (1 / 8) →
      P (Ebad ∪ E ∪ N) ≤ ENNReal.ofReal (1 / 4) := fun {E} hE => by
    calc P (Ebad ∪ E ∪ N) ≤ P Ebad + P E + P N :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) + 0 := by
          rw [hN]; exact add_le_add (add_le_add hPbad hE) le_rfl
      _ = ENNReal.ofReal (1 / 4) := by
          rw [add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  -- comparison on good `ω`
  have hgood : ∀ ω, ω ∉ Ebad → ω ∉ N → Continuous (heatMollify ε (g ω)) ∧
      (∀ z w, lfppDOn ξ (heatMollify ε (g ω)) closedUnitSquare z w ≤
        ENNReal.ofReal K * lfppDOn ξ (fun x => Y (ε ^ 2) x ω) closedUnitSquare z w) ∧
      (∀ z w, lfppDOn ξ (fun x => Y (ε ^ 2) x ω) closedUnitSquare z w ≤
        ENNReal.ofReal K * lfppDOn ξ (heatMollify ε (g ω)) closedUnitSquare z w) := by
    intro ω h1 h2
    have hs : ∀ x ∈ closedUnitSquare, |heatMollify ε (g ω) x - Y (ε ^ 2) x ω| ≤ M :=
      fun x hx => not_lt.1 fun h => h1 ⟨x, hx, h⟩
    exact ⟨not_not.1 h2, fun z w => (lfppDOn_biLip_of_sup_le hs z w).1,
      fun z w => (lfppDOn_biLip_of_sup_le hs z w).2⟩
  -- positivity of `λ_ε`
  have hlam : 0 < lam := by
    by_contra hneg
    push_neg at hneg
    have hall : Elow = univ := by
      ext ω
      simp only [Elow, mem_ofPred_eq, mem_univ, iff_true]
      obtain ⟨p, hp⟩ := lrPairs_nonempty
      refine (crossPhi_le _ hp).trans ?_
      rw [hAe, sqMetricC_apply (hYc ω)]
      exact (mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg) ENNReal.toReal_nonneg).trans
        hcl.le
    rw [hall, measure_univ] at hPlow
    have := ENNReal.one_le_ofReal.1 hPlow
    norm_num at this
  -- the law of `g` is `normGFFLaw`
  have hlaw := GM.normGFFLaw_eq hg
  have hgm : AEMeasurable g P := hg.1.measurable.aemeasurable
  -- upper bound
  set m₀ : ℝ := K * lam * Cu'
  have hm₀ : (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {h | lfppCrossIn ξ ε h ≤ m₀} := by
    rw [hlaw]
    refine le_trans ?_ (Measure.le_map_apply hgm _)
    refine prob_compl_ge ((measure_mono ?_).trans (hsum2 hPup))
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨n1, n2⟩, n3⟩ := hn
    obtain ⟨hc, hd1, -⟩ := hgood ω n1 n3
    apply hω
    show lfppCrossIn ξ ε (g ω) ≤ m₀
    refine (lfppCrossIn_le_of_dom hc (hYc ω) hlam hK.le hd1).trans ?_
    rw [← hAe]
    have : crossPhi (A (ε ^ 2) ω) ≤ Cu' := (not_lt.1 n2).trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hbdd : BddBelow {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {h | lfppCrossIn ξ ε h ≤ m}} := by
    refine ⟨0, fun m hm => ?_⟩
    by_contra hneg
    push_neg at hneg
    have he : {h | lfppCrossIn ξ ε h ≤ m} = ∅ := by
      ext h; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hneg (lfppCrossIn_nonneg ξ ε h)
    rw [mem_ofPred_eq, he, measure_empty] at hm
    exact absurd hm (by simp)
  have hup : aEpsDF ξ ε ≤ m₀ := csInf_le hbdd hm₀
  -- lower bound
  set m₁ : ℝ := K⁻¹ * lam * cl
  have hlo : m₁ ≤ aEpsDF ξ ε := by
    refine le_csInf ⟨m₀, hm₀⟩ fun m hm => ?_
    by_contra hlt
    push_neg at hlt
    have hmeas : NullMeasurableSet {h | lfppCrossIn ξ ε h ≤ m} (P.map g) := by
      rw [← hlaw]
      exact nullMeasurableSet_le (aemeasurable_lfppCrossIn_normGFFLaw ξ ε hε) aemeasurable_const
    have hm' : (2 : ℝ≥0∞)⁻¹ ≤ P (g ⁻¹' {h | lfppCrossIn ξ ε h ≤ m}) := by
      have := hm
      simp only [mem_ofPred_eq] at this
      rwa [hlaw, Measure.map_apply₀ hgm hmeas] at this
    have hsub : g ⁻¹' {h | lfppCrossIn ξ ε h ≤ m} ⊆ Ebad ∪ Elow ∪ N := by
      intro ω hω
      by_contra hn
      simp only [mem_union, not_or] at hn
      obtain ⟨⟨n1, n2⟩, n3⟩ := hn
      obtain ⟨hc, -, hd2⟩ := hgood ω n1 n3
      have h1 := le_lfppCrossIn_of_dom hc (hYc ω) hlam hK hd2
      rw [← hAe] at h1
      have h2 : m₁ < K⁻¹ * lam * crossPhi (A (ε ^ 2) ω) :=
        mul_lt_mul_of_pos_left (not_le.1 n2) (by positivity)
      have h3 : lfppCrossIn ξ ε (g ω) ≤ m := hω
      linarith
    have := hm'.trans ((measure_mono hsub).trans (hsum2 hPlow))
    rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp] at this
    have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 this
    norm_num at this
  refine ⟨hlam, le_trans ?_ hlo, hup.trans ?_⟩
  · -- `C⁻¹ λ ≤ K⁻¹ λ cl`
    have hC : K / cl ≤ max (K * Cu') (K / cl) := le_max_right _ _
    have hCpos : 0 < max (K * Cu') (K / cl) := by positivity
    have : (max (K * Cu') (K / cl))⁻¹ ≤ K⁻¹ * cl := by
      rw [inv_le_comm₀ hCpos (by positivity), mul_inv, inv_inv, ← div_eq_mul_inv]
      exact hC
    calc (max (K * Cu') (K / cl))⁻¹ * lam ≤ K⁻¹ * cl * lam :=
          mul_le_mul_of_nonneg_right this hlam.le
      _ = m₁ := by ring
  · calc m₀ = K * Cu' * lam := by ring
      _ ≤ max (K * Cu') (K / cl) * lam :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le

end LQGMetric.DFGPS
