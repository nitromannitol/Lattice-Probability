/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffFarA at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFar
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `𝔞_ε` is bounded below on `[ε₁, 1)` (DFGPS Lemma 2.8, the range `[ε₁, 1)`)

`aEpsDF_ge_far`: for `0 < ε₁`, `inf_{ε ∈ [ε₁, 1)} 𝔞_ε > 0`. Own elementary argument (the paper
uses `𝔞_ε` only as a normalization): under `normGFFLaw` the field `(ε, z) ↦ h*_ε(z)` is a.s.
continuous on `(0,∞) × ℂ` (`lem2_1HeatJoint`), so `M := sup_{[ε₁,1] × B̄₂(0)} |h*_ε|` is finite and
`P(M > M₀) < 1/2` for some deterministic `M₀`; on `{M ≤ M₀}` every left–right crossing of `[0,1]²`
has `e^{ξ h*_ε} ds`-length `≥ e^{−|ξ| M₀}` (DDDF.S2.c, `rectLen_ge`), hence the median
`𝔞_ε ≥ e^{−|ξ| M₀}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP DDDF

lemma rectAB_one_toSet : (rectAB 1 1).toSet = closedUnitSquare := by
  ext z
  simp [MarkedRect.toSet, rectAB, closedUnitSquare, Complex.mem_reProdIm, and_assoc]

lemma lfppCrossIn_eq_rectLen (ξ ε : ℝ) (h : DistC) :
    lfppCrossIn ξ ε h = (rectLen ξ (heatMollify ε h) (rectAB 1 1)).toReal := by
  have h2 : (rectAB 1 1).side₁ = leftSide := by
    ext z; simp [MarkedRect.side₁, rectAB, leftSide, Complex.mem_reProdIm]
  have h3 : (rectAB 1 1).side₂ = rightSide := by
    ext z; simp [MarkedRect.side₂, rectAB, rightSide, Complex.mem_reProdIm]
  unfold lfppCrossIn rectLen crossLenIn
  rw [rectAB_one_toSet, h2, h3]

lemma lfppCrossIn_ge {ξ ε M : ℝ} {h : DistC} (hc : Continuous (heatMollify ε h))
    (hM : ∀ x ∈ closedUnitSquare, |heatMollify ε h x| ≤ M) :
    Real.exp (-(|ξ| * M)) ≤ lfppCrossIn ξ ε h := by
  rw [lfppCrossIn_eq_rectLen]
  have := exp_neg_le_lenObs (ξ := ξ) (Y := fun x (_ : Unit) => heatMollify ε h x)
    (fun _ => hc) (rectAB 1 1) zero_le_one zero_le_one (ω := ())
    (fun x hx => hM x (rectAB_one_toSet ▸ hx))
  simpa [lenObs, MarkedRect.crossWidth, rectAB] using this

lemma lfppCrossIn_le {ξ ε M : ℝ} {h : DistC}
    (hM : ∀ x ∈ closedUnitSquare, |heatMollify ε h x| ≤ M) :
    lfppCrossIn ξ ε h ≤ Real.exp (|ξ| * M) := by
  rw [lfppCrossIn_eq_rectLen]
  have := lenObs_le_exp (ξ := ξ) (Y := fun x (_ : Unit) => heatMollify ε h x)
    (rectAB 1 1) zero_le_one zero_le_one (ω := ())
    (fun x hx => hM x (rectAB_one_toSet ▸ hx))
  simpa [lenObs, MarkedRect.crossWidth, rectAB] using this

lemma closedUnitSquare_subset_closedBall_two : closedUnitSquare ⊆ closedBall (0 : ℂ) 2 := by
  intro z ⟨h1, h2, h3, h4⟩
  rw [mem_closedBall_zero_iff]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith

/-- **`𝔞_ε` is bounded below on `[ε₁, 1)`.** -/
theorem aEpsDF_ge_far (γ : ℝ) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∃ c > 0, ∀ ε ∈ Ico ε₁ 1, c ≤ aEpsDF (xiGamma γ) ε := by
  obtain ⟨Ω, _, P, hP, g, hg⟩ := GFFExist.exists_normalizedWPGFF
  have hlaw := GM.normGFFLaw_eq hg
  have hμ : IsProbabilityMeasure (normGFFLaw) := by rw [hlaw]; infer_instance
  have hid : IsWholePlaneGFF id (normGFFLaw) := by rw [hlaw]; exact GM.isWholePlaneGFF_id_map hg.1
  have hJ := lem2_1HeatJoint (normGFFLaw) id hid
  set ξ := xiGamma γ
  -- a deterministic `M` with `μ(M < farSup) < 1/2`
  have hfm : Measurable (farSup ε₁ 2) := measurable_farSup ε₁ 2
  have hT : Tendsto (fun n : ℕ => normGFFLaw {h | (n : ℝ) < farSup ε₁ 2 h}) atTop (𝓝 0) := by
    have hm : Antitone fun n : ℕ => {h : DistC | (n : ℝ) < farSup ε₁ 2 h} := fun m n hmn h hh => by
      simp only [mem_ofPred_eq] at hh ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hh
    have hI : (⋂ n : ℕ, {h : DistC | (n : ℝ) < farSup ε₁ 2 h}) = ∅ := by
      ext h; simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      exact exists_nat_ge _
    have := tendsto_measure_iInter_atTop (μ := normGFFLaw)
      (fun n : ℕ => (measurableSet_lt measurable_const hfm).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩
    rwa [hI, measure_empty] at this
  obtain ⟨n, hn⟩ := (hT.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 2⁻¹ by simp))).exists
  set M : ℝ := (n : ℝ)
  refine ⟨Real.exp (-(|ξ| * M)), Real.exp_pos _, fun ε hε => ?_⟩
  have hε0 : 0 < ε := hε₁.trans_le hε.1
  set G : Set DistC := {h | (∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
      ∃ L, Tendsto (fun n : ℕ => (id h : DistC) (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (id h) p.2) (Ioi 0 ×ˢ univ)} with hG
  have hG0 : normGFFLaw Gᶜ = 0 := hJ
  have hbd : ∀ h ∈ G, farSup ε₁ 2 h ≤ M → ∀ x ∈ closedUnitSquare, |heatMollify ε h x| ≤ M :=
    fun h hh hM x hx => (abs_heatMollify_le_farSup (p := (ε, x)) hε₁ hh.2
      ⟨⟨hε.1, hε.2.le⟩, closedUnitSquare_subset_closedBall_two hx⟩).trans hM
  -- the median set
  unfold aEpsDF lowerMedian
  have hgood : 2⁻¹ ≤ normGFFLaw ({h | farSup ε₁ 2 h ≤ M} ∩ G) := by
    rw [measure_inter_conull hG0]
    by_contra hlt
    push Not at hlt
    have h1 := measure_add_measure_compl (μ := normGFFLaw)
      (s := {h : DistC | farSup ε₁ 2 h ≤ M}) (measurableSet_le hfm measurable_const)
    have hc : {h : DistC | farSup ε₁ 2 h ≤ M}ᶜ = {h | M < farSup ε₁ 2 h} := by
      ext h; simp [not_le]
    rw [hc, measure_univ] at h1
    have : normGFFLaw {h : DistC | farSup ε₁ 2 h ≤ M} + normGFFLaw {h | M < farSup ε₁ 2 h} <
        2⁻¹ + 2⁻¹ := ENNReal.add_lt_add hlt hn
    rw [h1, ENNReal.inv_two_add_inv_two] at this
    exact lt_irrefl _ this
  refine le_csInf ⟨Real.exp (|ξ| * M), hgood.trans (measure_mono fun h hh =>
    lfppCrossIn_le (hbd h hh.2 hh.1))⟩ fun m hm => ?_
  by_contra hlt
  push Not at hlt
  have hsub : {h : DistC | lfppCrossIn ξ ε h ≤ m} ⊆ {h | M < farSup ε₁ 2 h} ∪ Gᶜ := by
    intro h hh
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, mem_compl_iff, not_or, not_lt, not_not] at hno
    have := lfppCrossIn_ge (ξ := ξ) (continuous_heatMollify_of_joint hno.2.2 hε0)
      (hbd h hno.2 hno.1)
    exact absurd (this.trans hh) (not_le.2 hlt)
  have := (hm.trans (measure_mono hsub)).trans (measure_union_le _ _)
  rw [hG0, add_zero] at this
  exact absurd hn (not_lt.2 this)

/-- **Tightness for `ε ∈ [ε₁, 1)`** (whole-plane GFF, any closed square, any `ε₁ > 0`). -/
theorem lem2_8_tight_far' {γ : ℝ} {a : ℂ} {s : ℝ} (hs : 0 < s) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ico ε₁ 1,
      μ = P.map fun ω => lfppSqC (xiGamma γ) ε (g ω) (closedSq a s)} := by
  obtain ⟨c, hc, h⟩ := aEpsDF_ge_far γ hε₁
  exact lem2_8_tight_far hs hg hε₁ hc h

end LQGMetric.DFGPS
