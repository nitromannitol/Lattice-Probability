/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidChain
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.Smoothing




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric.MetricGeometry

 

private theorem finite_curve_transfer (D E : LSCMetric) (Y : Set ℂ)
    (hint : D.internal Y = E.internal Y)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hY : ∀ t ∈ Icc a b, P t ∈ Y) (hfin : D.len P a b ≠ ∞) :
    ∃ (Q : ℝ → ℂ) (L : ℝ), E.IsCurve Q 0 L ∧
      Q '' Icc 0 L = P '' Icc a b ∧ E.len Q 0 L = D.len P a b := by
  let L := (D.len P a b).toReal
  let Q : ℝ → ℂ := @lengthParam D.Space
    (@EMetricSpace.toPseudoEMetricSpace D.Space D.instEMetricSpace) (D.pt ∘ P) a b
  have hDu : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L) := by
    have h0 := hasUnitSpeedOn_lengthParam hP.1 hP.2 hfin
    dsimp [Q, L, LSCMetric.len, LSCMetric.pt, Function.comp, id] at h0 ⊢
    exact h0
  have hDc : D.IsCurve Q 0 L :=
    ⟨ENNReal.toReal_nonneg, continuousOn_of_hasUnitSpeedOn hDu⟩
  have himage : Q '' Icc 0 L = P '' Icc a b := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have himg := variationOnFromTo_image_Icc hP.1 hP.2 hfin
      have hs' : s ∈ Icc 0 (curveLength (D.pt ∘ P) a b).toReal := by
        simpa only [L, LSCMetric.len, curveLength] using hs
      rw [← himg] at hs'
      obtain ⟨t, ht, rfl⟩ := hs'
      exact ⟨t, ht, by simpa [Q, LSCMetric.pt, LSCMetric.Space] using
        (lengthParam_variationOnFromTo hfin ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      have himg := variationOnFromTo_image_Icc hP.1 hP.2 hfin
      refine ⟨variationOnFromTo (D.pt ∘ P) (Icc a b) a t, ?_, ?_⟩
      · have hs' : variationOnFromTo (D.pt ∘ P) (Icc a b) a t ∈
            Icc 0 (curveLength (D.pt ∘ P) a b).toReal := by
          rw [← himg]
          exact ⟨t, ht, rfl⟩
        simpa only [L, LSCMetric.len, curveLength] using hs'
      · simpa [Q, LSCMetric.pt, LSCMetric.Space] using
          (lengthParam_variationOnFromTo hfin ht)
  have hQY : ∀ s ∈ Icc 0 L, Q s ∈ Y := by
    intro s hs
    obtain ⟨t, ht, hQ⟩ : Q s ∈ P '' Icc a b := by
      rw [← himage]; exact ⟨s, hs, rfl⟩
    rw [← hQ]
    exact hY t ht
  have hEbound : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      edist (E.pt (Q s)) (E.pt (Q t)) ≤ edist s t := by
    intro s hs t ht
    rcases le_total s t with hst | hst
    · have hsub : Icc s t ⊆ Icc 0 L := Icc_subset_Icc hs.1 ht.2
      have hc : D.IsCurve Q s t := ⟨hst, hDc.2.mono hsub⟩
      have hlen : D.len Q s t = ENNReal.ofReal (t - s) := by
        exact hasUnitSpeedOn_Icc_iff.mp hDu s t hs.1 hst ht.2
      calc
        edist (E.pt (Q s)) (E.pt (Q t))
            = E (Q s, Q t) := rfl
        _ ≤ E.internal Y (⟨Q s, hQY s hs⟩, ⟨Q t, hQY t ht⟩) :=
          BiLipschitz.Barrier.edist_le_internal' E Y
            (⟨Q s, hQY s hs⟩, ⟨Q t, hQY t ht⟩)
        _ = D.internal Y (⟨Q s, hQY s hs⟩, ⟨Q t, hQY t ht⟩) := by rw [hint]
        _ ≤ D.len Q s t := BiLipschitz.Barrier.internal_le_len' D hc
          (fun u hu => hQY u (hsub hu))
        _ = edist s t := by rw [hlen, edist_dist, Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr hst)]
    · have hsub : Icc t s ⊆ Icc 0 L := Icc_subset_Icc ht.1 hs.2
      have hc : D.IsCurve Q t s := ⟨hst, hDc.2.mono hsub⟩
      have hlen : D.len Q t s = ENNReal.ofReal (s - t) := by
        exact hasUnitSpeedOn_Icc_iff.mp hDu t s ht.1 hst hs.2
      calc
        edist (E.pt (Q s)) (E.pt (Q t))
            = E (Q t, Q s) := by rw [edist_comm]; rfl
        _ ≤ E.internal Y (⟨Q t, hQY t ht⟩, ⟨Q s, hQY s hs⟩) :=
          BiLipschitz.Barrier.edist_le_internal' E Y
            (⟨Q t, hQY t ht⟩, ⟨Q s, hQY s hs⟩)
        _ = D.internal Y (⟨Q t, hQY t ht⟩, ⟨Q s, hQY s hs⟩) := by rw [hint]
        _ ≤ D.len Q t s := BiLipschitz.Barrier.internal_le_len' D hc
          (fun u hu => hQY u (hsub hu))
        _ = edist s t := by rw [hlen, edist_dist, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr hst)]
  have hElip : LipschitzOnWith 1 (E.pt ∘ Q) (Icc 0 L) := by
    intro s hs t ht
    simpa [Function.comp_apply] using hEbound s hs t ht
  have hEc : E.IsCurve Q 0 L := ⟨ENNReal.toReal_nonneg, hElip.continuousOn⟩
  have hlen : E.len Q 0 L = D.len P a b := by
    rw [BiLipschitz.PaidSeparators.len_eq_internalPartitionSup E hEc hQY,
      ← hint, ← BiLipschitz.PaidSeparators.len_eq_internalPartitionSup D hDc hQY]
    have h0 := curveLength_lengthParam hP.1 hP.2 hfin
    dsimp [Q, L, LSCMetric.len, LSCMetric.pt, Function.comp, id] at h0 ⊢
    exact h0
  exact ⟨Q, L, hEc, himage, hlen⟩

theorem aroundDist_eq_of_internal_eq (D E : LSCMetric) (Y : Set ℂ)
    (hint : D.internal Y = E.internal Y) (A : EuclideanAnnulus)
    (hA : A.toSet ⊆ Y) : aroundDist D A = aroundDist E A := by
  have hle : ∀ X X' : LSCMetric, X.internal Y = X'.internal Y →
      aroundDist X' A ≤ aroundDist X A := by
    intro X X' hXX
    unfold aroundDist
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hPA => le_iInf fun hSep => ?_
    by_cases hfin : X.len P a b = ∞
    · rw [hfin]
      exact le_top
    obtain ⟨Q, L, hQ, htrace, hlen⟩ := finite_curve_transfer X X' Y hXX P a b hP
      (fun t ht => hA (hPA t ht)) hfin
    have hQA : ∀ t ∈ Icc 0 L, Q t ∈ A.toSet := by
      intro t ht
      have hmem : Q t ∈ P '' Icc a b := by
        rw [← htrace]
        exact ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hs'⟩ := hmem
      rw [← hs']
      exact hPA s hs
    have hSep' : Disconnects (Q '' Icc 0 L) A.innerBoundary A.outerBoundary := by
      rw [htrace]
      exact hSep
    have hcost : aroundDist X' A ≤ X'.len Q 0 L := by
      unfold aroundDist
      apply iInf_le_of_le Q
      apply iInf_le_of_le (0 : ℝ)
      apply iInf_le_of_le L
      apply iInf_le_of_le hQ
      apply iInf_le_of_le hQA
      exact iInf_le _ hSep'
    exact hcost.trans_eq hlen
  exact le_antisymm (hle E D hint.symm) (hle D E hint)

 
end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
