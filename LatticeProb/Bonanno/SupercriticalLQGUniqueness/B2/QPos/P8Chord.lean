/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P8Chord at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos.P8

open LQGDimension.TreeIneqJ42 in
 
theorem chord_le_sub {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖P b - P a‖ ≤ ∫ t in a..b, ‖deriv P t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hP.piecewise
  have hsub : uIcc a b ⊆ uIcc 0 1 := by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le P (deriv P) hab
    (countable_range t) (hP.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun x hx => hasDerivAt_of_piece ht0 htk hC
      ⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩ hx.2)
    (hP.intervalIntegrable_deriv_dddf.mono_set hsub)
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

 
theorem ofReal_chord_le_sub {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ENNReal.ofReal ‖P b - P a‖ ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal ‖deriv P t‖ := by
  have hsub : uIcc a b ⊆ uIcc 0 1 := by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb
  have hI := hP.intervalIntegrable_deriv_dddf.mono_set hsub
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hI
  have hI' : IntegrableOn (fun t => ‖deriv P t‖) (Ioo a b) :=
    IntegrableOn.mono_set hI.norm Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hI' (Filter.Eventually.of_forall fun _ =>
    norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ((chord_le_sub hP ha hab hb).trans_eq ?_)
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

 


theorem exit_interval {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {c : ℂ}
    {r₁ r₂ : ℝ} (hr : r₁ < r₂) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hcs : ‖P s - c‖ ≤ r₁)
    (hfar : r₂ ≤ ‖P 0 - c‖ ∨ r₂ ≤ ‖P 1 - c‖) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ (∀ t ∈ Ioo a b, ‖P t - c‖ < r₂) ∧
      r₂ - r₁ ≤ ‖P b - P a‖ := by
  have hcont := hP.continuousOn
  have hdist : ContinuousOn (fun t => ‖P t - c‖) (Icc 0 1) :=
    (hcont.sub continuousOn_const).norm
  rcases hfar with h0 | h1
  · 
    set D := Icc 0 s ∩ (fun t => ‖P t - c‖) ⁻¹' Ici r₂ with hD
    have hDc : IsClosed D :=
      (hdist.mono (Icc_subset_Icc le_rfl hs.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hDne : D.Nonempty := ⟨0, ⟨le_rfl, hs.1⟩, h0⟩
    have hDb : BddAbove D := ⟨s, fun t ht => ht.1.2⟩
    set a := sSup D
    have haD : a ∈ D := hDc.csSup_mem hDne hDb
    refine ⟨a, s, haD.1.1, haD.1.2, hs.2, fun t ht => ?_, ?_⟩
    · by_contra hge
      push_neg at hge
      have htD : t ∈ D := ⟨⟨le_trans haD.1.1 ht.1.le, ht.2.le⟩, hge⟩
      have := le_csSup hDb htD
      linarith [ht.1]
    · have h2 : r₂ ≤ ‖P a - c‖ := haD.2
      have := norm_sub_norm_le (P a - c) (P s - c)
      rw [show P a - c - (P s - c) = P a - P s by ring, norm_sub_rev (P a) (P s)] at this
      linarith
  · 
    set D := Icc s 1 ∩ (fun t => ‖P t - c‖) ⁻¹' Ici r₂ with hD
    have hDc : IsClosed D :=
      (hdist.mono (Icc_subset_Icc hs.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hDne : D.Nonempty := ⟨1, ⟨hs.2, le_rfl⟩, h1⟩
    have hDb : BddBelow D := ⟨s, fun t ht => ht.1.1⟩
    set b := sInf D
    have hbD : b ∈ D := hDc.csInf_mem hDne hDb
    refine ⟨s, b, hs.1, hbD.1.1, hbD.1.2, fun t ht => ?_, ?_⟩
    · by_contra hge
      push_neg at hge
      have htD : t ∈ D := ⟨⟨ht.1.le, le_trans ht.2.le hbD.1.2⟩, hge⟩
      have := csInf_le hDb htD
      linarith [ht.2]
    · have h2 : r₂ ≤ ‖P b - c‖ := hbD.2
      have := norm_sub_norm_le (P b - c) (P s - c)
      rw [show P b - c - (P s - c) = P b - P s by ring] at this
      linarith

end SupercriticalLQGUniqueness.B2.QPos.P8
