/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.PathAnalytic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux

/-!
# Analytic facts on piecewise C¹ paths: integrable speed, chord ≤ arclength

Task P2-LFPP. Adapted from LQGDimension (`LQGDimension/LFPP/TreeInequalityAux.lean`,
`deriv_intervalIntegrable`, `chord_le_arclength`), whose proofs are for `IsAdmissiblePath`
(paths `0 → 1` in `U`); the piece lemmas `exists_piece`, `hasDerivAt_of_piece`,
`deriv_bound_piece` are reused directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

open LQGDimension.TreeIneqJ42 (exists_piece hasDerivAt_of_piece deriv_bound_piece)

variable {P : ℝ → ℂ} {z w : ℂ}

/-- `P'` is integrable on `[0,1]` (as LD's `deriv_intervalIntegrable`). -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.intervalIntegrable_deriv (hP : IsPiecewiseC1Path P z w) :
    IntervalIntegrable (deriv P) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hP.piecewise
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv P x‖ ≤ C :=
    fun i => deriv_bound_piece (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv P x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv P).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

theorem _root_.LQGMetric.IsPiecewiseC1Path.integrableOn_norm_deriv (hP : IsPiecewiseC1Path P z w) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) : IntegrableOn (fun t => ‖deriv P t‖) (Icc a b) := by
  have h := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1
    hP.intervalIntegrable_deriv
  exact (h.mono_set (Icc_subset_Icc ha hb)).norm

/-- **Chord ≤ arclength** (as LD's `chord_le_arclength`). -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.norm_sub_le (hP : IsPiecewiseC1Path P z w) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) : ‖P b - P a‖ ≤ ∫ t in a..b, ‖deriv P t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hP.piecewise
  have hI : IntervalIntegrable (deriv P) volume a b :=
    hP.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ha hb)
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le P (deriv P) hab
    (countable_range t) (hP.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun x hx => hasDerivAt_of_piece ht0 htk hC
      ⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩ hx.2) hI
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- Chord ≤ arclength, `ℝ≥0∞` form on `Icc`. -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.ofReal_norm_sub_le (hP : IsPiecewiseC1Path P z w) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ENNReal.ofReal ‖P b - P a‖ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal ‖deriv P t‖ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hP.integrableOn_norm_deriv ha hb)
    (Eventually.of_forall fun _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ((hP.norm_sub_le ha hab hb).trans_eq ?_)
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- the arclength `∫₀¹ |P'|` is finite -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.lintegral_norm_deriv_lt_top (hP : IsPiecewiseC1Path P z w) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖deriv P t‖ < ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hP.integrableOn_norm_deriv le_rfl le_rfl)
    (Eventually.of_forall fun _ => norm_nonneg _)]
  exact ENNReal.ofReal_lt_top

/-- **Lower bound** `m |P(b) - P(a)| ≤ ∫_a^b e^{ξφ(P)}|P'|` when `m ≤ e^{ξ φ(P t)}` on `[a,b]`. -/
theorem _root_.LQGMetric.IsPiecewiseC1Path.ofReal_mul_norm_sub_le (hP : IsPiecewiseC1Path P z w) {ξ : ℝ}
    {φ : ℂ → ℝ} {m : ℝ} (hm : 0 ≤ m) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hmP : ∀ t ∈ Icc a b, m ≤ Real.exp (ξ * φ (P t))) :
    ENNReal.ofReal (m * ‖P b - P a‖) ≤ ∫⁻ t in Icc a b, lenDens ξ φ P t := by
  rw [ENNReal.ofReal_mul hm]
  calc ENNReal.ofReal m * ENNReal.ofReal ‖P b - P a‖
      ≤ ENNReal.ofReal m * ∫⁻ t in Icc a b, ENNReal.ofReal ‖deriv P t‖ :=
        mul_le_mul_right (hP.ofReal_norm_sub_le ha hab hb) _
    _ = ∫⁻ t in Icc a b, ENNReal.ofReal m * ENNReal.ofReal ‖deriv P t‖ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ t in Icc a b, lenDens ξ φ P t := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        rw [← ENNReal.ofReal_mul hm]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hmP t ht) (norm_nonneg _))

end LFPP
end LQGMetric
