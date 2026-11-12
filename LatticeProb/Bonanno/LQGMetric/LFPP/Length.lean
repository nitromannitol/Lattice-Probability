/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Length at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Metric.WeylConcat
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# LFPP is a length metric; curve length of piecewise C¹ paths

Task P2-LFPP, items 1 and 3 (DFGPS.S5 "Riemannian length = curve length", upper half). For
continuous `φ`, the `D^φ`-length of a piecewise C¹ path is at most `∫₀¹ e^{ξφ(P)}|P'|`
(`len_le_lfppLen`; partition definition of length, GM l. 262–266), so `(ℂ, D^φ)` is a length
space (`isLength_lfppContMetric`; GM l. 268–271). Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

open MetricGeometry

variable {ξ : ℝ} {φ : ℂ → ℝ}

theorem edist_lfppContMetric (hφ : Continuous φ) (x y : ℂ) :
    edist ((lfppContMetric ξ φ hφ).pt x) ((lfppContMetric ξ φ hφ).pt y) = lfppD ξ φ x y := by
  rw [edist_dist, ContMetric.dist_pt, lfppContMetric_apply]
  exact ENNReal.ofReal_toReal (lfppD_ne_top hφ x y)

/-- `D^φ(P(s), P(t)) ≤ ∫_s^t e^{ξφ(P)}|P'|` -/
theorem lfppD_le_setLIntegral {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    lfppD ξ φ (P s) (P t) ≤ ∫⁻ τ in Ioc s t, lenDens ξ φ P τ := by
  rcases hst.lt_or_eq with hlt | rfl
  · rw [setLIntegral_congr Ioc_ae_eq_Icc, ← lfppLen_subPath P hlt]
    exact lfppDOn_le (isPiecewiseC1Path_subPath hP hs hlt ht) fun _ _ => mem_univ _
  · exact (lfppDOn_self (ξ := ξ) (φ := φ) convex_univ (mem_univ (P s))).le.trans (zero_le)

/-- **The `D^φ`-length of a piecewise C¹ path is at most its LFPP length.** -/
theorem len_le_lfppLen (hφ : Continuous φ) {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (lfppContMetric ξ φ hφ).len P a b ≤ ∫⁻ τ in Icc a b, lenDens ξ φ P τ := by
  refine eVariationOn_le_lintegral fun s t hs hst ht => ?_
  show edist ((lfppContMetric ξ φ hφ).pt (P s)) ((lfppContMetric ξ φ hφ).pt (P t)) ≤ _
  rw [edist_lfppContMetric]
  exact lfppD_le_setLIntegral hP (ha.trans hs) hst (ht.trans hb)

/-- **`(ℂ, D^φ)` is a length space.** -/
theorem isLength_lfppContMetric (hφ : Continuous φ) : (lfppContMetric ξ φ hφ).IsLength := by
  rw [ContMetric.IsLength, isLengthSpace_iff_curves]
  intro x y ε hε
  have hlt : lfppD ξ φ x y < lfppD ξ φ x y + ENNReal.ofReal ε :=
    ENNReal.lt_add_right (lfppD_ne_top hφ x y) (by simpa using hε)
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  have h1 : (lfppContMetric ξ φ hφ).len P.1 0 1 ≤ lfppLen ξ φ P.1 :=
    len_le_lfppLen hφ P.2.1 le_rfl le_rfl
  refine ⟨(lfppContMetric ξ φ hφ).pt ∘ P.1, 0, 1, zero_le_one,
    (ContMetric.continuous_pt _).comp_continuousOn P.2.1.continuousOn, ?_, ?_, ?_⟩
  · show P.1 0 = x; exact P.2.1.source
  · show P.1 1 = y; exact P.2.1.target
  · rw [show edist x y = lfppD ξ φ x y from edist_lfppContMetric hφ x y]
    exact h1.trans hP.le

theorem isLength_lfppDistCM (ξ ε : ℝ) (h : DistC) (hc : Continuous (heatMollify ε h)) :
    (lfppDistCM ξ ε h hc).IsLength :=
  isLength_lfppContMetric hc

end LFPP
end LQGMetric
