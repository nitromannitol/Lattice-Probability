/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedDef at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Cont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreB
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont

 





















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

 
def plRad (q ε : ℝ) : ℝ := ε * Real.log ε⁻¹ ^ q

lemma log_inv_pos {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : 0 < Real.log ε⁻¹ :=
  Real.log_pos ((one_lt_inv₀ hε.1).2 hε.2)

lemma plRad_pos (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : 0 < plRad q ε :=
  mul_pos hε.1 (Real.rpow_pos_of_pos (log_inv_pos hε) q)

lemma plRad_sq_pos (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : 0 < plRad q ε ^ 2 :=
  pow_pos (plRad_pos q hε) 2

lemma sqrt_plRad_sq (q : ℝ) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (plRad q ε ^ 2) = plRad q ε :=
  Real.sqrt_sq (plRad_pos q hε).le

 

def plBump (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (y : ℂ) : ℝ :=
  locBump (plRad q ε ^ 2) (plRad_sq_pos q hε) y

lemma contDiff_plBump (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (plBump q ε hε) :=
  contDiff_locBump _ _

lemma plBump_nonneg (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (y : ℂ) : 0 ≤ plBump q ε hε y :=
  locBump_nonneg _ _ _

lemma plBump_le_one (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (y : ℂ) : plBump q ε hε y ≤ 1 :=
  locBump_le_one _ _ _

lemma plBump_eq_one (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {y : ℂ} (hy : ‖y‖ ≤ plRad q ε / 2) :
    plBump q ε hε y = 1 :=
  locBump_eq_one _ _ (by rw [sqrt_plRad_sq q hε]; exact hy)

lemma plBump_eq_zero (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) {y : ℂ} (hy : plRad q ε ≤ ‖y‖) :
    plBump q ε hε y = 0 :=
  locBump_eq_zero _ _ (by rw [sqrt_plRad_sq q hε]; exact hy)

lemma plBump_radial (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (y : ℂ) :
    plBump q ε hε y = plBump q ε hε (‖y‖ : ℂ) :=
  locBump_radial _ _ _

lemma plBump_comp_eq_zero (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) {w : ℂ}
    (hw : w ∉ closedBall z (plRad q ε)) : plBump q ε hε (z - w) = 0 := by
  refine plBump_eq_zero q ε hε ?_
  rw [mem_closedBall, not_le] at hw
  rw [← dist_eq_norm, dist_comm]
  exact hw.le

 

 
def plTest (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) : TestC where
  toFun := fun w => plBump q ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w
  contDiff' := ((contDiff_plBump q ε hε).comp (contDiff_const.sub contDiff_id)).mul
    (contDiff_heatKernel_left _ z)
  hasCompactSupport' := (HasCompactSupport.intro (isCompact_closedBall z (plRad q ε))
    fun _ hw => plBump_comp_eq_zero q ε hε z hw).mul_right
  tsupport_subset' := subset_univ _

lemma plTest_apply (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z w : ℂ) :
    plTest q ε hε z w = plBump q ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w := rfl

theorem tsupport_plTest_subset (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) :
    tsupport (plTest q ε hε z : ℂ → ℝ) ⊆ closedBall z (plRad q ε) := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  by_contra hc
  exact hw (show plBump q ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w = 0 by
    rw [plBump_comp_eq_zero q ε hε z hc, zero_mul])

lemma plTest_nonneg (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z w : ℂ) : 0 ≤ plTest q ε hε z w :=
  mul_nonneg (plBump_nonneg _ _ _ _) (heatKernel_nonneg _ (by positivity) _ _)

 
lemma plTest_translate (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z w : ℂ) :
    plTest q ε hε z w = plTest q ε hε 0 (w - z) := by
  rw [plTest_apply, plTest_apply]
  congr 1
  · congr 1; ring
  · unfold heatKernel
    rw [zero_sub, norm_neg, norm_sub_rev]

 
def plZ (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) : ℝ := ∫ w, plTest q ε hε 0 w
lemma integral_plTest (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) :
    ∫ w, plTest q ε hε z w = plZ q ε hε := by
  simp_rw [plTest_translate q ε hε z]
  exact integral_sub_right_eq_self (fun w => plTest q ε hε 0 w) z

lemma plZ_pos (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) : 0 < plZ q ε hε := by
  have hc : Continuous (plTest q ε hε 0 : ℂ → ℝ) := (plTest q ε hε 0).continuous
  have h0 : plTest q ε hε 0 0 ≠ 0 := by
    rw [plTest_apply, sub_zero, plBump_eq_one q ε hε (by
      rw [norm_zero]; exact (div_pos (plRad_pos q hε) two_pos).le), one_mul]
    unfold heatKernel
    have : 0 < ε ^ 2 / 2 := by have := hε.1; positivity
    positivity
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (plTest q ε hε 0).hasCompactSupport (plTest_nonneg q ε hε 0) h0

lemma plZ_le_one (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) : plZ q ε hε ≤ 1 := by
  have hs : 0 < ε ^ 2 / 2 := by have := hε.1; positivity
  rw [← integral_heatKernel (ε ^ 2 / 2) hs 0]
  refine integral_mono ((plTest q ε hε 0).continuous.integrable_of_hasCompactSupport
    (plTest q ε hε 0).hasCompactSupport) (integrable_heatKernel _ hs 0) fun w => ?_
  rw [plTest_apply]
  calc plBump q ε hε (0 - w) * heatKernel (ε ^ 2 / 2) 0 w ≤ 1 * heatKernel (ε ^ 2 / 2) 0 w :=
        mul_le_mul_of_nonneg_right (plBump_le_one _ _ _ _) (heatKernel_nonneg _ hs.le _ _)
    _ = _ := one_mul _

 
def plMollify (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (h : DistC) (z : ℂ) : ℝ :=
  (plZ q ε hε)⁻¹ * h (plTest q ε hε z)

 
theorem plMollify_addConst (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (h : DistC) (c : ℝ) (z : ℂ) :
    plMollify q ε hε (addConst h c) z = plMollify q ε hε h z + c := by
  unfold plMollify
  rw [GFFInv.addConst_apply, integral_plTest, mul_add, ← mul_assoc, inv_mul_cancel₀ (plZ_pos q ε hε).ne',
    one_mul]

 

theorem plMollify_congr (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (O : TopologicalSpace.Opens ℂ)
    {g g' : DistC} (he : restrictTo O g = restrictTo O g') {z : ℂ}
    (hz : closedBall z (plRad q ε) ⊆ O) :
    plMollify q ε hε g z = plMollify q ε hε g' z := by
  unfold plMollify
  rw [DFGPS.L217.apply_eq_of_restrictTo_eq he _ ((tsupport_plTest_subset q ε hε z).trans hz)]

 
end SupercriticalLQGUniqueness.B2.Polylog
