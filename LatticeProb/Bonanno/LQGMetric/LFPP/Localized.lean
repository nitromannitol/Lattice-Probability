/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Localized at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn

/-!
# DFGPS.S4: localized LFPP and its locality property (deterministic form)

DFGPS (`literature/src/1905.00380/lqg-metric-estimates-final.tex` l. 666–684): `ψ_ε` is a smooth
radial bump, `≡ 1` on `B_{ε^{1/2}/2}(0)`, `0` outside `B_{ε^{1/2}}(0)`;
`ĥ*_ε(z) := ∫ ψ_ε(z - w) h(w) p_{ε²/2}(z, w) dw` "in the sense of distributional pairing";
`D̂^ε_h(z,w) := inf_P ∫₀¹ e^{ξ ĥ*_ε(P(t))}|P'(t)| dt`; (eqn-localized-property, l. 683): "for any
open `U`, the internal metric `D̂^ε_h(·,·;U)` is a.s. determined by `h|_{B_{ε^{1/2}}(U)}`".

Here `ψ_ε` is built from mathlib's radial bump base `ContDiffBumpBase.ofInnerProductSpace`
with radii `√ε/2`, `√ε` (smooth and radial, `locBump_radial`), and
`ĥ*_ε(z) = ⟨h, ψ_ε(z - ·) p_{ε²/2}(z, ·)⟩` is a genuine pairing with a test function (no limit).
The locality is proved deterministically: if two distributions agree on all test functions
supported in `B_{√ε}(U)`, then `ĥ*_ε` agree on `U`, hence so do the internal LFPP distances
`lfppDOn ξ ĥ*_ε U` (infimum over piecewise C¹ paths in `U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace LFPP

/-- `ψ_ε`: smooth radial bump, `1` on `B_{√ε/2}(0)`, `0` off `B_{√ε}(0)` (DFGPS l. 666).
Built from mathlib's explicitly radial base `ContDiffBumpBase.ofInnerProductSpace`
(`y ↦ smoothTransition (2 - ‖y‖/(√ε/2))`), not from `someContDiffBumpBase` (a choice, not provably
radial). The argument `hε` is kept for the interface. -/
def locBump (ε : ℝ) (_hε : 0 < ε) (y : ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((Real.sqrt ε / 2)⁻¹ • y)

theorem contDiff_locBump (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (locBump ε hε) := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun y : ℂ => ((2 : ℝ), (Real.sqrt ε / 2)⁻¹ • y) :=
    contDiff_const.prodMk (contDiff_id.const_smul _)
  exact ((ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hf
    fun _ => ⟨by norm_num, mem_univ _⟩).of_le le_rfl

theorem locBump_nonneg (ε : ℝ) (hε : 0 < ε) (y : ℂ) : 0 ≤ locBump ε hε y :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _).1

theorem locBump_le_one (ε : ℝ) (hε : 0 < ε) (y : ℂ) : locBump ε hε y ≤ 1 :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _).2

theorem norm_locBump_arg (ε : ℝ) (hε : 0 < ε) (y : ℂ) :
    ‖(Real.sqrt ε / 2)⁻¹ • y‖ = ‖y‖ / (Real.sqrt ε / 2) := by
  have := Real.sqrt_pos.2 hε
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_eq_div]

/-- `ψ_ε = 1` on `B̄_{√ε/2}(0)` -/
theorem locBump_eq_one (ε : ℝ) (hε : 0 < ε) {y : ℂ} (hy : ‖y‖ ≤ Real.sqrt ε / 2) :
    locBump ε hε y = 1 := by
  have := Real.sqrt_pos.2 hε
  refine (ContDiffBumpBase.ofInnerProductSpace ℂ).eq_one 2 (by norm_num) _ ?_
  rw [norm_locBump_arg ε hε, div_le_one (by positivity)]
  exact hy

/-- `ψ_ε = 0` off `B_{√ε}(0)` -/
theorem locBump_eq_zero (ε : ℝ) (hε : 0 < ε) {y : ℂ} (hy : Real.sqrt ε ≤ ‖y‖) :
    locBump ε hε y = 0 := by
  have := Real.sqrt_pos.2 hε
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)
  by_contra hne
  have hm : (Real.sqrt ε / 2)⁻¹ • y ∈ Function.support
      ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) := hne
  rw [hs, mem_ball_zero_iff, norm_locBump_arg ε hε, div_lt_iff₀ (by positivity)] at hm
  linarith

/-- `ψ_ε` is radial: its value only depends on `‖y‖` (DFGPS l. 666, "radially symmetric") -/
theorem locBump_radial (ε : ℝ) (hε : 0 < ε) (y : ℂ) :
    locBump ε hε y = locBump ε hε (‖y‖ : ℂ) := by
  simp only [locBump, ContDiffBumpBase.ofInnerProductSpace, norm_smul, Complex.norm_real,
    norm_norm]

-- keep `ψ_ε` folded in downstream elaboration (unfolding it makes `whnf` time out)
attribute [irreducible] locBump

theorem contDiff_heatKernel_left (s : ℝ) (z : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w => heatKernel s z w := by
  unfold heatKernel
  apply contDiff_const.mul
  apply Real.contDiff_exp.comp
  apply ContDiff.div_const
  apply ContDiff.neg
  exact (contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)

theorem locBump_comp_eq_zero (ε : ℝ) (hε : 0 < ε) (z : ℂ) {w : ℂ}
    (hw : w ∉ closedBall z (Real.sqrt ε)) : locBump ε hε (z - w) = 0 := by
  refine locBump_eq_zero ε hε ?_
  rw [mem_closedBall, not_le] at hw
  rw [← dist_eq_norm, dist_comm]
  exact hw.le

/-- the test function `w ↦ ψ_ε(z - w) p_{ε²/2}(z, w)` -/
def locTest (ε : ℝ) (hε : 0 < ε) (z : ℂ) : TestC where
  toFun := fun w => locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w
  contDiff' := ((contDiff_locBump ε hε).comp (contDiff_const.sub contDiff_id)).mul
    (contDiff_heatKernel_left _ z)
  hasCompactSupport' := (HasCompactSupport.intro (isCompact_closedBall z (Real.sqrt ε))
    fun w hw => locBump_comp_eq_zero ε hε z hw).mul_right
  tsupport_subset' := subset_univ _

theorem tsupport_locTest_subset (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    tsupport (locTest ε hε z : ℂ → ℝ) ⊆ closedBall z (Real.sqrt ε) := by
  refine closure_minimal (fun w hw => ?_) isClosed_closedBall
  by_contra hc
  exact hw (show locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w = 0 by
    rw [locBump_comp_eq_zero ε hε z hc, zero_mul])

/-- the localized mollification `ĥ*_ε(z)` (DFGPS (eqn-localized-def)) -/
def locMollify (ε : ℝ) (hε : 0 < ε) (h : DistC) (z : ℂ) : ℝ := h (locTest ε hε z)

/-- the localized LFPP internal distance `D̂^ε_h(z, w; U)` -/
def lfppLocOn (ξ ε : ℝ) (hε : 0 < ε) (h : DistC) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  lfppDOn ξ (locMollify ε hε h) U z w

/-- the internal LFPP distance on `S` only depends on the density on `S` -/
theorem lfppDOn_congr {ξ : ℝ} {φ φ' : ℂ → ℝ} {S : Set ℂ} (h : EqOn φ φ' S) (z w : ℂ) :
    lfppDOn ξ φ S z w = lfppDOn ξ φ' S z w := by
  refine iInf_congr fun P => ?_
  rw [lfppLen_eq, lfppLen_eq]
  refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  simp only [lenDens, h (P.2.2 t ht)]

end LFPP
end LQGMetric
