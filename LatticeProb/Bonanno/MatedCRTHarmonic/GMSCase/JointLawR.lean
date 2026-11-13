/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.JointLawR at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.JointLaw

/-!
# The Case 3 and Case 4 laws at a general renormalization radius

Same statements as `GMSCase.JointLaw` with the radius `1/2` of [18] (4.41)–(4.42) replaced by an
arbitrary radius `r > 0` with `B̄_r(z₀) ⊆ B̄_1(0)`: the field `h(r · + z₀) − h_r(z₀)`
(`caseNormalized r h z₀`), its sampled average `h_r(z₀)` (`radAvg r h z₀`) and a law-preserving
measurable family `τ z₀` acting on an independent observation `Y`.

The repaired Case 3 argument  uses a radius `r ∈ (3/4, 1)` equal to
The radius of the γ-cone's Markov decomposition, so that the two random mesh factors have the same
law.

* `map_caseNormalized`, `map_case_pair`, `map_case_marked`;
* `indepFun_radAvg_caseLocal` (exact Lemma A.2 independence at radius `r`);
* `map_case3_marked_r` (disintegration over the sampled average = constant kernel).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint

section LawR

variable {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
  {h : Ω → DistC} {Y : Ω → 𝒴} {τ : ℂ → 𝒴 → 𝒴}

theorem measurable_caseNormalized_left (r : ℝ) (z₀ : ℂ) :
    Measurable fun g : DistC => caseNormalized r g z₀ := by
  have hpair : Measurable fun g : DistC => ((g, z₀) : DistC × ℂ) :=
    measurable_id.prodMk measurable_const
  have e : Measurable ((fun p : DistC × ℂ => caseNormalized r p.1 p.2) ∘
      (fun g : DistC => ((g, z₀) : DistC × ℂ))) := (measurable_caseNormalized r).comp hpair
  exact e

/-- The normalized pullback has the law of `h` (GM's affine invariance). -/
theorem map_caseNormalized (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    P.map (fun ω => caseNormalized r (h ω) z₀) = P.map h :=
  CircleAvg.map_affine_sub_circleAvg hh hr z₀

/-! ## Restriction to the unit disk -/

/-- The unit disk and the radius-`r` disk about `z₀` correspond under `y ↦ (y − z₀)/r`. -/
theorem mem_ballO_iff_radius {r : ℝ} (hr : 0 < r) (z₀ y : ℂ) :
    y ∈ ballO z₀ r ↔ r⁻¹ • y + (-((r⁻¹ : ℂ) * z₀)) ∈ ballO (0 : ℂ) 1 := by
  simp only [ballO, Opens.mem_mk, Metric.mem_ball, dist_eq_norm, sub_zero]
  have e : r⁻¹ • y + -((r⁻¹ : ℂ) * z₀) = (r⁻¹ : ℂ) * (y - z₀) := by
    rw [Complex.real_smul]; push_cast; ring
  have hn : ‖((r : ℂ))⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [e, norm_mul, hn]
  constructor
  · intro hh
    calc r⁻¹ * ‖y - z₀‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hh (inv_pos.2 hr)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  · intro hh
    have := mul_lt_mul_of_pos_left hh hr
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at this

/-- Restricting the radius-`r` pullback to the unit disk only sees the field on `B_r(z₀)`. -/
def caseLocalPull {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    DistOn (ballO z₀ r) → DistOn (ballO (0 : ℂ) 1) :=
  fun T => ((r⁻¹ : ℝ) ^ 2) • T.comp (GM.testScalePush (inv_ne_zero hr.ne') (mem_ballO_iff_radius hr z₀))

theorem measurable_caseLocalPull {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    Measurable (caseLocalPull hr z₀) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  show Measurable fun T : DistOn (ballO z₀ r) =>
    (r⁻¹ : ℝ) ^ 2 * T (GM.testScalePush (inv_ne_zero hr.ne') (mem_ballO_iff_radius hr z₀) ψ)
  exact (measurable_distOn_apply _).const_mul _

theorem restrictTo_affineComp_radius {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (affineComp r z₀ g) =
      caseLocalPull hr z₀ (restrictTo (ballO z₀ r) g) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GM.restrictTo_apply_eq_scale (r := r⁻¹) (inv_pos.2 hr) (mem_ballO_iff_radius hr z₀)]
  have hcomp : affineComp r⁻¹ (-((r⁻¹ : ℂ) * z₀)) (affineComp r z₀ g) = g := by
    rw [GM.affineComp_comp (inv_ne_zero hr.ne') hr.ne']
    have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    have h2 : (r : ℂ) * -((r⁻¹ : ℂ) * z₀) + z₀ = 0 := by
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring
    rw [h1, h2]
    exact GM.affineComp_one_zero g
  rw [hcomp]
  rfl

/-- The restricted normalized pullback is the pullback of the restricted re-normalized field. -/
theorem restrictTo_caseNormalized {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (caseNormalized r g z₀) =
      caseLocalPull hr z₀ (restrictTo (ballO z₀ r) (addConst g (-circleAvg g r z₀))) := by
  rw [caseNormalized, ← GM.affineComp_addConst hr, restrictTo_affineComp_radius hr]

end LawR

end MatedCRTHarmonic.GMSCase
