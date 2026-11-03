/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3A at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer2E
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.BubbleTransfer

/-!
# Germ step for unbounded `V`: the logarithmic cutoff at infinity (task P2-MKD3)

`logInf r R = 1 − χ_{0,r,R}` with QZ's logarithmic cutoff `K3.logCutoff` (`BubbleCutoff.lean`):
smooth, values in `[0,1]`, `= 1` on `B̄(0,2r)`, `= 0` off `B(0,R)`, and
`∫ ‖∇ logInf r R‖² ≤ 2π C² / log (R/(2r))` (`C = logCutoffConst`), so the whole-plane Dirichlet
pairing `(h, logInf r R)_∇` has norm `→ 0` as `R → ∞` ("a point, here `∞`, has zero capacity in
2D"). Source: Berestycki–Powell arXiv:2404.16642 §1.8 (logarithmic cutoffs; the whole-plane
Dirichlet space modulo constants); the computation is QZ's `logCutoff` gradient bound integrated
in polar coordinates (QZ `annulus_polar_integral`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovGermVer

open MarkovGauss MarkovZB MarkovGerm MarkovExt MarkovNorm Blueprint QuantumZipper
  QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

/-- the logarithmic cutoff at infinity: `1` on `B̄(0,2r)`, `0` off `B(0,R)` -/
def logInf (r R : ℝ) (x : ℂ) : ℝ := 1 - logCutoff 0 r R x

lemma contDiff_logInf {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logInf r R) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logCutoff (0 : ℂ) r R) := by
    unfold logCutoff
    exact (bubbleCutoff_contDiff_logCutoffRadial hr hR).comp
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  exact contDiff_const.sub h1

lemma logInf_mem_Icc (r R : ℝ) (x : ℂ) : 0 ≤ logInf r R x ∧ logInf r R x ≤ 1 := by
  have := bubbleCutoff_logCutoff_mem_Icc (0 : ℂ) r R x
  simp only [logInf]; constructor <;> linarith [this.1, this.2]

lemma logInf_eq_one {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) {x : ℂ} (hx : ‖x‖ ≤ 2 * r) :
    logInf r R x = 1 := by
  have := bubbleCutoff_logCutoff_eq_zero (0 : ℂ) hr hR (x := x) (by simpa using hx)
  simp [logInf, this]

lemma logInf_eq_zero {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) {x : ℂ} (hx : R ≤ ‖x‖) :
    logInf r R x = 0 := by
  have := bubbleCutoff_logCutoff_eq_one (0 : ℂ) hr hR (x := x) (by simpa using hx)
  simp [logInf, this]

lemma hasCompactSupport_logInf {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) :
    HasCompactSupport (logInf r R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => by
    simp only [mem_closedBall, dist_zero_right, not_le] at hx
    exact logInf_eq_zero hr hR hx.le

lemma logInf_mem_zeroSpace {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) :
    logInf r R ∈ zeroSpace ((⊤ : Opens ℂ) : Set ℂ) :=
  ⟨contDiff_logInf hr hR, hasCompactSupport_logInf hr hR, subset_univ _⟩

lemma norm_fderiv_logInf (r R : ℝ) (x : ℂ) :
    ‖fderiv ℝ (logInf r R) x‖ = ‖fderiv ℝ (logCutoff (0 : ℂ) r R) x‖ := by
  rw [show logInf r R = fun x => 1 - logCutoff 0 r R x from rfl, fderiv_const_sub, norm_neg]

lemma fderiv_logInf_eq_zero {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) {x : ℂ}
    (hx : ¬ (2 * r < ‖x - 0‖ ∧ ‖x - 0‖ < R)) : ‖fderiv ℝ (logInf r R) x‖ = 0 := by
  rw [norm_fderiv_logInf, bubbleTransfer_fderiv_logCutoff_eq_zero (0 : ℂ) hr hR hx, norm_zero]

lemma norm_fderiv_logInf_le {r R : ℝ} (hr : 0 < r) (hR : 2 * r < R) (x : ℂ) :
    ‖fderiv ℝ (logInf r R) x‖ ≤ logCutoffConst / (Real.log (R / (2 * r)) * ‖x - 0‖) := by
  rw [norm_fderiv_logInf]; exact bubbleCutoff_fderiv_logCutoff_le (0 : ℂ) hr hR x

/-- **Energy of the logarithmic cutoff at infinity**:
`∫ ‖∇ logInf r R‖² ≤ 2π C² / log (R/(2r))`. -/
theorem integral_norm_fderiv_logInf_sq_le {r R : ℝ} (hr : 0 < r) (h2R : 2 * r < R) :
    ∫ x, ‖fderiv ℝ (logInf r R) x‖ ^ 2 ≤
      2 * Real.pi * logCutoffConst ^ 2 / Real.log (R / (2 * r)) := by
  set L := Real.log (R / (2 * r)) with hL
  have hLpos : 0 < L := bubbleCutoff_log_pos hr h2R
  set C := logCutoffConst
  have hC : (0 : ℝ) ≤ C := by simp [C, logCutoffConst]
  set A : Set ℂ := {x : ℂ | 2 * r < ‖x - 0‖ ∧ ‖x - 0‖ < R}
  have hcont : Continuous fun x : ℂ => ‖x - 0‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hA : MeasurableSet A := (isOpen_lt continuous_const hcont).measurableSet.inter
      (isOpen_lt hcont continuous_const).measurableSet
  set G : ℂ → ℝ := fun x => ‖fderiv ℝ (logInf r R) x‖ ^ 2
  set F : ℂ → ℝ := fun x => C ^ 2 / L ^ 2 * (‖x - 0‖ ^ 2)⁻¹
  have hG0 : ∀ x, x ∉ A → G x = 0 := fun x hx => by
    simp only [G, fderiv_logInf_eq_zero hr h2R hx]; norm_num
  have hGA : ∀ x ∈ A, G x ≤ F x := fun x hx => by
    have hpos : 0 < ‖x - 0‖ := by have := hx.1; linarith
    have hb := norm_fderiv_logInf_le hr h2R x
    simp only [G, F]
    calc ‖fderiv ℝ (logInf r R) x‖ ^ 2 ≤ (C / (L * ‖x - 0‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = C ^ 2 / L ^ 2 * (‖x - 0‖ ^ 2)⁻¹ := by field_simp
  have hGm : Measurable G :=
    ((measurable_fderiv ℝ (logInf r R)).norm.pow_const 2)
  have hFm : Measurable F := by
    simp only [F]; fun_prop
  have h2r : (0 : ℝ) < 2 * r := by linarith
  have hFb : ∀ x, 2 * r < ‖x - 0‖ → ‖F x‖ ≤ C ^ 2 / L ^ 2 * ((2 * r) ^ 2)⁻¹ := fun x hx => by
    have hpos : (0 : ℝ) < ‖x - 0‖ ^ 2 := pow_pos (h2r.trans hx) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) (by positivity)
    exact pow_le_pow_left₀ h2r.le hx.le 2
  obtain ⟨hpolar, -⟩ := annulus_polar_integral hFm (0 : ℂ) h2r h2R (by positivity) hFb
  have hFi : IntegrableOn F A := by
    refine Measure.integrableOn_of_bounded (M := C ^ 2 / L ^ 2 * ((2 * r) ^ 2)⁻¹) ?_
      hFm.aestronglyMeasurable ?_
    · have hsub : A ⊆ closedBall (0 : ℂ) R := fun x hx => by
        have h2 : ‖x - 0‖ < R := hx.2
        rw [mem_closedBall, dist_eq_norm]; exact h2.le
      exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne
    · exact (ae_restrict_iff' hA).2 (ae_of_all _ fun x hx => hFb x hx.1)
  have hGint : ∫ x, G x = ∫ x in A, G x := by
    rw [← integral_indicator hA]
    congr 1; funext x
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx, hG0 x hx]
  have hGle : ∫ x in A, G x ≤ ∫ x in A, F x := by
    refine setIntegral_mono_on ?_ hFi hA hGA
    refine hFi.mono' hGm.aestronglyMeasurable
      ((ae_restrict_iff' hA).2 (ae_of_all _ fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hGA x hx
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ρ * ∫ θ in (-Real.pi)..Real.pi, F (circleMap 0 ρ θ) =
      2 * Real.pi * (C ^ 2 / L ^ 2) * ρ⁻¹ := fun ρ hρ => by
    have : ∀ θ, F (circleMap 0 ρ θ) = C ^ 2 / L ^ 2 * (ρ ^ 2)⁻¹ := fun θ => by
      simp [F, abs_of_pos hρ]
    simp only [this, intervalIntegral.integral_const, smul_eq_mul]
    field_simp; ring
  have hval : ∫ ρ in (2 * r)..R, ρ * ∫ θ in (-Real.pi)..Real.pi, F (circleMap 0 ρ θ) =
      2 * Real.pi * (C ^ 2 / L ^ 2) * L := by
    rw [intervalIntegral.integral_congr (g := fun ρ => 2 * Real.pi * (C ^ 2 / L ^ 2) * ρ⁻¹)
      fun ρ hρ => hcirc ρ (by
        rw [Set.uIcc_of_le h2R.le] at hρ; linarith [hρ.1])]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h2r (by linarith)]
  calc ∫ x, ‖fderiv ℝ (logInf r R) x‖ ^ 2 = ∫ x in A, G x := hGint
    _ ≤ ∫ x in A, F x := hGle
    _ = 2 * Real.pi * (C ^ 2 / L ^ 2) * L := by rw [hpolar, hval]
    _ = 2 * Real.pi * C ^ 2 / L := by field_simp

end MarkovGermVer
end LQGMetric
