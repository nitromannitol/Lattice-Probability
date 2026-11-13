/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLFPPAS.Field.LocalizedExponentContinuity at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedApproximation
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Cont
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# Dependence on the localization exponent

The localized field is jointly continuous in its cutoff radius, including when that radius is
written as δ (log δ⁻¹)^q and q varies.  This adapter is used to pass from the existing
fixed-exponent polar formula on a countable dense family to the radius-uniform estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Field

private def exponentKernel (δ t : ℝ) (z : ℂ) (q : ℝ) (w : ℂ) : ℝ :=
  LQGMetric.DFGPS.locProf (2 * (Real.log δ + q * Real.log t)) (z - w) *
    LQGMetric.heatKernel (δ ^ 2 / 2) z w

private lemma plRad_exponent_formula {δ t q : ℝ} (ht : 0 < t)
    (htδ : t = Real.log δ⁻¹) :
    plRad q δ = δ * Real.exp (q * Real.log t) := by
  rw [plRad, ← htδ, Real.rpow_def_of_pos ht]
  ring_nf

lemma log_plRad_sq_formula {δ t q : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (ht : 1 < t) (htδ : t = Real.log δ⁻¹) :
    Real.log (plRad q δ ^ 2) = 2 * (Real.log δ + q * Real.log t) := by
  have hrad := plRad_exponent_formula (by linarith) htδ (q := q)
  have hrad' : plRad q δ = Real.exp (Real.log δ + q * Real.log t) := by
    rw [hrad, ← Real.exp_log hδ.1, ← Real.exp_add]
    simp only [Real.log_exp]
  rw [hrad', ← Real.exp_nat_mul]
  simp only [Real.log_exp]
  ring

private lemma exponentKernel_contDiff (δ t : ℝ) (z : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => exponentKernel δ t z p.1 p.2) := by
  have hcoord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => (2 * (Real.log δ + p.1 * Real.log t), z - p.2)) := by
    fun_prop
  exact (LQGMetric.DFGPS.contDiff_locProf.comp hcoord).mul
    ((LQGMetric.LFPP.contDiff_heatKernel_left (δ ^ 2 / 2) z).comp contDiff_snd)

/-- Pairing a fixed distribution with the localized test varies continuously with the PL exponent.
The restriction radius is locally bounded, so this is continuity in the test-function topology. -/
theorem continuousAt_plPairing_exponent {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hlog : 1 < Real.log δ⁻¹) (h : DistC) (z : ℂ) (q₀ : ℝ) :
    ContinuousAt (fun q => h (plTest q δ hδ z)) q₀ := by
  let t := Real.log δ⁻¹
  have htδ : t = Real.log δ⁻¹ := rfl
  have ht : 1 < t := hlog
  have hRt : 0 < Real.log t := Real.log_pos ht
  let R := δ * Real.exp ((|q₀| + 1) * Real.log t)
  have hR : 0 < R := by
    change 0 < δ * Real.exp ((|q₀| + 1) * Real.log t)
    exact mul_pos hδ.1 (Real.exp_pos _)
  let K : TopologicalSpace.Compacts ℂ := ⟨closedBall z R, isCompact_closedBall _ _⟩
  let X := closedBall q₀ 1
  let Ψ : ℝ × ℂ → ℂ → ℝ := fun p w => exponentKernel δ t z p.1 w
  have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry Ψ) := by
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℂ) × ℂ => (p.1.1, p.2)) := by fun_prop
    exact (exponentKernel_contDiff δ t z).comp hmap
  have hs : ∀ x : X, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ (x.1, 0)) := by
    intro x
    exact (exponentKernel_contDiff δ t z).comp
      (contDiff_const.prodMk contDiff_id)
  have hzero : ∀ x : X, ∀ w ∉ (K : Set ℂ), Ψ (x.1, 0) w = 0 := by
    intro x w hw
    have hx : |x.1 - q₀| ≤ 1 := by
      have hx0 : dist x.1 q₀ ≤ 1 := x.2
      simpa only [Real.dist_eq] using hx0
    have hx' : |x.1| ≤ |q₀| + 1 := by
      calc |x.1| = |(x.1 - q₀) + q₀| := by ring_nf
        _ ≤ |x.1 - q₀| + |q₀| := abs_add_le _ _
        _ ≤ |q₀| + 1 := by linarith
    have hrad : plRad x.1 δ ≤ R := by
      rw [plRad_exponent_formula (by linarith) htδ (q := x.1)]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (le_trans (le_abs_self x.1) hx') hRt.le)) hδ.1.le
    have hw' : R < ‖z - w‖ := by
      change w ∉ closedBall z R at hw
      rw [mem_closedBall, dist_eq_norm, not_le] at hw
      simpa only [norm_sub_rev] using hw
    have heq := log_plRad_sq_formula hδ hlog htδ (q := x.1)
    have hbump := plBump_eq_locProf x.1 δ hδ (z - w)
    change LQGMetric.DFGPS.locProf
      (2 * (Real.log δ + x.1 * Real.log (Real.log δ⁻¹))) (z - w) *
        LQGMetric.heatKernel (δ ^ 2 / 2) z w = 0
    rw [← heq, ← hbump, plBump_eq_zero x.1 δ hδ]
    · simp
    · exact hrad.trans hw'.le
  have hD : ∀ i : ℕ, Continuous fun p : X × ℂ =>
      iteratedFDeriv ℝ i (Ψ (p.1.1, 0)) p.2 := by
    intro i
    have hc := LQGMetric.DFGPS.continuous_iteratedFDeriv_snd_rc hΨ i
    have hmap : Continuous fun p : X × ℂ => ((p.1.1, (0 : ℂ)), p.2) := by fun_prop
    exact hc.comp hmap
  have hc := LQGMetric.continuous_testFamK K (fun x : X => Ψ (x.1, 0)) hs hzero hD
  have he : (fun x : X => plTest x.1 δ hδ z) =
      (LQGMetric.ofSuppC K) ∘
        LQGMetric.testFamK K (fun x : X => Ψ (x.1, 0)) hs hzero := by
    funext x
    ext w
    rw [plTest_apply, plBump_eq_locProf,
      log_plRad_sq_formula hδ hlog htδ (q := x.1)]
    rfl
  have hB : Continuous fun x : X => plTest x.1 δ hδ z := by
    rw [he]
    exact (LQGMetric.ofSuppC K).continuous.comp hc
  have hval : Continuous fun x : X => h (plTest x.1 δ hδ z) :=
    (map_continuous h).comp hB
  exact (continuousOn_iff_continuous_domRestrict.2 hval).continuousAt
    (closedBall_mem_nhds q₀ one_pos)

/-- The normalizing mass also varies continuously with the localization exponent. -/
theorem continuousAt_plZ_exponent {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hlog : 1 < Real.log δ⁻¹) (q₀ : ℝ) :
    ContinuousAt (fun q => plZ q δ hδ) q₀ := by
  let one : C(ℂ, ℝ) := ContinuousMap.const ℂ 1
  have h := continuousAt_plPairing_exponent hδ hlog (LQGMetric.ofCont one) 0 q₀
  have heq : (fun q => (LQGMetric.ofCont one) (plTest q δ hδ 0)) =
      fun q => plZ q δ hδ := by
    funext q
    rw [LQGMetric.ofCont_apply, plZ]
    simp [one]
  rw [heq] at h
  exact h

/-- At fixed positive scale the normalized localized field is continuous in its cutoff exponent. -/
theorem continuousAt_plMollify_exponent {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hlog : 1 < Real.log δ⁻¹) (h : DistC) (z : ℂ) (q₀ : ℝ) :
    ContinuousAt (fun q => plMollify q δ hδ h z) q₀ := by
  have hnum := continuousAt_plPairing_exponent hδ hlog h z q₀
  have hden := continuousAt_plZ_exponent hδ hlog q₀
  have hpos : plZ q₀ δ hδ ≠ 0 := (plZ_pos q₀ δ hδ).ne'
  have hinv : ContinuousAt (fun q => (plZ q δ hδ)⁻¹) q₀ := hden.inv₀ hpos
  change ContinuousAt
    ((fun q : ℝ => (plZ q δ hδ)⁻¹) * (fun q => h (plTest q δ hδ z))) q₀
  exact hinv.mul hnum

end SupercriticalLFPPAS.Field
