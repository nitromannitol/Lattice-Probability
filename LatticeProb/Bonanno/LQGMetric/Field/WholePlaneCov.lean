import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar

/-!
# The whole-plane covariance kernel and its centred form

The covariance kernel of the whole-plane Gaussian free field, normalised at scale one, is
`wholePlaneCov z w = log (max ‖z‖ 1 * max ‖w‖ 1 / ‖z - w‖)` (normalisation as in
Duplantier–Miller–Sheffield). It is the logarithmic kernel `-log ‖z - w‖` plus the two cutoff
terms `log (max ‖z‖ 1)` and `log (max ‖w‖ 1)`. The Lean value on the diagonal is `log (· / 0) = 0`;
the diagonal is Lebesgue-null, so it does not affect any integral below.

For continuous compactly supported `φ`, `ψ` with `∫ φ = 0` and `∫ ψ = 0`, the cutoff terms
integrate to zero, so the whole-plane pairing equals the logarithmic covariance `logCov φ ψ`
of Statement/GFF (the centred logarithmic potential form, Armitage–Gardiner).
-/

open MeasureTheory Set Filter Topology

namespace LatticeProb

/-- The whole-plane Gaussian free field covariance kernel at scale one,
`log (max ‖z‖ 1 * max ‖w‖ 1 / ‖z - w‖)`, in the normalisation of Duplantier–Miller–Sheffield.
On the diagonal the value is the junk value `log (· / 0) = 0`; the diagonal is Lebesgue-null. -/
noncomputable def wholePlaneCov (z w : ℂ) : ℝ :=
  Real.log (max ‖z‖ 1 * max ‖w‖ 1 / ‖z - w‖)

lemma max_norm_pos (z : ℂ) : 0 < max ‖z‖ 1 :=
  lt_of_lt_of_le one_pos (le_max_right _ _)

/-- Off the diagonal the whole-plane kernel is the logarithmic kernel `-log ‖z - w‖` plus the two
cutoff terms `log (max ‖z‖ 1)` and `log (max ‖w‖ 1)`. -/
lemma wholePlaneCov_eq_of_ne {z w : ℂ} (h : z ≠ w) :
    wholePlaneCov z w = -Real.log ‖z - w‖ + Real.log (max ‖z‖ 1) + Real.log (max ‖w‖ 1) := by
  have hd : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  unfold wholePlaneCov
  rw [Real.log_div (mul_ne_zero (max_norm_pos z).ne' (max_norm_pos w).ne') hd,
    Real.log_mul (max_norm_pos z).ne' (max_norm_pos w).ne']
  ring

/-- The cutoff term `z ↦ log (max ‖z‖ 1)` is continuous. -/
lemma continuous_log_max_norm : Continuous fun z : ℂ => Real.log (max ‖z‖ 1) :=
  Continuous.log (continuous_norm.max continuous_const) fun z => (max_norm_pos z).ne'

/-- Inner integral of the whole-plane kernel against a continuous compactly supported `ψ`:
the logarithmic potential of `ψ` at `x`, plus the cutoff term at `x` times `∫ ψ`, plus the
integral of the cutoff term against `ψ`. The diagonal `{x}` is Lebesgue-null. -/
lemma integral_wholePlaneCov_mul {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (x : ℂ) :
    ∫ y, wholePlaneCov x y * ψ y =
      (∫ y, -Real.log ‖x - y‖ * ψ y) + (∫ y, Real.log (max ‖x‖ 1) * ψ y)
        + ∫ y, Real.log (max ‖y‖ 1) * ψ y := by
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x :=
    compl_mem_ae_iff.mpr (measure_singleton x)
  have hpt : ∫ y, wholePlaneCov x y * ψ y =
      ∫ y, ((-Real.log ‖x - y‖ * ψ y + Real.log (max ‖x‖ 1) * ψ y)
        + Real.log (max ‖y‖ 1) * ψ y) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [wholePlaneCov_eq_of_ne hy.symm]
    ring
  have hK : Integrable (fun y => -Real.log ‖x - y‖ * ψ y) := by
    refine ((QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hψ hψc x).neg).congr
      (ae_of_all _ fun y => ?_)
    show -(Real.log ‖y - x‖ * ψ y) = -Real.log ‖x - y‖ * ψ y
    rw [norm_sub_rev x y, neg_mul]
  have hc : Integrable (fun y => Real.log (max ‖x‖ 1) * ψ y) :=
    (hψ.integrable_of_hasCompactSupport hψc).const_mul _
  have hm : Integrable (fun y => Real.log (max ‖y‖ 1) * ψ y) :=
    (continuous_log_max_norm.mul hψ).integrable_of_hasCompactSupport (hψc.mul_left)
  have hKc : Integrable (fun y => -Real.log ‖x - y‖ * ψ y + Real.log (max ‖x‖ 1) * ψ y) :=
    hK.add hc
  rw [hpt, integral_add hKc hm, integral_add hK hc]

/-- Pulling a constant out of an integral with `∫ φ = 0`: the constant `c` in `L x + c` drops out.
If `φ L` is not integrable both sides vanish. -/
lemma integral_mul_add_const_of_integral_eq_zero {φ : ℂ → ℝ} (hφ : Integrable φ)
    (hφ0 : ∫ x, φ x = 0) (L : ℂ → ℝ) (c : ℝ) :
    ∫ x, φ x * (L x + c) = ∫ x, φ x * L x := by
  by_cases hf : Integrable (fun x => φ x * L x)
  · have hg : Integrable (fun x => φ x * c) := hφ.mul_const c
    simp_rw [mul_add]
    rw [integral_add hf hg, integral_mul_const, hφ0, zero_mul, add_zero]
  · have hfg : ¬ Integrable (fun x => φ x * L x + φ x * c) := by
      intro h
      exact hf ((h.sub (hφ.mul_const c)).congr (ae_of_all _ fun x => by simp))
    simp_rw [mul_add]
    rw [integral_undef hfg, integral_undef hf]

/-- Centred form of the whole-plane covariance. For continuous compactly supported `φ`, `ψ` with
`∫ φ = 0` and `∫ ψ = 0`, the whole-plane pairing equals the logarithmic covariance `logCov φ ψ`. -/
theorem integral_integral_wholePlaneCov_mul_eq_logCov {φ ψ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hφ0 : ∫ z, φ z = 0) (hψ0 : ∫ z, ψ z = 0) :
    ∫ x, ∫ y, φ x * wholePlaneCov x y * ψ y = LQGMetric.logCov φ ψ := by
  have hinner : ∀ x, ∫ y, φ x * wholePlaneCov x y * ψ y
      = φ x * ((∫ y, -Real.log ‖x - y‖ * ψ y) + ∫ y, Real.log (max ‖y‖ 1) * ψ y) := by
    intro x
    have h1 : ∫ y, φ x * wholePlaneCov x y * ψ y = φ x * ∫ y, wholePlaneCov x y * ψ y := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    have hcut : ∫ y, Real.log (max ‖x‖ 1) * ψ y = 0 := by
      rw [integral_const_mul, hψ0, mul_zero]
    rw [h1, integral_wholePlaneCov_mul hψ hψc x, hcut, add_zero]
  have hlog : LQGMetric.logCov φ ψ = ∫ x, φ x * ∫ y, -Real.log ‖x - y‖ * ψ y := by
    unfold LQGMetric.logCov
    congr 1
    funext x
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  calc ∫ x, ∫ y, φ x * wholePlaneCov x y * ψ y
      = ∫ x, φ x * ((∫ y, -Real.log ‖x - y‖ * ψ y) + ∫ y, Real.log (max ‖y‖ 1) * ψ y) :=
        integral_congr_ae (ae_of_all _ hinner)
    _ = ∫ x, φ x * ∫ y, -Real.log ‖x - y‖ * ψ y :=
        integral_mul_add_const_of_integral_eq_zero (hφ.integrable_of_hasCompactSupport hφc) hφ0
          (fun x => ∫ y, -Real.log ‖x - y‖ * ψ y) (∫ y, Real.log (max ‖y‖ 1) * ψ y)
    _ = LQGMetric.logCov φ ψ := hlog.symm

/-- The centred form for the covariance test class `LQGMetric.TestC0` (smooth compactly supported
functions with zero integral). -/
theorem integral_integral_wholePlaneCov_mul_eq_logCov_testC0 (φ ψ : LQGMetric.TestC0) :
    ∫ x, ∫ y, (φ.1 : ℂ → ℝ) x * wholePlaneCov x y * (ψ.1 : ℂ → ℝ) y
      = LQGMetric.logCov (φ.1 : ℂ → ℝ) (ψ.1 : ℂ → ℝ) :=
  integral_integral_wholePlaneCov_mul_eq_logCov φ.1.contDiff.continuous φ.1.hasCompactSupport
    ψ.1.contDiff.continuous ψ.1.hasCompactSupport φ.2 ψ.2

/-- Inclusion of the covariance test class in the smooth compactly supported functions:
for `φ : LQGMetric.TestC0`, `φ` is `C^∞` with compact support and `tsupport φ ⊆ Set.univ`.
This is the defining predicate `LatticeProb.IsTestFunction Set.univ` unfolded (Analysis/
DistributionalLaplacian). The converse does not hold by the definitions: the predicate
imposes no condition on `∫ φ`. -/
theorem testC0_contDiff_hasCompactSupport (φ : LQGMetric.TestC0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.1 : ℂ → ℝ) ∧ HasCompactSupport (φ.1 : ℂ → ℝ) ∧
      tsupport (φ.1 : ℂ → ℝ) ⊆ Set.univ :=
  ⟨φ.1.contDiff, φ.1.hasCompactSupport, Set.subset_univ _⟩

end LatticeProb
