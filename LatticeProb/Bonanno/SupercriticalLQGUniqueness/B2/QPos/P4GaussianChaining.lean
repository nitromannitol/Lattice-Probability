/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4GaussianChaining at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.FerniqueFinite
import Mathlib.Tactic

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric

namespace SupercriticalLQGUniqueness.B2.QPos

 







theorem gaussian_box_max_expectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (hN : 0 < N) (X : Ω → Fin N → ℝ)
    (hX : HasGaussianLaw X μ)
    (h0 : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (p : Fin N → Fin 2 → ℝ) {v L : ℝ}
    (hv : 0 ≤ v) (hL : 0 < L)
    (hdiam : ∀ i j, ‖p i - p j‖ ≤ 3 * L)
    (hinc : ∀ i j,
      ∫ ω, (X ω i - X ω j) ^ 2 ∂μ ≤ v * ‖p i - p j‖ / L) :
    ∫ ω, ⨆ i, X ω i ∂μ ≤
      20 * Real.sqrt 5 * Real.sqrt (v / L) *
        Real.sqrt ((2 + 1 : ℝ) * (3 * L)) := by
  have hL0 : 0 ≤ v / L := div_nonneg hv hL.le
  have hinc' (i j : Fin N) :
      ∫ ω, (X ω i - X ω j) ^ 2 ∂μ ≤
        Real.sqrt (v / L) ^ 2 * ‖p i - p j‖ := by
    rw [Real.sq_sqrt hL0]
    calc
      _ ≤ v * ‖p i - p j‖ / L := hinc i j
      _ = v / L * ‖p i - p j‖ := by ring
  simpa only [Nat.cast_ofNat] using
    (LQGMetric.SupTail.integral_iSup_finVec_le hN hX h0 p
      (Real.sqrt_nonneg _) hdiam hinc')

 




theorem gaussian_box_max_expectation_uniform
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N : ℕ} (hN : 0 < N) (X : Ω → Fin N → ℝ)
    (hX : HasGaussianLaw X μ)
    (h0 : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (p : Fin N → Fin 2 → ℝ) {v L : ℝ}
    (hv : 0 ≤ v) (hL : 0 < L)
    (hdiam : ∀ i j, ‖p i - p j‖ ≤ 3 * L)
    (hinc : ∀ i j,
      ∫ ω, (X ω i - X ω j) ^ 2 ∂μ ≤ v * ‖p i - p j‖ / L) :
    ∫ ω, ⨆ i, X ω i ∂μ ≤ 60 * Real.sqrt 5 * Real.sqrt v := by
  have hmain := gaussian_box_max_expectation μ hN X hX h0 p hv hL hdiam hinc
  have hL0 : 0 ≤ v / L := div_nonneg hv hL.le
  have hprod : Real.sqrt (v / L) * Real.sqrt (9 * L) =
      3 * Real.sqrt v := by
    calc
      _ = Real.sqrt ((v / L) * (9 * L)) :=
        (Real.sqrt_mul hL0 _).symm
      _ = Real.sqrt (9 * v) := by
        congr 1
        field_simp
      _ = 3 * Real.sqrt v := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  have heq : (2 + 1 : ℝ) * (3 * L) = 9 * L := by ring
  rw [heq] at hmain
  calc
    _ ≤ 20 * Real.sqrt 5 * Real.sqrt (v / L) * Real.sqrt (9 * L) := hmain
    _ = 60 * Real.sqrt 5 * Real.sqrt v := by
      rw [mul_assoc (20 * Real.sqrt 5) (Real.sqrt (v / L))
        (Real.sqrt (9 * L)), hprod]
      ring

end SupercriticalLQGUniqueness.B2.QPos
