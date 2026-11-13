/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.Median.Window at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Composition
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PowerWindow




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Median

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem median_power_window_exponent_of_local_bound
    (lam : ℕ → ℝ) (a : ℝ → ℝ) (ξ α C ε₀ : ℝ)
    (hξ : 0 < ξ) (hC : 0 ≤ C) (hε₀ : 0 < ε₀)
    (hlam : ∀ n, 0 < lam n)
    (ha : ∀ ε, 0 < ε → ε < ε₀ → 0 < a ε)
    (hSlope : Tendsto (fun n => Real.logb 2 (lam n) / (n : ℝ)) atTop (𝓝 (-α)))
    (hmed : ∀ ε, 0 < ε → ε < ε₀ →
      |Real.log (a ε) - Real.log (lam ⌊Real.logb (1 / 2) ε⌋₊)| ≤
        C * Real.sqrt ((⌊Real.logb (1 / 2) ε⌋₊ : ℝ) + 1) + C) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - ξ * ((1 - α) / ξ) + δ)) ≤ ENNReal.ofReal (a ε) ∧
      ENNReal.ofReal (a ε) ≤ ENNReal.ofReal (ε ^ (1 - ξ * ((1 - α) / ξ) - δ)) := by
  let b : ℝ → ℝ := fun ε =>
    if 0 < ε ∧ ε < ε₀ then a ε else if 0 < ε then lam ⌊Real.logb (1 / 2) ε⌋₊ else 1
  have hbpos : ∀ ε, 0 < ε → 0 < b ε := by
    intro ε hε
    by_cases hsmall : ε < ε₀
    · simpa [b, hε, hsmall] using ha ε hε hsmall
    · simpa [b, hε, hsmall] using hlam ⌊Real.logb (1 / 2) ε⌋₊
  have hbmed : ∀ ε, 0 < ε → ε < 1 →
      |Real.log (b ε) - Real.log (lam ⌊Real.logb (1 / 2) ε⌋₊)| ≤
        C * Real.sqrt ((⌊Real.logb (1 / 2) ε⌋₊ : ℝ) + 1) + C := by
    intro ε hε _
    by_cases hsmall : ε < ε₀
    · simpa [b, hε, hsmall] using hmed ε hε hsmall
    · have hbeq : b ε = lam ⌊Real.logb (1 / 2) ε⌋₊ := by
        simp [b, hε, hsmall]
      rw [hbeq]
      simp only [sub_self, abs_zero]
      exact add_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hC
  intro δ hδ
  have hpow := Exponent.PowerWindow.median_power_window_exponent lam b ξ α C
    hξ hC hbpos hSlope hbmed δ hδ
  filter_upwards [hpow, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε hp hε hsmall
  have hε' : 0 < ε := hε
  have hsmall' : ε < ε₀ := hsmall
  have hbeq : b ε = a ε := by simp [b, hε', hsmall']
  rwa [hbeq] at hp


 

theorem isLFPPExponent_of_dyadic_median_slope
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {W₀ : WNSpace → Ω₀ → ℝ} (hW₀ : IsWhiteNoise P₀ W₀)
    (ξ : Set.Ioi (0 : ℝ)) (α : ℝ)
    (hSlope : Tendsto
      (fun n : ℕ => Real.logb 2 (lambdaN (ξ : ℝ) W₀ P₀ n) / (n : ℝ))
      atTop (𝓝 (-α))) :
    IsLFPPExponent ξ ((1 - α) / (ξ : ℝ)) := by
  letI := hW₀.isProbabilityMeasure
  intro Ω _ P _ h hh X med hXm δ hδ
  obtain ⟨C, ε₀, hC, hε₀, hLocal⟩ :=
    exists_normalized_heat_version_median_log_bound P h hh P₀ hW₀ (ξ : ℝ)
  have hX : ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ z : ℂ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
        atTop (𝓝 (X ε ω z)) := by
    intro ε hε z
    exact (hXm ε hε).1 z
  have hAll := hLocal X hX
  let lam : ℕ → ℝ := lambdaN (ξ : ℝ) W₀ P₀
  let a : ℝ → ℝ := fun ε => (med ε).toReal
  have ha : ∀ ε, 0 < ε → ε < ε₀ → 0 < a ε := by
    intro ε hε hεsmall
    have hm := hAll ε hε hεsmall (med ε) (hXm ε hε).2
    exact ENNReal.toReal_pos hm.1.ne' hm.2.1.ne
  have hmed : ∀ ε, 0 < ε → ε < ε₀ →
      |Real.log (a ε) - Real.log (lam ⌊Real.logb (1 / 2) ε⌋₊)| ≤
        C * Real.sqrt ((⌊Real.logb (1 / 2) ε⌋₊ : ℝ) + 1) + C := by
    intro ε hε hεsmall
    have hm := (hAll ε hε hεsmall (med ε) (hXm ε hε).2).2.2
    simpa only [a, lam, Exponent.PowerWindow.logb_half_eq_logb_two_inv] using hm
  have hpow := median_power_window_exponent_of_local_bound lam a
    (ξ : ℝ) α C ε₀ ξ.property hC.le hε₀
    (fun n => lambdaN_pos hW₀ n) ha hSlope hmed δ hδ
  filter_upwards [hpow, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε hp hε hεsmall
  have hε' : 0 < ε := hε
  have hεsmall' : ε < ε₀ := hεsmall
  have hm := hAll ε hε' hεsmall' (med ε) (hXm ε hε').2
  have heq : ENNReal.ofReal (med ε).toReal = med ε :=
    ENNReal.ofReal_toReal hm.2.1.ne
  simpa only [a, heq] using hp


end SupercriticalLQGUniqueness.Exponent.Median
