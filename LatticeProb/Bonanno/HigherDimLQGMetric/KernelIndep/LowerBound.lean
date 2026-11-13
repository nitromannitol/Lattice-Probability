/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.LowerBound at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.BandAsymptotic

/-! Sharp elementary lower bound on the distance exponent and nonempty subcritical interval. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Real
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion IsLFPPExponent)

/-- The elementary bound `Q(ξ) ≥ 1/ξ - √(2d)`. -/
theorem distExp_ge {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    1 / ξ - Real.sqrt (2 * d) ≤ distExp d ξ := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨lam, hlam⟩ := exists_isExponentFor hd hκ hξ
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  let P : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  haveI := hW.isProbabilityMeasure
  obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
  have he : IsLFPPExponent H P ξ lam := hlam _ P W hW H hH
  have hlamle : lam ≤ ξ * Real.sqrt (2 * d) := by
    apply limit_le_of_upper_tails he
    intro A hA
    exact band_logDistance_upper_tail hd hκ hW hH hξ hA
  rw [distExp_eq_of_isExponentFor hd hξ hκ hlam]
  apply (le_div_iff₀ hξ).2
  calc (1 / ξ - Real.sqrt (2 * d)) * ξ =
      1 - ξ * Real.sqrt (2 * d) := by field_simp
    _ ≤ 1 - lam := by linarith

/-- The interval of sufficiently small `ξ` is subcritical. -/
theorem exists_subcritical_range {d : ℕ} (hd : 2 ≤ d) :
    ∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀,
      Real.sqrt (2 * d) < distExp d ξ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  refine ⟨1 / (2 * Real.sqrt (2 * d)), by positivity, ?_⟩
  intro ξ hξ
  have hξ0 := hξ.1
  have hmul : 2 * Real.sqrt (2 * d) < 1 / ξ := by
    apply (lt_div_iff₀ hξ0).2
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (2 * d))).1 hξ.2
    simpa only [mul_comm] using hh
  have hbound := distExp_ge hd hξ0
  linarith

end HigherDimLQGMetric
