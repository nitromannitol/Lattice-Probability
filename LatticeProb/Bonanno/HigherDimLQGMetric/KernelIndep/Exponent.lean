/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.Exponent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.KernelIndep

/-! Existence and uniqueness of the kernel-independent distance exponent. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Real
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion IsLFPPExponent)

/-- `distExp` takes the genuine existence branch. -/
theorem distExp_isDistanceExponent {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) :
    IsDistanceExponent d ξ (distExp d ξ) := by
  obtain ⟨κ₀, hκ₀⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨lam₀, h₀⟩ := exists_isExponentFor hd hκ₀ hξ
  have hex : ∃ Q : ℝ, IsDistanceExponent d ξ Q := by
    refine ⟨(1 - lam₀) / ξ, ?_⟩
    intro κ hκ Ω _ P W hW H hH
    obtain ⟨lam, hlam⟩ := exists_isExponentFor hd hκ hξ
    have heq := kernel_indep hd hκ₀ hκ hξ h₀ hlam
    have hexp := hlam Ω P W hW H hH
    convert hexp using 1
    rw [← heq]
    field_simp
    ring
  unfold distExp
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

/-- Any kernel-specific exponent computes `distExp`. -/
theorem distExp_eq_of_isExponentFor {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {lam : ℝ}
    (h : IsExponentFor d κ ξ lam) :
    distExp d ξ = (1 - lam) / ξ := by
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  let P : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
  haveI := hW.isProbabilityMeasure
  obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
  have h₁ := h _ P W hW H hH
  have h₂ := (distExp_isDistanceExponent hd hξ) κ hκ _ P W hW H hH
  have heq := isLFPPExponent_unique h₁ h₂
  have hξne : ξ ≠ 0 := hξ.ne'
  apply (eq_div_iff hξne).2
  nlinarith

/-- The iff statement used to seal the frozen sanity anchor. -/
theorem distExp_spec_proof :
    ∀ (d : ℕ), 2 ≤ d → ∀ ξ : ℝ, 0 < ξ → ∀ Q : ℝ,
      IsDistanceExponent d ξ Q ↔ Q = distExp d ξ := by
  intro d hd ξ hξ Q
  constructor
  · intro hQ
    obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
    obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
    let P : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP
    haveI := hW.isProbabilityMeasure
    obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
    have h₁ := hQ κ hκ _ P W hW H hH
    have h₂ := (distExp_isDistanceExponent hd hξ) κ hκ _ P W hW H hH
    have heq := isLFPPExponent_unique h₁ h₂
    nlinarith
  · intro hQ
    rw [hQ]
    exact distExp_isDistanceExponent hd hξ

end HigherDimLQGMetric
