/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenLower4Trunc at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower4

/-!
# GFF-K3, node H5 (continued): truncated Green potentials as test functions

`tpot φ δ = trunc δ ∘ gpot φ` lies in `zeroSpace H` (`tpot_mem_zeroSpace`) and satisfies
`E_H(tpot φ δ) ≤ ∫ tpot φ δ · φ` (`energy_tpot_le`). Consequently (`kernelCov_densMeas_le`):
if `∫ f dσ ≤ C √E_H(f)` for all `f ∈ zeroSpace H`, then `B(σ, σ) ≤ C²` for `σ = densMeas φ`.
Route and sources: see the docstring of `GreenLower4` (Adams–Hedberg 1996, Thm 3.3.1, contraction
principle; the combination with the weak equation is our own short argument).
-/

noncomputable section

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

variable {φ : ℂ → ℝ} {ε : ℝ}

/-- The truncated Green potential `trunc δ ∘ gpot φ`. -/
def tpot (φ : ℂ → ℝ) (δ : ℝ) (x : ℂ) : ℝ := trunc δ (gpot φ x)

theorem tpot_mem_zeroSpace (hφ : GoodDens φ ε) {δ : ℝ} (hδ : 0 < δ) :
    tpot φ δ ∈ zeroSpace H := by
  obtain ⟨R, hR⟩ := exists_gpot_lt hφ hδ
  have hgc : Continuous (gpot φ) := (contDiff_gpot hφ).continuous
  have hsub : Function.support (tpot φ δ) ⊆ {x | δ ≤ gpot φ x} := fun x hx => by
    by_contra h
    exact hx (trunc_eq_zero hδ (not_le.mp h).le)
  have hts : tsupport (tpot φ δ) ⊆ {x | δ ≤ gpot φ x} :=
    closure_minimal hsub (isClosed_le continuous_const hgc)
  refine ⟨(contDiff_trunc δ).comp (contDiff_gpot hφ), ?_, ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact trunc_eq_zero hδ (hR x hx).le
  · intro x hx
    have h1 : δ ≤ gpot φ x := hts hx
    show 0 < x.im
    by_contra h
    linarith [gpot_nonpos hφ (not_lt.mp h)]

lemma integrable_gradInner_K3 {u f : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : Integrable (gradInner u f) := by
  have h : ∀ v, Integrable fun z => fderiv ℝ u z v * fderiv ℝ f z v := fun v =>
    (((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left
  exact (h 1).add (h Complex.I)

/-- **H5 (energy of the truncation).** `E_H(trunc δ ∘ u) ≤ ∫ (trunc δ ∘ u) φ`. -/
theorem energy_tpot_le (hφ : GoodDens φ ε) {δ : ℝ} (hδ : 0 < δ) :
    dirichletEnergyOn H (tpot φ δ) ≤ ∫ z, tpot φ δ z * φ z := by
  have hmem := tpot_mem_zeroSpace hφ hδ
  have hu1 : ContDiff ℝ 1 (gpot φ) := (contDiff_gpot hφ).of_le (by simp)
  have hf1 : ContDiff ℝ 1 (tpot φ δ) := hmem.1.of_le (by simp)
  rw [← weak_gpot hφ hmem, energy_eq_of_tsupport_subset hmem.2.2]
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ ?_) (by positivity)
  · simp only [norm_fderiv_sq_eq_gradInner]
    exact integrable_gradInner_K3 hf1 hf1 hmem.2.1
  · exact integrable_gradInner_K3 hu1 hf1 hmem.2.1
  · intro z
    show ‖fderiv ℝ (tpot φ δ) z‖ ^ 2 ≤ gradInner (gpot φ) (tpot φ δ) z
    rw [norm_fderiv_sq_eq_gradInner]
    have hd := (hu1.differentiable one_ne_zero) z
    have e : ∀ v, fderiv ℝ (tpot φ δ) z v =
        Real.smoothTransition (gpot φ z / δ - 1) * fderiv ℝ (gpot φ) z v :=
      fun v => fderiv_trunc_comp hd δ v
    simp only [gradInner, e]
    set s := Real.smoothTransition (gpot φ z / δ - 1)
    have hs0 : 0 ≤ s := Real.smoothTransition.nonneg _
    have hs1 : s ≤ 1 := Real.smoothTransition.le_one _
    set a := fderiv ℝ (gpot φ) z 1
    set b := fderiv ℝ (gpot φ) z Complex.I
    nlinarith [mul_nonneg (mul_nonneg hs0 (sub_nonneg.2 hs1)) (add_nonneg (sq_nonneg a) (sq_nonneg b))]

/-- **H5 (lower bound for smooth densities).** If `∫ f dσ ≤ C √E_H(f)` on `zeroSpace H`, then
`B(σ, σ) ≤ C²`, for `σ = densMeas φ`. -/
theorem kernelCov_densMeas_le (hφ : GoodDens φ ε) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ f ∈ zeroSpace H, ∫ x, f x ∂densMeas φ ≤ C * Real.sqrt (dirichletEnergyOn H f)) :
    kernelCov greenH (densMeas φ) (densMeas φ) ≤ C ^ 2 := by
  have hφc := hφ.smooth.continuous
  have hgc : Continuous (gpot φ) := (contDiff_gpot hφ).continuous
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.compact
  have hB : kernelCov greenH (densMeas φ) (densMeas φ) = ∫ z, φ z * gpot φ z :=
    integral_densMeas hφ (gpot φ)
  set M := ∫ z, φ z with hM
  have hM0 : 0 ≤ M := integral_nonneg hφ.nonneg
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ := η / (2 * M + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδeq : δ * (2 * M + 1) = η := div_mul_cancel₀ η (by positivity)
  have hmem := tpot_mem_zeroSpace hφ hδ
  have hE := energy_tpot_le hφ hδ
  have hle := h _ hmem
  rw [integral_densMeas hφ] at hle
  set a := ∫ z, φ z * tpot φ δ z with ha
  have hcomm : ∫ z, tpot φ δ z * φ z = a := by
    rw [ha]; congr 1; funext z; exact mul_comm _ _
  rw [hcomm] at hE
  have ha0 : 0 ≤ a := integral_nonneg fun z => mul_nonneg (hφ.nonneg z) (trunc_nonneg hδ _)
  have haC : a ≤ C ^ 2 := by
    have h1 : a ≤ C * Real.sqrt a :=
      hle.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hC)
    set r := Real.sqrt a
    have hr0 : 0 ≤ r := Real.sqrt_nonneg a
    have hra : r ^ 2 = a := Real.sq_sqrt ha0
    rw [← hra] at h1 ⊢
    rcases hr0.eq_or_lt with h0 | h0
    · rw [← h0, zero_pow two_ne_zero]; positivity
    · have : r ≤ C := by nlinarith
      exact pow_le_pow_left₀ hr0 this 2
  have ig : Integrable fun z => φ z * gpot φ z :=
    (hφc.mul hgc).integrable_of_hasCompactSupport hφ.compact.mul_right
  have it : Integrable fun z => φ z * tpot φ δ z :=
    (hφc.mul ((contDiff_trunc δ).continuous.comp hgc)).integrable_of_hasCompactSupport
      hφ.compact.mul_right
  have hlow : (∫ z, φ z * gpot φ z) - M * (2 * δ) ≤ a := by
    rw [hM, ← integral_mul_const, ← integral_sub ig (hφi.mul_const _)]
    refine integral_mono (ig.sub (hφi.mul_const _)) it fun z => ?_
    show φ z * gpot φ z - φ z * (2 * δ) ≤ φ z * trunc δ (gpot φ z)
    have h1 := sub_le_trunc hδ (gpot φ z)
    have h2 := hφ.nonneg z
    nlinarith
  have h2 : M * (2 * δ) ≤ η := by nlinarith
  rw [hB]
  linarith

end QuantumZipper.K3
