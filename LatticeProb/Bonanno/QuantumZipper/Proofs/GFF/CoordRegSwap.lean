/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.CoordRegSwap at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence

/-!
# Folded-circle smoothing commutes (helper for RC2)

`foldedCircle_bind_comm`: `fc(w,r).bind (fc(·, ρ)) = fc(w,ρ).bind (fc(·, r))`.

Both sides are the law of `foldH (w + r e^{iθ} + ρ e^{iφ})` for independent uniform angles:
the inner fold can be dropped because `foldH ∘ conj = foldH` and the uniform circle measure is
invariant under `φ ↦ −φ` (`integral_foldedCircle_foldH`), and the two angles can then be
exchanged (Fubini). Also `foldedCircle (foldH c) ρ = foldedCircle c ρ`.

Source: none — **own elementary proof** (symmetry of the uniform circle measure and Fubini).
-/

noncomputable section

open MeasureTheory Set
open scoped Real ComplexConjugate

namespace QuantumZipper
namespace CoordReg

theorem foldH_conj' (z : ℂ) : foldH (conj z) = foldH z := by
  unfold foldH
  simp only [Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy z.im 0 with h | h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]
  · have hz : conj z = z := Complex.conj_eq_iff_im.2 h
    rw [if_pos (by linarith), if_pos (by linarith), hz]
  · rw [if_neg (by linarith), if_pos (by linarith)]

theorem circleMap_conj' (c : ℂ) (ρ φ : ℝ) :
    circleMap (conj c) ρ φ = conj (circleMap c ρ (-φ)) := by
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  push_cast
  ring_nf

theorem integral_circleUnif_Ico {g : ℂ → ℝ} (hg : Measurable g) (c : ℂ) (ρ : ℝ) :
    ∫ z, g z ∂circleUnif c ρ = (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), g (circleMap c ρ θ) := by
  unfold circleUnif
  rw [integral_smul_measure,
    integral_map (measurable_circleMap c ρ).aemeasurable hg.aestronglyMeasurable,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem integral_foldedCircle_Ico {g : ℂ → ℝ} (hg : Measurable g) (c : ℂ) (ρ : ℝ) :
    ∫ z, g z ∂foldedCircle c ρ =
      (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), g (foldH (circleMap c ρ θ)) := by
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable hg.aestronglyMeasurable]
  exact integral_circleUnif_Ico (hg.comp measurable_foldH) c ρ

theorem setIntegral_Ico_eq_intervalIntegral (h : ℝ → ℝ) :
    ∫ θ in Ico 0 (2 * π), h θ = ∫ θ in (0 : ℝ)..(2 * π), h θ := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by positivity)]

theorem integral_foldedCircle_conj {g : ℂ → ℝ} (hg : Measurable g) (c : ℂ) (ρ : ℝ) :
    ∫ z, g z ∂foldedCircle (conj c) ρ = ∫ z, g z ∂foldedCircle c ρ := by
  rw [integral_foldedCircle_Ico hg, integral_foldedCircle_Ico hg]
  congr 1
  rw [setIntegral_Ico_eq_intervalIntegral, setIntegral_Ico_eq_intervalIntegral]
  simp_rw [circleMap_conj', foldH_conj']
  rw [intervalIntegral.integral_comp_neg (fun θ => g (foldH (circleMap c ρ θ))), neg_zero]
  have h := ((periodic_circleMap c ρ).comp (fun z => g (foldH z))).intervalIntegral_add_eq
    (-(2 * π)) 0
  simp only [Function.comp_def, neg_add_cancel, zero_add] at h
  exact h

theorem integral_foldedCircle_foldH {g : ℂ → ℝ} (hg : Measurable g) (c : ℂ) (ρ : ℝ) :
    ∫ z, g z ∂foldedCircle (foldH c) ρ = ∫ z, g z ∂foldedCircle c ρ := by
  unfold foldH
  split_ifs
  · rfl
  · exact integral_foldedCircle_conj hg c ρ

/-- Two finite measures with the same integrals of indicator functions are equal. -/
theorem measure_eq_of_integral_indicator {μ ν : Measure ℂ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ A, MeasurableSet A → ∫ z, A.indicator (1 : ℂ → ℝ) z ∂μ =
      ∫ z, A.indicator (1 : ℂ → ℝ) z ∂ν) : μ = ν := by
  ext A hA
  have := h A hA
  rw [integral_indicator_one hA, integral_indicator_one hA] at this
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this

theorem foldedCircle_foldH (c : ℂ) (ρ : ℝ) : foldedCircle (foldH c) ρ = foldedCircle c ρ :=
  measure_eq_of_integral_indicator fun A hA =>
    integral_foldedCircle_foldH (measurable_const.indicator hA) c ρ

theorem measurable_integral_foldedCircle {g : ℂ → ℝ} (hg : Measurable g) (ρ : ℝ) :
    Measurable fun u => ∫ v, g v ∂foldedCircle u ρ := by
  have hf : StronglyMeasurable (fun q : ℂ × ℂ => g q.2) :=
    (hg.comp measurable_snd).stronglyMeasurable
  exact (hf.integral_kernel_prod_right' (κ := SmoothConv.fcKernel ρ)).measurable

/-- The double-angle formula for the integral against `fc(w,r).bind fc(·,ρ)`. -/
theorem integral_bind_foldedCircle_eq {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ}
    (hM : ∀ z, |g z| ≤ M) (w : ℂ) (r ρ : ℝ) :
    ∫ z, g z ∂((foldedCircle w r).bind fun u => foldedCircle u ρ) =
      (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), (2 * π)⁻¹ *
        ∫ φ in Ico 0 (2 * π), g (foldH (circleMap (circleMap w r θ) ρ φ)) := by
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) (foldedCircle w r)
  have hint : Integrable g ((foldedCircle w r).bind fun u => foldedCircle u ρ) :=
    Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hM z)
  rw [(CircleFubini.integral_bind_circle (foldedCircle w r) hint).2]
  have hF := measurable_integral_foldedCircle hg ρ
  rw [integral_foldedCircle_Ico hF]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ico fun θ _ => ?_
  rw [integral_foldedCircle_foldH hg, integral_foldedCircle_Ico hg]

theorem circleMap_circleMap (w : ℂ) (r ρ θ φ : ℝ) :
    circleMap (circleMap w r θ) ρ φ = circleMap (circleMap w ρ φ) r θ := by
  simp only [circleMap]; ring

/-- **Folded-circle smoothing commutes.** -/
theorem foldedCircle_bind_comm (w : ℂ) (r ρ : ℝ) :
    ((foldedCircle w r).bind fun u => foldedCircle u ρ) =
      (foldedCircle w ρ).bind fun u => foldedCircle u r := by
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) (foldedCircle w r)
  have := CircleFubini.isFiniteMeasure_bind_circle (r := r) (foldedCircle w ρ)
  refine measure_eq_of_integral_indicator fun A hA => ?_
  have hg : Measurable (A.indicator (1 : ℂ → ℝ)) := measurable_const.indicator hA
  have hM : ∀ z, |A.indicator (1 : ℂ → ℝ) z| ≤ 1 := fun z => by
    by_cases hz : z ∈ A <;> simp [hz]
  rw [integral_bind_foldedCircle_eq hg hM, integral_bind_foldedCircle_eq hg hM]
  congr 1
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have hm : Measurable fun p : ℝ × ℝ =>
      A.indicator (1 : ℂ → ℝ) (foldH (circleMap (circleMap w r p.1) ρ p.2)) := by
    refine hg.comp (measurable_foldH.comp ?_)
    have : Continuous fun p : ℝ × ℝ => circleMap (circleMap w r p.1) ρ p.2 := by
      simp only [circleMap]; fun_prop
    exact this.measurable
  have hint : Integrable (Function.uncurry fun θ φ =>
      A.indicator (1 : ℂ → ℝ) (foldH (circleMap (circleMap w r θ) ρ φ)))
      ((volume.restrict (Ico 0 (2 * π))).prod (volume.restrict (Ico 0 (2 * π)))) := by
    haveI : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ico_lt_top.ne
    exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hM _)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun φ => integral_congr_ae (ae_of_all _ fun θ => ?_))
  show A.indicator 1 (foldH (circleMap (circleMap w r θ) ρ φ)) =
    A.indicator 1 (foldH (circleMap (circleMap w ρ φ) r θ))
  rw [circleMap_circleMap]

end CoordReg
end QuantumZipper
