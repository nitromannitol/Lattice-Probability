/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.Coupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.SegCombLaw
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.F2WedgeCoupleFree

/-!
# The coupling of DG Lemma 2.5: `h̃ = ξ̃⁻¹(ξ h + √(ξ̃² − ξ²) h′)`

Ding–Gwynne, arXiv:1807.01072, Lemma 2.5 (`lem-lfpp-mono`, DG:736–745), proof (DG:747–750):
"Let `h′` be an independent GFF with the same law as `h`. Then the field
`h̃ := ξ̃⁻¹(ξ h + √(ξ̃² − ξ²) h′)` has the same law as `h`, as can be seen by computing
`E[(h̃,f)(h̃,g)]`." We do this at the level of circle-average processes on `Ω × Ω` with
`P ⊗ P`: both `hc ∘ fst` and the coupled process satisfy `LQGDimension.IsGFFCircleAverage`.
Product-space Gaussian tools are reused from QuantumZipper (`F2.isGaussianProcess_sumElim_prod`,
`F2.cov_fst_add_snd`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace LQGMetric
namespace DG

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hc : ℝ → ℂ → Ω → ℝ}

/-- The DG coupling `h̃ = (ξ/ξ̃) h + (√(ξ̃² − ξ²)/ξ̃) h′` on `Ω × Ω`. -/
def coupledCA (ξ ξt : ℝ) (hc : ℝ → ℂ → Ω → ℝ) (ε : ℝ) (z : ℂ) (p : Ω × Ω) : ℝ :=
  ξ / ξt * hc ε z p.1 + √(ξt ^ 2 - ξ ^ 2) / ξt * hc ε z p.2

/-- `hc ∘ fst` on `Ω × Ω`. -/
def fstCA (hc : ℝ → ℂ → Ω → ℝ) (ε : ℝ) (z : ℂ) (p : Ω × Ω) : ℝ := hc ε z p.1

lemma isGFFCircleAverage_fstCA (hG : LQGDimension.IsGFFCircleAverage hc P) :
    LQGDimension.IsGFFCircleAverage (fstCA hc) (P.prod P) := by
  have := hG.isProbabilityMeasure
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · have hZ := QuantumZipper.F2.isGaussianProcess_sumElim_prod hG.isGaussianProcess
      hG.isGaussianProcess
    exact hZ.comp_right (fun p : Ioi (0 : ℝ) × ℂ => Sum.inl p)
  · intro ε hε z
    change ∫ p, hc ε z p.1 ∂(P.prod P) = 0
    rw [integral_fun_fst, hG.integral_eq_zero ε hε z, smul_zero]
  · intro ε hε δ hδ z w
    refine (QuantumZipper.F2.cov_comp_fst (P' := P) (LQGDimension.SegLaw.memLp_slice hG hε z)
      (LQGDimension.SegLaw.memLp_slice hG hδ w)).trans ?_
    exact hG.covariance_eq ε hε δ hδ z w
  · intro ε hε p
    exact hG.continuous ε hε p.1

lemma isGFFCircleAverage_coupledCA (hG : LQGDimension.IsGFFCircleAverage hc P) {ξ ξt : ℝ}
    (hξ0 : 0 < ξ) (hξ : ξ ≤ ξt) :
    LQGDimension.IsGFFCircleAverage (coupledCA ξ ξt hc) (P.prod P) := by
  have := hG.isProbabilityMeasure
  have hξt : 0 < ξt := hξ0.trans_le hξ
  set a := ξ / ξt
  set b := √(ξt ^ 2 - ξ ^ 2) / ξt
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · classical
    have hZ := QuantumZipper.F2.isGaussianProcess_sumElim_prod hG.isGaussianProcess
      hG.isGaussianProcess
    refine hZ.of_isGaussianProcess fun p => ?_
    let I : Finset ((Ioi (0 : ℝ) × ℂ) ⊕ (Ioi (0 : ℝ) × ℂ)) := {Sum.inl p, Sum.inr p}
    let i1 : I := ⟨Sum.inl p, by simp [I]⟩
    let i2 : I := ⟨Sum.inr p, by simp [I]⟩
    exact ⟨I, a • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) i1 +
      b • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) i2, fun ω => rfl⟩
  · intro ε hε z
    have m := LQGDimension.SegLaw.memLp_slice hG hε z
    have i1 := ((m.comp_fst P).integrable one_le_two).const_mul a
    have i2 := ((m.comp_snd P).integrable one_le_two).const_mul b
    change ∫ p, (a * hc ε z p.1 + b * hc ε z p.2) ∂(P.prod P) = 0
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_fun_fst (fun x => hc ε z x), integral_fun_snd (fun x => hc ε z x),
      hG.integral_eq_zero ε hε z]
    simp
  · intro ε hε δ hδ z w
    have m1 := LQGDimension.SegLaw.memLp_slice hG hε z
    have m2 := LQGDimension.SegLaw.memLp_slice hG hδ w
    refine (QuantumZipper.F2.cov_fst_add_snd (m1.const_mul a) (m2.const_mul a) (m1.const_mul b)
      (m2.const_mul b)).trans ?_
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_mul_left, covariance_const_mul_right, hG.covariance_eq ε hε δ hδ z w]
    have hs : √(ξt ^ 2 - ξ ^ 2) ^ 2 = ξt ^ 2 - ξ ^ 2 :=
      Real.sq_sqrt (by nlinarith)
    have : a * a + b * b = 1 := by
      simp only [a, b]
      field_simp
      rw [hs]; ring
    linear_combination (LQGDimension.gffCircleCov ε z δ w) * this
  · intro ε hε p
    exact ((continuous_const.mul (hG.continuous ε hε p.1)).add
      (continuous_const.mul (hG.continuous ε hε p.2)))

end DG
end LQGMetric
