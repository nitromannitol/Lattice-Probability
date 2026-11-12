/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerG

/-!
# DDDF Lemma 6: `φ_L^{(δ)}` and `φ_H^{(δ)}` are Gaussian processes

DDDF (arXiv:1904.08021, `tightness.tex` l. 553: "`φ_L^{(δ)}` … is a smooth Gaussian field",
"`φ_H^{(δ)}` … is a smooth Gaussian field"). `φ_L(x) = √π (W(lKer x) + W'(gKer x))` with `W`, `W'`
independent white noises: the joint process `Sum.elim W W'` is Gaussian (independent Gaussian
vectors are jointly Gaussian, mathlib `IndepFun.hasGaussianLaw`; the argument is that of
QuantumZipper `isGaussianProcess_sumElim_prod`, F2WedgeCoupleFree.lean:113, on one space), and
`φ_L` is a linear image of it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two independent white noises form a jointly Gaussian process indexed by `WNSpace ⊕ WNSpace`. -/
theorem isGaussianProcess_sumElim_indep {W W' : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hW' : IsWhiteNoise P W') (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) :
    IsGaussianProcess (fun (i : WNSpace ⊕ WNSpace) ω => Sum.elim (fun f => W f ω)
      (fun g => W' g ω) i) P := by
  classical
  have := hW.isProbabilityMeasure
  constructor
  intro I
  have g₁ := hW.isGaussianProcess.hasGaussianLaw I.toLeft
  have g₂ := hW'.isGaussianProcess.hasGaussianLaw I.toRight
  have hind' : IndepFun (fun ω => I.toLeft.restrict (W · ω))
      (fun ω => I.toRight.restrict (W' · ω)) P :=
    hind.comp (Finset.measurable_restrict _) (Finset.measurable_restrict _)
  have hG := IndepFun.hasGaussianLaw g₁ g₂ hind'
  let L : ((I.toLeft → ℝ) × (I.toRight → ℝ)) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => match i with
      | ⟨Sum.inl s, h⟩ => (ContinuousLinearMap.proj
          (⟨s, Finset.mem_toLeft.2 h⟩ : I.toLeft)).comp (ContinuousLinearMap.fst ℝ _ _)
      | ⟨Sum.inr t, h⟩ => (ContinuousLinearMap.proj
          (⟨t, Finset.mem_toRight.2 h⟩ : I.toRight)).comp (ContinuousLinearMap.snd ℝ _ _)
  have e : (fun ω => I.restrict (fun i => Sum.elim (fun f => W f ω) (fun g => W' g ω) i)) =
      fun ω => L (I.toLeft.restrict (W · ω), I.toRight.restrict (W' · ω)) := by
    funext ω; funext i
    rcases i with ⟨i | i, h⟩ <;> rfl
  rw [e]
  exact hG.map_fun L

/-- **`φ_L^{(δ)}` is a Gaussian process** (DDDF l. 553). -/
theorem isGaussianProcess_phiL (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W')
    (hind : IndepFun (fun ω f => W f ω) (fun ω f => W' f ω) P) (δ : ℝ) :
    IsGaussianProcess (fun x => phiL h W W' δ x) P := by
  classical
  have hZ := isGaussianProcess_sumElim_indep hW hW' hind
  constructor
  intro J
  set I : Finset (WNSpace ⊕ WNSpace) := J.image (fun x => Sum.inl (lKer F U δ x)) ∪
    J.image (fun x => Sum.inr (gKer h δ x)) with hI
  have g := hZ.hasGaussianLaw I
  have m1 : ∀ x : J, (Sum.inl (lKer F U δ x) : WNSpace ⊕ WNSpace) ∈ I := fun x =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ x.2)
  have m2 : ∀ x : J, (Sum.inr (gKer h δ x) : WNSpace ⊕ WNSpace) ∈ I := fun x =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ x.2)
  let L : (I → ℝ) →L[ℝ] (J → ℝ) := ContinuousLinearMap.pi fun x =>
    Real.sqrt Real.pi • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨_, m1 x⟩ +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨_, m2 x⟩)
  have e : (fun ω => J.restrict (fun x => phiL h W W' δ x ω)) =
      fun ω => L (I.restrict (fun i => Sum.elim (fun f => W f ω) (fun g => W' g ω) i)) := by
    funext ω; funext x
    simp [L, phiL_eq, smul_eq_mul]; ring
  rw [e]
  exact g.map_fun L

lemma integral_W_eq_zero {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (f : WNSpace) :
    ∫ ω, W f ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  rw [(hW.hasLaw_single f).integral_eq, integral_id_gaussianReal]

/-- `φ_L^{(δ)}` is centered. -/
theorem integral_phiL (h : ConfHyp F U) {W W' : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P W') (δ : ℝ) (x : ℂ) :
    ∫ ω, phiL h W W' δ x ω ∂P = 0 := by
  have := hW.isProbabilityMeasure
  simp only [phiL_eq]
  rw [integral_const_mul, integral_add ((memLp_two_W hW _).integrable one_le_two)
    ((memLp_two_W hW' _).integrable one_le_two), integral_W_eq_zero hW, integral_W_eq_zero hW']
  simp

end DDDF
end LQGMetric
