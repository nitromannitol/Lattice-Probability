/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.F2WedgeCoupleFree at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Opens of namespaces with no copied declaration are removed (WedgeTK). -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.RegularSample
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleMeanValue
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleFubini
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.SmoothingConvergence
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.CharFun
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.MetricSpace.Thickening
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.NonVacuity

/-!
# WEDGE-COUPLE (1): a free field from a lateral part and an independent radial part

Theorem 1.3, node F2, step (2b), input `WedgeLogCouplingStmt` (`F2Step2b.lean`). The key missing
lemma is the converse of the radial/lateral decomposition of the free field (Sheffield,
arXiv:1012.4797, §1.6 and §5.4 pp. 70–72; Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1:
`h = h_{|·|}(0) + h†` with independent summands): the lateral part of a free field plus an
independent copy of the radial part of a free field is again a free field.

For two free fields `X₁` on `(Ω, P)` and `X₂` on `(Ω', P')` we set on `(Ω × Ω', P ⊗ P')`, for
admissible `μ` (and `0` otherwise — junk coordinates are sanitized, so that the new field is a
function of the lateral part of `X₁` and the radial part of `X₂` only):

  `coupleField X₁ X₂ ω μ = X₁ ω.1 μ − ∫ h¹_{|z|}(0) dμ + ∫ h²_{|z|}(0) dμ`

(`h_r(0) = radAvgReg`). Theorem `isFreeGFFModConstH_coupleField`: this is a free field.

Route (own argument; the sources state the decomposition, not this converse in our
formalism): by radial stochastic Fubini (`WedgeTK.ae_integral_radial`) a.s.
`∫ h_{|z|}(0) dμ = X (radSmear μ)`, so the pair differences of `coupleField` are a.s.
`(D¹_p − D¹_{p̄}) ∘ fst + D²_{p̄} ∘ snd` (`p̄` the radially smeared pair), a linear image of two
independent Gaussian processes (hence Gaussian); the covariance identity reduces to the kernel
identity `kernelCov μ (radSmear ν) = kernelCov (radSmear μ) (radSmear ν)` (the Neumann potential
of a radial measure is radial, `WedgeTK.integral_phi_radSmear`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace F2



/-! ## 1. The kernel identity -/

/-! ## 2. Independent Gaussian processes on a product space -/

section ProdGauss

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Two Gaussian processes living on the two factors of a product probability space form a
jointly Gaussian process. -/
theorem isGaussianProcess_sumElim_prod {S T : Type*} {Z₁ : S → Ω → ℝ} {Z₂ : T → Ω' → ℝ}
    (h₁ : IsGaussianProcess Z₁ P) (h₂ : IsGaussianProcess Z₂ P') :
    IsGaussianProcess (fun (i : S ⊕ T) (ω : Ω × Ω') =>
      Sum.elim (fun s => Z₁ s ω.1) (fun t => Z₂ t ω.2) i) (P.prod P') := by
  classical
  constructor
  intro I
  have g₁ := NonVacuity.nv_hasGaussianLaw (measurePreserving_fst (μ := P) (ν := P'))
    (h₁.hasGaussianLaw I.toLeft)
  have g₂ := NonVacuity.nv_hasGaussianLaw (measurePreserving_snd (μ := P) (ν := P'))
    (h₂.hasGaussianLaw I.toRight)
  have hind := NonVacuity.nv_indepFun_prod (μ := P) (ν := P')
    (fun ω => I.toLeft.restrict (Z₁ · ω)) (fun ω => I.toRight.restrict (Z₂ · ω))
  have hG := IndepFun.hasGaussianLaw g₁ g₂ hind
  let L : ((I.toLeft → ℝ) × (I.toRight → ℝ)) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => match i with
      | ⟨Sum.inl s, h⟩ => (ContinuousLinearMap.proj
          (⟨s, Finset.mem_toLeft.2 h⟩ : I.toLeft)).comp (ContinuousLinearMap.fst ℝ _ _)
      | ⟨Sum.inr t, h⟩ => (ContinuousLinearMap.proj
          (⟨t, Finset.mem_toRight.2 h⟩ : I.toRight)).comp (ContinuousLinearMap.snd ℝ _ _)
  have e : (fun ω : Ω × Ω' => I.restrict (fun i =>
      Sum.elim (fun s => Z₁ s ω.1) (fun t => Z₂ t ω.2) i)) =
      fun ω => L (I.toLeft.restrict (Z₁ · ω.1), I.toRight.restrict (Z₂ · ω.2)) := by
    funext ω; funext i
    rcases i with ⟨i | i, h⟩ <;> rfl
  rw [e]
  exact hG.map_fun L

theorem cov_comp_fst {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    cov[fun ω : Ω × Ω' => f ω.1, fun ω => g ω.1; P.prod P'] = cov[f, g; P] := by
  have hmp := measurePreserving_fst (μ := P) (ν := P')
  rw [← hmp.map_eq] at hf hg
  conv_rhs => rw [← hmp.map_eq]
  rw [covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
    hmp.measurable.aemeasurable]
  rfl

theorem cov_comp_snd {f g : Ω' → ℝ} (hf : MemLp f 2 P') (hg : MemLp g 2 P') :
    cov[fun ω : Ω × Ω' => f ω.2, fun ω => g ω.2; P.prod P'] = cov[f, g; P'] := by
  have hmp := measurePreserving_snd (μ := P) (ν := P')
  rw [← hmp.map_eq] at hf hg
  conv_rhs => rw [← hmp.map_eq]
  rw [covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
    hmp.measurable.aemeasurable]
  rfl

/-- Covariance of `f ∘ fst + g ∘ snd` on a product space. -/
theorem cov_fst_add_snd {f f' : Ω → ℝ} {g g' : Ω' → ℝ} (hf : MemLp f 2 P) (hf' : MemLp f' 2 P)
    (hg : MemLp g 2 P') (hg' : MemLp g' 2 P') :
    cov[fun ω : Ω × Ω' => f ω.1 + g ω.2, fun ω => f' ω.1 + g' ω.2; P.prod P'] =
      cov[f, f'; P] + cov[g, g'; P'] := by
  have a1 : MemLp (fun ω : Ω × Ω' => f ω.1) 2 (P.prod P') := hf.comp_fst P'
  have a2 : MemLp (fun ω : Ω × Ω' => g ω.2) 2 (P.prod P') := hg.comp_snd P
  have a3 : MemLp (fun ω : Ω × Ω' => f' ω.1) 2 (P.prod P') := hf'.comp_fst P'
  have a4 : MemLp (fun ω : Ω × Ω' => g' ω.2) 2 (P.prod P') := hg'.comp_snd P
  change cov[(fun ω : Ω × Ω' => f ω.1) + (fun ω => g ω.2),
    (fun ω : Ω × Ω' => f' ω.1) + (fun ω => g' ω.2); P.prod P'] = _
  have hc : cov[fun ω : Ω × Ω' => g ω.2, fun ω => f' ω.1; P.prod P'] = 0 := by
    rw [covariance_comm]; exact covariance_fst_snd_prod hf' hg
  rw [covariance_add_left a1 a2 (a3.add a4), covariance_add_right a1 a3 a4,
    covariance_add_right a2 a3 a4, covariance_fst_snd_prod hf hg', hc,
    cov_comp_fst hf hf', cov_comp_snd hg hg']
  ring

end ProdGauss

/-! ## 3. The coupled field and its freeness -/

section Couple

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X₁ : Ω → FieldSample} {X₂ : Ω' → FieldSample}

end Couple

end F2
end QuantumZipper
