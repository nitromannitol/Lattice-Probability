/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.KernelForm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Conformal
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH2

/-!
# GFF-K3 §3, node C2: kernel form of the dual norm on conformal images

Blueprint `blueprint/GFF_K3_BLUEPRINT.md`, §3 node **C2** `[C1, H7, Pushforward.bounded_density]`.
For a conformal map `φ : D → ℍ` (`IsConformalOnto φ D H`) and a finite measure `μ` whose
pushforward `(μ|_D) ∘ φ⁻¹` is `IsAdmissibleH`,

`dualNormSq D (zeroSpace D) μ = ∫_D ∫_D G_ℍ(φ x, φ y) dμ dμ`,

i.e. the Green function of `D` is `G_ℍ ∘ (φ × φ)`.  Source: Sheffield, *Gaussian free fields for
mathematicians* (2007), §2.2 (conformal invariance of the Dirichlet inner product) and §3
(`Var⟨h,μ⟩ = ∬ G dμ dμ`).  Proof: C1 (`dualNormSq_conformal`) moves the dual norm to `ℍ`, H7
(`dualNormSq_H_eq`) identifies it with the Green energy there, and the change of variables
`∫ F d(ν.map φ) = ∫ F ∘ φ dν` pulls the Green energy back.  Since `φ` is only controlled on `D`,
the change of variables is done with the measurable modification `D.piecewise φ 0`, which has
the same pushforward of `μ|_D`.

This file: the kernel form of the dual norm (`dualNormSq_conformal_eq_kernel`), of the dual
covariance (`dualCov_conformal_eq_kernel`), and of the covariance of a zero-boundary GFF on `D`
(`IsZeroBoundaryGFFOn.cov_conformal`).  The density version with densities touching `∂D`
(`dualCov_conformal_withDensity`) is in `KernelForm2.lean`.
-/

noncomputable section

open MeasureTheory Set Function ProbabilityTheory
open Classical
open scoped ENNReal ProbabilityTheory

namespace QuantumZipper.K3

variable {φ : ℂ → ℂ} {D : Set ℂ}

/-- The measurable modification of `φ` off `D`. -/
def confMod (φ : ℂ → ℂ) (D : Set ℂ) : ℂ → ℂ := D.piecewise φ 0

lemma measurable_confMod (hφ : IsConformalOnto φ D H) : Measurable (confMod φ D) :=
  ContinuousOn.measurable_piecewise hφ.diffOn.continuousOn continuousOn_const
    hφ.isOpen.measurableSet

lemma confMod_eqOn : EqOn (confMod φ D) φ D := fun _ hz => Set.piecewise_eq_of_mem _ _ _ hz

lemma map_restrict_confMod (hφ : IsConformalOnto φ D H) (μ : Measure ℂ) :
    (μ.restrict D).map φ = (μ.restrict D).map (confMod φ D) :=
  Measure.map_congr ((ae_restrict_mem hφ.isOpen.measurableSet).mono
    fun _ hz => (confMod_eqOn hz).symm)

/-- Change of variables in `kernelCov greenH` along a measurable map. -/
lemma kernelCov_greenH_map {m n : Measure ℂ} [IsFiniteMeasure n] {ψ : ℂ → ℂ}
    (hψ : Measurable ψ) :
    kernelCov greenH (m.map ψ) (n.map ψ) = kernelCov (fun x y => greenH (ψ x) (ψ y)) m n := by
  unfold kernelCov
  have hin : ∀ x, ∫ y, greenH x y ∂(n.map ψ) = ∫ y, greenH x (ψ y) ∂n := fun x =>
    integral_map hψ.aemeasurable (measurable_greenH_left x).aestronglyMeasurable
  simp_rw [hin]
  have hsm : StronglyMeasurable fun x => ∫ y, greenH x (ψ y) ∂n :=
    StronglyMeasurable.integral_prod_right' (f := fun p : ℂ × ℂ => greenH p.1 (ψ p.2))
      (measurable_greenH.comp (measurable_fst.prodMk (hψ.comp measurable_snd))).stronglyMeasurable
  exact integral_map hψ.aemeasurable hsm.aestronglyMeasurable

/-- The Green energy of the pushforwards is the `G_ℍ ∘ (φ × φ)` energy on `D`. -/
theorem kernelCov_conformal (hφ : IsConformalOnto φ D H) (μ ν : Measure ℂ) [IsFiniteMeasure ν] :
    kernelCov greenH ((μ.restrict D).map φ) ((ν.restrict D).map φ) =
      ∫ x in D, ∫ y in D, greenH (φ x) (φ y) ∂ν ∂μ := by
  rw [map_restrict_confMod hφ μ, map_restrict_confMod hφ ν,
    kernelCov_greenH_map (measurable_confMod hφ)]
  unfold kernelCov
  refine setIntegral_congr_fun hφ.isOpen.measurableSet fun x hx => ?_
  refine setIntegral_congr_fun hφ.isOpen.measurableSet fun y hy => ?_
  simp only [confMod_eqOn hx, confMod_eqOn hy]

/-- **Node C2 (covariance form).** -/
theorem dualCov_conformal_eq_kernel (hφ : IsConformalOnto φ D H) {μ ν : Measure ℂ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ' : IsAdmissibleH ((μ.restrict D).map φ)) (hν' : IsAdmissibleH ((ν.restrict D).map φ)) :
    dualCov D (zeroSpace D) μ ν = ∫ x in D, ∫ y in D, greenH (φ x) (φ y) ∂ν ∂μ := by
  have hadd : ((μ + ν).restrict D).map φ = (μ.restrict D).map φ + (ν.restrict D).map φ := by
    rw [map_restrict_confMod hφ, map_restrict_confMod hφ μ, map_restrict_confMod hφ ν,
      Measure.restrict_add, Measure.map_add _ _ (measurable_confMod hφ)]
  have hcov : dualCov D (zeroSpace D) μ ν =
      dualCov H (zeroSpace H) ((μ.restrict D).map φ) ((ν.restrict D).map φ) := by
    unfold dualCov
    rw [dualNormSq_conformal hφ (μ + ν), dualNormSq_conformal hφ μ, dualNormSq_conformal hφ ν,
      hadd]
  rw [hcov, dualCov_H_eq hμ' hν', kernelCov_conformal hφ]

end QuantumZipper.K3
