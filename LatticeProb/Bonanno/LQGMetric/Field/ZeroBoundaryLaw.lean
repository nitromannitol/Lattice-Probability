/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryLaw at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH
import Mathlib.MeasureTheory.Constructions.Projective

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The zero-boundary GFF: Riesz form of the covariance, bilinearity, uniqueness of the law
(task P2-ZB, WP-14)

For `ZBAdmissible U`:

* `zbRiesz U φ ∈ GradSpace U` (QZ's Riesz vectors of `φ⁺dz` and `φ⁻dz`, subtracted) represents
  `f ↦ ∫ f φ` on `C_c^∞(U)` in the Dirichlet inner product (`inner_zbRiesz_gradFeat`), and
  `zeroGFFTestCov U φ ψ = ⟪zbRiesz U φ, zbRiesz U ψ⟫` (`zeroGFFTestCov_eq_inner`): the covariance
  is the `H⁻¹(U)` inner product (Sheffield math/0312099 §2; QZ `K3.dualCov_eq_inner_rieszVec`);
* `zbRiesz` is linear (`zbRiesz_add`, `zbRiesz_smul`: uniqueness of representers in the closure),
  so `zeroGFFTestCov U` is bilinear and positive semidefinite;
* `IsZBGFFProcess.map_eq` : two zero-boundary GFF processes on `U` have the same law on
  `TestOn U → ℝ` (finite-dimensional laws are centred Gaussian with the same covariance, QZ
  `WedgeRes.map_eq_of_gaussian_vec`; mathlib `IsProjectiveLimit.unique`), and
  `IsZeroBoundaryGFF.map_eq` : two `𝒟'(U)`-valued zero-boundary GFFs have the same law (the
  σ-algebra of `𝒟'(U)` is the cylinder one). Same proof as `GFFLaw.map_pairProc_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

/-! ## Riesz form of the covariance -/

section Riesz

variable {U : Opens ℂ}

/-- the Riesz vector of `f ↦ ∫ f φ` in `GradSpace U` -/
def zbRiesz (U : Opens ℂ) (φ : TestOn U) : GradSpace U :=
  rieszVec U (zeroSpace U) (testMeasPos φ) - rieszVec U (zeroSpace U) (testMeasNeg φ)

lemma zbRiesz_mem (φ : TestOn U) : zbRiesz U φ ∈ gradClosure U (zeroSpace U) :=
  sub_mem rieszVec_mem rieszVec_mem

theorem zeroGFFTestCov_eq_inner (hadm : ZBAdmissible U) (φ ψ : TestOn U) :
    zeroGFFTestCov U φ ψ = ⟪zbRiesz U φ, zbRiesz U ψ⟫ := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  unfold zeroGFFTestCov zbRiesz
  rw [dualCov_eq_inner_rieszVec hV (hadm φ).1 (hadm ψ).1,
    dualCov_eq_inner_rieszVec hV (hadm φ).1 (hadm ψ).2,
    dualCov_eq_inner_rieszVec hV (hadm φ).2 (hadm ψ).1,
    dualCov_eq_inner_rieszVec hV (hadm φ).2 (hadm ψ).2]
  simp only [inner_sub_left, inner_sub_right]
  ring

lemma integral_mul_test_eq (φ : TestOn U) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ∫ x, f x ∂(testMeasPos φ) - ∫ x, f x ∂(testMeasNeg φ) = ∫ x, f x * φ x := by
  have hfc : Continuous f := hf.1.continuous
  rw [integral_testMeasPos_K3 φ.continuous.measurable, integral_testMeasNeg_K3
    φ.continuous.measurable, ← integral_sub]
  · congr 1; funext x; rw [← sub_mul, max_sub_max_neg_K3, mul_comm]
  · exact ((φ.continuous.max continuous_const).mul hfc).integrable_of_hasCompactSupport
      hf.2.1.mul_left
  · exact ((φ.continuous.neg.max continuous_const).mul hfc).integrable_of_hasCompactSupport
      hf.2.1.mul_left

/-- `zbRiesz U φ` represents `f ↦ ∫ f φ` on `C_c^∞(U)`. -/
theorem inner_zbRiesz_gradFeat (hadm : ZBAdmissible U)
    (hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g) (φ : TestOn U) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace U) : ⟪zbRiesz U φ, gradFeat U f⟫ = ∫ x, f x * φ x := by
  have hV := isDNSpace_zeroSpace (U : Set ℂ)
  rw [zbRiesz, inner_sub_left, pair_rieszVec hV (hadm φ).1 hpos f hf,
    pair_rieszVec hV (hadm φ).2 hpos f hf, integral_mul_test_eq φ hf]

/-- two vectors of the closure with the same pairings against `gradFeat` agree -/
lemma eq_of_mem_gradClosure {v w : GradSpace U} (hv : v ∈ gradClosure U (zeroSpace U))
    (hw : w ∈ gradClosure U (zeroSpace U))
    (h : ∀ f ∈ zeroSpace U, ⟪v, gradFeat U f⟫ = ⟪w, gradFeat U f⟫) : v = w := by
  set u := v - w
  have hu : u ∈ gradClosure U (zeroSpace U) := sub_mem hv hw
  have h0 : ∀ f ∈ zeroSpace U, ⟪u, gradFeat U f⟫ = 0 := fun f hf => by
    rw [inner_sub_left, h f hf, sub_self]
  have hspan : (Submodule.span ℝ (gradFeat U '' zeroSpace U) : Set (GradSpace U)) ⊆
      {x | ⟪u, x⟫ = 0} := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span (isDNSpace_zeroSpace (U : Set ℂ)) hx
    exact h0 f hf
  have hcl : IsClosed {x : GradSpace U | ⟪u, x⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hu' : u ∈ closure (Submodule.span ℝ (gradFeat U '' zeroSpace U) : Set (GradSpace U)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hu
  have huu : ⟪u, u⟫ = 0 := closure_minimal hspan hcl hu'
  exact sub_eq_zero.1 (inner_self_eq_zero.1 huu)

lemma zbRiesz_eq_zero_of_nopos (hpos : ¬ ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g)
    (φ : TestOn U) : zbRiesz U φ = 0 :=
  eq_zero_of_mem_gradClosure_of_nopos (isDNSpace_zeroSpace (U : Set ℂ)) hpos (zbRiesz_mem φ)

/-- `Var⟨h̊^U, φ⟩ = ‖zbRiesz U φ‖² ≥ 0`. -/
theorem zeroGFFTestCov_self_nonneg (hadm : ZBAdmissible U) (φ : TestOn U) :
    0 ≤ zeroGFFTestCov U φ φ := by
  rw [zeroGFFTestCov_eq_inner hadm]; exact real_inner_self_nonneg

end Riesz

/-! ## Uniqueness of the law -/

section Law

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {U : Opens ℂ}

/-- the path `ω ↦ (φ ↦ X φ ω)` of a process indexed by `𝓓(U)` -/
def zbPath (X : TestOn U → Ω → ℝ) (ω : Ω) : TestOn U → ℝ := fun φ => X φ ω

/-- **Uniqueness of the law** of the zero-boundary GFF process on `U`. -/
theorem IsZBGFFProcess.map_eq {X : TestOn U → Ω → ℝ} {X' : TestOn U → Ω' → ℝ}
    (hX : IsZBGFFProcess U X P) (hX' : IsZBGFFProcess U X' P') :
    P.map (zbPath X) = P'.map (zbPath X') := by
  have := hX.gaussian.isProbabilityMeasure
  have := hX'.gaussian.isProbabilityMeasure
  have hm : Measurable (zbPath X) := measurable_pi_iff.2 hX.measurable
  have hm' : Measurable (zbPath X') := measurable_pi_iff.2 hX'.measurable
  have hfin : ∀ I : Finset (TestOn U), (P.map (zbPath X)).map I.restrict =
      (P'.map (zbPath X')).map I.restrict := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hm,
      Measure.map_map (Finset.measurable_restrict I) hm']
    exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
      (U := fun (i : I) ω => X i.1 ω) (V := fun (i : I) ω => X' i.1 ω)
      (hX.gaussian.hasGaussianLaw I) (hX'.gaussian.hasGaussianLaw I)
      (fun i => hX.measurable _) (fun i => hX'.measurable _)
      (fun i => (hX.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => (hX'.gaussian.hasGaussianLaw_eval i.1).memLp_two)
      (fun i => hX.centered i.1) (fun i => hX'.centered i.1)
      (fun i j => by rw [hX.covariance_eq, hX'.covariance_eq])
  exact IsProjectiveLimit.unique (P := fun I => (P'.map (zbPath X')).map I.restrict)
    hfin (fun _ => rfl)

/-- the pairing map `𝒟'(U) → (𝓓(U) → ℝ)` -/
def distEval (U : Opens ℂ) (g : DistOn U) : TestOn U → ℝ := fun φ => g φ

lemma measurable_distEval (U : Opens ℂ) : Measurable (distEval U) := fun _ hs => ⟨_, hs, rfl⟩

/-- **Uniqueness of the law** of a `𝒟'(U)`-valued zero-boundary GFF. -/
theorem IsZeroBoundaryGFF.map_eq {g : Ω → DistOn U} {g' : Ω' → DistOn U}
    (hg : IsZeroBoundaryGFF U g P) (hg' : IsZeroBoundaryGFF U g' P') : P.map g = P'.map g' := by
  have h := hg.process.map_eq hg'.process
  have e1 : zbPath (fun φ ω => g ω φ) = distEval U ∘ g := rfl
  have e2 : zbPath (fun φ ω => g' ω φ) = distEval U ∘ g' := rfl
  rw [e1, e2, ← Measure.map_map (measurable_distEval U) hg.measurable,
    ← Measure.map_map (measurable_distEval U) hg'.measurable] at h
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := congrArg (fun μ : Measure (TestOn U → ℝ) => μ t) h
  rwa [Measure.map_apply (measurable_distEval U) ht,
    Measure.map_apply (measurable_distEval U) ht] at this

end Law

end LQGMetric
