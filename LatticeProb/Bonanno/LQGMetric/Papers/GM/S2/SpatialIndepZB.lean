/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepZB at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryAffine
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DisjointUnion
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# GM Lemma 2.7: the pieces of a zero-boundary GFF on disjoint balls are independent

GM (`literature/src/1905.00383/uniqueness-final.tex`) l. 974–975, proof of Lemma 2.7: "Since the
balls `B_{1+s}(z)` for `z ∈ 𝒵` are disjoint, the Markov property of `h` implies that the fields
`(h − h_{1+s}(z))|_{B_{1+s}(z)}` … are conditionally independent given `h|_{ℂ∖U}`." Given the
Markov decomposition `h = 𝔥 + h̊` on `U` (`Blueprint.LMLem2_1`), this is the statement that the
restrictions of the zero-boundary GFF `h̊` on `U` to the components of `U` are independent
(Sheffield, *Gaussian free fields for mathematicians*, arXiv:math/0312099, and Sheffield,
arXiv:1012.4797, p. 12: the zero-boundary GFF on a domain with several components is the sum of
independent zero-boundary GFFs on the components).

Proof: the pairings form a jointly Gaussian process (mathlib
`IsGaussianProcess.iIndepFun_of_covariance_eq_zero`), and the cross covariances vanish because the
dual Dirichlet norm splits over a disjoint union of open sets (QuantumZipper
`K3.dualNormSq_union_of_disjoint`, `QuantumZipper/Proofs/GFF/K3/DisjointUnion.lean`).

* `zeroGFFTestCov_eq_zero_of_split` — `Cov(⟨h̊,φ⟩, ⟨h̊,ψ⟩) = 0` for `φ` vanishing on `D₂`, `ψ`
  vanishing on `D₁`, `U = D₁ ∪ D₂` a disjoint union of open sets.
* `iIndepFun_restrictTo_of_zeroBoundary` — the restrictions `h̊|_{D_i}` to relatively clopen,
  pairwise disjoint open subsets `D_i` of a bounded `U` are mutually independent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM

open QuantumZipper

section DualNorm

/-- the dual norm on `D` of a measure that does not charge `D` vanishes -/
lemma dualNormSq_eq_zero_of_measure_eq_zero {D : Set ℂ} {μ : Measure ℂ} (hμ : μ D = 0) :
    dualNormSq D (zeroSpace D) μ = 0 := by
  unfold dualNormSq
  refine le_antisymm (iSup₂_le fun f hf => ?_) zero_le
  have h0 : ∫ x, f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    refine measure_mono_null (fun x hx => ?_) hμ
    by_contra hxD
    exact hx (image_eq_zero_of_notMem_tsupport fun h => hxD (hf.1.2.2 h))
  simp [h0]

/-- adding a measure that does not charge `D` does not change the dual norm on `D` -/
lemma dualNormSq_add_of_measure_eq_zero {D : Set ℂ} {μ ν : Measure ℂ} (hν : ν D = 0) :
    dualNormSq D (zeroSpace D) (μ + ν) = dualNormSq D (zeroSpace D) μ := by
  unfold dualNormSq
  refine iSup_congr fun f => iSup_congr fun hf => ?_
  have hfν : (fun x => f x) =ᵐ[ν] 0 := by
    refine measure_mono_null (fun x hx => ?_) hν
    by_contra hxD
    exact hx (image_eq_zero_of_notMem_tsupport fun h => hxD (hf.1.2.2 h))
  have hint : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ := by
    by_cases hi : Integrable f μ
    · have hiν : Integrable f ν := (integrable_zero _ _ ν).congr hfν.symm
      rw [integral_add_measure hi hiν, integral_eq_zero_of_ae hfν, add_zero]
    · have : ¬ Integrable f (μ + ν) := fun h => hi (h.mono_measure (Measure.le_add_right le_rfl))
      rw [integral_undef hi, integral_undef this]
  rw [hint]

/-- **Cross covariances vanish on a disjoint union** (own assembly from QZ
`K3.dualNormSq_union_of_disjoint`): for `U = D₁ ∪ D₂` disjoint open, `μ` not charging `D₂`, `ν` not
charging `D₁`, both of finite dual norm on `U`, `dualCov U μ ν = 0`. -/
lemma dualCov_eq_zero_of_split {D₁ D₂ : Set ℂ} (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    (hd : Disjoint D₁ D₂) {μ ν : Measure ℂ} (hμ : μ D₂ = 0) (hν : ν D₁ = 0)
    (hμf : dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ < ⊤)
    (hνf : dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) ν < ⊤) :
    dualCov (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ ν = 0 := by
  unfold dualCov
  have hμ1 : dualNormSq D₁ (zeroSpace D₁) μ < ⊤ :=
    (K3.dualNormSq_zeroSpace_mono h₁ subset_union_left).trans_lt hμf
  have hν2 : dualNormSq D₂ (zeroSpace D₂) ν < ⊤ :=
    (K3.dualNormSq_zeroSpace_mono h₂ subset_union_right).trans_lt hνf
  rw [K3.dualNormSq_union_of_disjoint h₁ h₂ hd, K3.dualNormSq_union_of_disjoint h₁ h₂ hd,
    K3.dualNormSq_union_of_disjoint h₁ h₂ hd, dualNormSq_add_of_measure_eq_zero hν,
    add_comm μ ν, dualNormSq_add_of_measure_eq_zero hμ, dualNormSq_eq_zero_of_measure_eq_zero hμ,
    dualNormSq_eq_zero_of_measure_eq_zero hν, add_zero, zero_add,
    ENNReal.toReal_add hμ1.ne hν2.ne]
  ring

lemma testMeasPos_eq_zero_of_eqOn {ρ : ℂ → ℝ} {D : Set ℂ} (hD : MeasurableSet D)
    (hρ : ∀ x ∈ D, ρ x = 0) : testMeasPos ρ D = 0 := by
  rw [testMeasPos, withDensity_apply _ hD,
    setLIntegral_congr_fun hD (g := fun _ => 0) fun x hx => by simp [hρ x hx]]
  simp

lemma testMeasNeg_eq_zero_of_eqOn {ρ : ℂ → ℝ} {D : Set ℂ} (hD : MeasurableSet D)
    (hρ : ∀ x ∈ D, ρ x = 0) : testMeasNeg ρ D = 0 := by
  rw [testMeasNeg, withDensity_apply _ hD,
    setLIntegral_congr_fun hD (g := fun _ => 0) fun x hx => by simp [hρ x hx]]
  simp

/-- `Cov(⟨h̊,φ⟩, ⟨h̊,ψ⟩) = 0` for `h̊` a zero-boundary GFF on `U = D₁ ∪ D₂` (disjoint open),
`φ = 0` on `D₂`, `ψ = 0` on `D₁` (finite dual norms of `φ^±`, `ψ^±` on `U`). -/
lemma zeroGFFTestCov_eq_zero_of_split {U D₁ D₂ : Set ℂ} (hU : U = D₁ ∪ D₂) (h₁ : IsOpen D₁)
    (h₂ : IsOpen D₂) (hd : Disjoint D₁ D₂) {φ ψ : ℂ → ℝ} (hφ : ∀ x ∈ D₂, φ x = 0)
    (hψ : ∀ x ∈ D₁, ψ x = 0)
    (hφp : dualNormSq U (zeroSpace U) (testMeasPos φ) < ⊤)
    (hφn : dualNormSq U (zeroSpace U) (testMeasNeg φ) < ⊤)
    (hψp : dualNormSq U (zeroSpace U) (testMeasPos ψ) < ⊤)
    (hψn : dualNormSq U (zeroSpace U) (testMeasNeg ψ) < ⊤) :
    zeroGFFTestCov U φ ψ = 0 := by
  subst hU
  have a1 := testMeasPos_eq_zero_of_eqOn h₂.measurableSet hφ
  have a2 := testMeasNeg_eq_zero_of_eqOn h₂.measurableSet hφ
  have b1 := testMeasPos_eq_zero_of_eqOn h₁.measurableSet hψ
  have b2 := testMeasNeg_eq_zero_of_eqOn h₁.measurableSet hψ
  unfold zeroGFFTestCov
  rw [dualCov_eq_zero_of_split h₁ h₂ hd a1 b1 hφp hψp, dualCov_eq_zero_of_split h₁ h₂ hd a1 b2 hφp hψn,
    dualCov_eq_zero_of_split h₁ h₂ hd a2 b1 hφn hψp, dualCov_eq_zero_of_split h₁ h₂ hd a2 b2 hφn hψn]
  ring

/-- the dual norm on `U = D₁ ∪ D₂` (disjoint open) of a measure not charging `D₂` is its dual
norm on `D₁` -/
lemma dualNormSq_union_eq_left {D₁ D₂ : Set ℂ} (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    (hd : Disjoint D₁ D₂) {μ : Measure ℂ} (hμ : μ D₂ = 0) :
    dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ = dualNormSq D₁ (zeroSpace D₁) μ := by
  rw [K3.dualNormSq_union_of_disjoint h₁ h₂ hd, dualNormSq_eq_zero_of_measure_eq_zero hμ, add_zero]

/-- the zero-boundary covariance on `U = D₁ ∪ D₂` of test functions vanishing on `D₂` is the
zero-boundary covariance on `D₁` -/
lemma zeroGFFTestCov_union_eq_left {U D₁ D₂ : Set ℂ} (hU : U = D₁ ∪ D₂) (h₁ : IsOpen D₁)
    (h₂ : IsOpen D₂) (hd : Disjoint D₁ D₂) {φ ψ : ℂ → ℝ} (hφ : ∀ x ∈ D₂, φ x = 0)
    (hψ : ∀ x ∈ D₂, ψ x = 0) : zeroGFFTestCov U φ ψ = zeroGFFTestCov D₁ φ ψ := by
  subst hU
  have a1 := testMeasPos_eq_zero_of_eqOn h₂.measurableSet hφ
  have a2 := testMeasNeg_eq_zero_of_eqOn h₂.measurableSet hφ
  have b1 := testMeasPos_eq_zero_of_eqOn h₂.measurableSet hψ
  have b2 := testMeasNeg_eq_zero_of_eqOn h₂.measurableSet hψ
  have e : ∀ {μ ν : Measure ℂ}, μ D₂ = 0 → ν D₂ = 0 →
      dualCov (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ ν = dualCov D₁ (zeroSpace D₁) μ ν := by
    intro μ ν hμ hν
    unfold dualCov
    have hμν : (μ + ν) D₂ = 0 := by simp [hμ, hν]
    rw [dualNormSq_union_eq_left h₁ h₂ hd hμν, dualNormSq_union_eq_left h₁ h₂ hd hμ,
      dualNormSq_union_eq_left h₁ h₂ hd hν]
  unfold zeroGFFTestCov
  rw [e a1 b1, e a1 b2, e a2 b1, e a2 b2]

end DualNorm

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the inclusion `𝓓(V) ⊆ 𝓓(U)` for `V ≤ U` -/
abbrev testIncl (V U : TopologicalSpace.Opens ℂ) : TestOn V →L[ℝ] TestOn U :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := U)

lemma coe_testIncl {V U : TopologicalSpace.Opens ℂ} (hVU : V ≤ U) (φ : TestOn V) :
    ((testIncl V U φ : TestOn U) : ℂ → ℝ) = φ := by
  simp [testIncl, TestFunction.monoCLM_apply, hVU]

lemma restrictTo_apply_testIncl {V U : TopologicalSpace.Opens ℂ} (hVU : V ≤ U) (h : DistC)
    (φ : TestOn V) : restrictTo V h φ = restrictTo U h (testIncl V U φ) := by
  change h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) φ) =
    h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) (testIncl V U φ))
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, hVU]

/-- **GM l. 974–975**: the restrictions of a zero-boundary GFF on a bounded open `U` to pairwise
disjoint, relatively clopen open subsets `D_i` are mutually independent. -/
theorem iIndepFun_restrictTo_of_zeroBoundary [IsProbabilityMeasure P] {U : TopologicalSpace.Opens ℂ}
    (hU : Bornology.IsBounded (U : Set ℂ)) {ι : Type*} (D : ι → TopologicalSpace.Opens ℂ)
    (hDU : ∀ i, D i ≤ U) (hdisj : Pairwise fun i j => Disjoint (D i : Set ℂ) (D j))
    (hsplit : ∀ i, IsOpen ((U : Set ℂ) \ D i)) {g : Ω → DistC}
    (hg : IsZeroBoundaryGFF U (fun ω => restrictTo U (g ω)) P) :
    iIndepFun (fun i ω => restrictTo (D i) (g ω)) P := by
  have hadm := zbAdmissible_of_isBounded hU
  set X : (i : ι) → TestOn (D i) → Ω → ℝ :=
    fun i φ ω => restrictTo U (g ω) (testIncl (D i) U φ) with hXdef
  have hX : IsGaussianProcess (fun (p : (i : ι) × TestOn (D i)) ω => X p.1 p.2 ω) P :=
    hg.process.gaussian.comp_right fun (p : (i : ι) × TestOn (D i)) => testIncl (D p.1) U p.2
  have mX : ∀ i φ, AEMeasurable (X i φ) P := fun i φ =>
    (hg.process.measurable (testIncl (D i) U φ)).aemeasurable
  have hcov : ∀ i j, i ≠ j → ∀ (φ : TestOn (D i)) (ψ : TestOn (D j)),
      cov[X i φ, X j ψ; P] = 0 := by
    intro i j hij φ ψ
    rw [hXdef]
    simp only
    rw [hg.process.covariance_eq]
    have hφ0 : ∀ x ∈ (U : Set ℂ) \ D i, (testIncl (D i) U φ : ℂ → ℝ) x = 0 := by
      intro x hx
      rw [coe_testIncl (hDU i)]
      exact image_eq_zero_of_notMem_tsupport fun h => hx.2 (φ.tsupport_subset h)
    have hψ0 : ∀ x ∈ (D i : Set ℂ), (testIncl (D j) U ψ : ℂ → ℝ) x = 0 := by
      intro x hx
      rw [coe_testIncl (hDU j)]
      exact image_eq_zero_of_notMem_tsupport fun h =>
        Set.disjoint_left.1 (hdisj hij) hx (ψ.tsupport_subset h)
    exact zeroGFFTestCov_eq_zero_of_split (union_sdiff_cancel (hDU i)).symm (D i).isOpen
      (hsplit i) disjoint_sdiff_right hφ0 hψ0 ((hadm _).1.2.2) ((hadm _).2.2.2)
      ((hadm _).1.2.2) ((hadm _).2.2.2)
  have hind := hX.iIndepFun_of_covariance_eq_zero mX hcov
  rw [iIndepFun_iff_iIndep] at hind ⊢
  convert hind using 1
  funext i
  show MeasurableSpace.comap _ (MeasurableSpace.comap
    (fun (T : DistOn (D i)) (φ : TestOn (D i)) => T φ) MeasurableSpace.pi) = _
  rw [MeasurableSpace.comap_comp]
  congr 1
  funext ω φ
  exact restrictTo_apply_testIncl (hDU i) (g ω) φ

/-- **the restriction of a zero-boundary GFF to a component is a zero-boundary GFF**: for
`B ≤ U` with `U \ B` open (`B` relatively clopen in `U`). -/
theorem isZeroBoundaryGFF_restrict_component {U B : TopologicalSpace.Opens ℂ} (hBU : B ≤ U)
    (hsplit : IsOpen ((U : Set ℂ) \ B)) {g : Ω → DistC}
    (hg : IsZeroBoundaryGFF U (fun ω => restrictTo U (g ω)) P) :
    IsZeroBoundaryGFF B (fun ω => restrictTo B (g ω)) P := by
  have hpair : ∀ φ : TestOn B, (fun ω => restrictTo B (g ω) φ) =
      fun ω => restrictTo U (g ω) (testIncl B U φ) := fun φ => by
    funext ω; exact restrictTo_apply_testIncl hBU (g ω) φ
  have hzero : ∀ φ : TestOn B, ∀ x ∈ (U : Set ℂ) \ B, (testIncl B U φ : ℂ → ℝ) x = 0 := by
    intro φ x hx
    rw [coe_testIncl hBU]
    exact image_eq_zero_of_notMem_tsupport fun h => hx.2 (φ.tsupport_subset h)
  have hmeas : ∀ φ : TestOn B, Measurable fun ω => restrictTo B (g ω) φ := fun φ => by
    rw [hpair]; exact hg.process.measurable _
  have hgauss : IsGaussianProcess (fun (φ : TestOn B) ω => restrictTo B (g ω) φ) P := by
    have e : (fun (φ : TestOn B) ω => restrictTo B (g ω) φ) =
        (fun (φ : TestOn U) ω => restrictTo U (g ω) φ) ∘ testIncl B U := funext hpair
    rw [e]
    exact hg.process.gaussian.comp_right (testIncl B U)
  have hcent : ∀ φ : TestOn B, ∫ ω, restrictTo B (g ω) φ ∂P = 0 := fun φ => by
    rw [hpair]; exact hg.process.centered _
  have hcov : ∀ φ ψ : TestOn B, cov[fun ω => restrictTo B (g ω) φ,
      fun ω => restrictTo B (g ω) ψ; P] = zeroGFFTestCov (B : Set ℂ) φ ψ := fun φ ψ => by
    rw [hpair, hpair, hg.process.covariance_eq,
      zeroGFFTestCov_union_eq_left (union_sdiff_cancel hBU).symm B.isOpen hsplit
        disjoint_sdiff_right (hzero φ) (hzero ψ), coe_testIncl hBU, coe_testIncl hBU]
  exact ⟨measurable_distOn_iff.2 hmeas, ⟨hmeas, hgauss, hcent, hcov⟩⟩

end Indep

end LQGMetric.GM
