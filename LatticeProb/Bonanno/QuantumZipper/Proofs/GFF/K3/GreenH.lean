/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenH at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Existence
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm11

/-!
# Green representation on `ℍ` and the dual-norm upper bound (GFF-K3 nodes H1, H2, H3)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.H.

* H1: `greenDensity f = -(2π)⁻¹ Δf`; `greenH_represent` (`∫ greenH(w,·) ρ_f = f(w)` on `Hbar`),
  `dirichletEnergyOn_H_eq` (`E_H f = ∫ f ρ_f`).
* H2: `ρ_f^± dz` are admissible; `∫ f dμ = B(μ, ρ_f⁺) − B(μ, ρ_f⁻)`; `B(ρ_f⁺ − ρ_f⁻) = E_H f`.
* H3: the signed Cauchy–Schwarz bound, `dualNormSq H (zeroSpace H) μ ≤ B(μ,μ)`, finiteness of
  `dualNormSq U (zeroSpace U) μ` for open `U ⊆ H`, and positive semidefiniteness of
  `zeroGFFTestCov U` on `TestFun H`.

The reflected term of `greenH` is handled by F4 at the point `w̄ ∉ tsupport f`.
-/

noncomputable section

open MeasureTheory Filter Set Laplacian
open scoped Real Topology RealInnerProductSpace ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

/-! ## Preliminaries -/

/-- The density `ρ_f = -(2π)⁻¹ Δf` of the Green representation. -/
def greenDensity (f : ℂ → ℝ) (z : ℂ) : ℝ := -(2 * Real.pi)⁻¹ * Δ f z

lemma two_le_smooth : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  simp

lemma contDiff_two_of_mem_zeroSpace {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ContDiff ℝ 2 f :=
  hf.1.of_le two_le_smooth

lemma H_subset_Hbar_K3 : H ⊆ Hbar := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz

theorem laplacian_eq_zero_of_notMem_tsupport_greenh {f : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport f) :
    Δ f z = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hz)).eq_of_nhds]
  exact congrFun InnerProductSpace.laplacian_const z

theorem continuous_greenDensity {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (greenDensity f) :=
  continuous_const.mul (continuous_laplacian_K3 hf)

theorem greenDensity_eq_zero_of_notMem {f : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport f) :
    greenDensity f z = 0 := by
  simp [greenDensity, laplacian_eq_zero_of_notMem_tsupport_greenh hz]

theorem tsupport_greenDensity_subset (f : ℂ → ℝ) : tsupport (greenDensity f) ⊆ tsupport f :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (greenDensity_eq_zero_of_notMem h)) (isClosed_tsupport _)

theorem hasCompactSupport_greenDensity {f : ℂ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (greenDensity f) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_greenDensity_subset f)

/-! ## H1 -/

/-- **H1.** Green representation of a test function on `ℍ`. -/
theorem greenH_represent {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) {w : ℂ} (hw : w ∈ Hbar) :
    ∫ z, greenH w z * greenDensity f z = f w := by
  have h2 := contDiff_two_of_mem_zeroSpace hf
  have hc := hf.2.1
  have hΔc := continuous_laplacian_K3 h2
  have hΔs := hasCompactSupport_laplacian_K3 hc
  have i1 := integrable_log_norm_sub_mul_K3 hΔc hΔs (conj w)
  have i2 := integrable_log_norm_sub_mul_K3 hΔc hΔs w
  have hwbar : conj w ∉ tsupport f := fun h => by
    have h' := hf.2.2 h
    change 0 < (conj w).im at h'
    rw [Complex.conj_im] at h'
    change 0 ≤ w.im at hw
    linarith
  have e : ∀ z, greenH w z * greenDensity f z =
      -(2 * π)⁻¹ * (Real.log ‖z - conj w‖ * Δ f z - Real.log ‖z - w‖ * Δ f z) := by
    intro z
    simp only [greenH, greenDensity, norm_sub_conj_comm w z, norm_sub_rev w z]
    ring
  simp_rw [e]
  have hπ : (2 * π) ≠ 0 := by positivity
  rw [integral_const_mul, integral_sub i1 i2, integral_log_norm_sub_mul_laplacian h2 hc,
    integral_log_norm_sub_mul_laplacian h2 hc, image_eq_zero_of_notMem_tsupport hwbar,
    mul_zero, zero_sub, mul_neg, neg_mul, neg_neg, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

/-- **H1.** The Dirichlet energy on `ℍ` of a test function. -/
theorem dirichletEnergyOn_H_eq {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) :
    dirichletEnergyOn H f = ∫ z, f z * greenDensity f z := by
  rw [energy_eq_of_tsupport_subset hf.2.2,
    integral_norm_fderiv_sq_eq_neg_integral_mul_laplacian (contDiff_two_of_mem_zeroSpace hf)
      hf.2.1]
  simp only [greenDensity]
  rw [show (fun z => f z * (-(2 * π)⁻¹ * Δ f z)) = fun z => -(2 * π)⁻¹ * (f z * Δ f z) from
    funext fun z => by ring, integral_const_mul]
  ring

/-! ## H2 -/

theorem integral_testMeasPos_K3 {ρ : ℂ → ℝ} (hρ : Measurable ρ) (G : ℂ → ℝ) :
    ∫ y, G y ∂(testMeasPos ρ) = ∫ y, max (ρ y) 0 * G y := by
  change ∫ y, G y ∂(volume.withDensity fun z => ((ρ z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hρ.real_toNNReal]
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]

theorem integral_testMeasNeg_K3 {ρ : ℂ → ℝ} (hρ : Measurable ρ) (G : ℂ → ℝ) :
    ∫ y, G y ∂(testMeasNeg ρ) = ∫ y, max (-ρ y) 0 * G y := by
  change ∫ y, G y ∂(volume.withDensity fun z => ((-ρ z).toNNReal : ℝ≥0∞)) = _
  have hm : Measurable fun z => (-ρ z).toNNReal := hρ.neg.real_toNNReal
  rw [integral_withDensity_eq_integral_smul hm]
  simp only [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]

theorem max_sub_max_neg_K3 (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

theorem isAdmissibleH_testMeasPos_of {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hK : tsupport ρ ⊆ Hbar) : IsAdmissibleH (testMeasPos ρ) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hρ
  exact isAdmissibleH_withDensity (g := fun z => ENNReal.ofReal (ρ z))
    (ENNReal.measurable_ofReal.comp hρ.measurable) (M := ENNReal.ofReal C) ENNReal.ofReal_lt_top
    (fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
      (by simpa [Real.norm_eq_abs] using hC x)))
    hc.isCompact hK (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])

theorem isAdmissibleH_testMeasNeg_of {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hK : tsupport ρ ⊆ Hbar) : IsAdmissibleH (testMeasNeg ρ) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hρ
  exact isAdmissibleH_withDensity (g := fun z => ENNReal.ofReal (-ρ z))
    (ENNReal.measurable_ofReal.comp hρ.measurable.neg) (M := ENNReal.ofReal C)
    ENNReal.ofReal_lt_top
    (fun x => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans
      (by simpa [Real.norm_eq_abs] using hC x)))
    hc.isCompact hK (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])

/-- **H2.** The measures `ρ_f^± dz` are admissible. -/
theorem isAdmissibleH_testMeas_greenDensity {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) :
    IsAdmissibleH (testMeasPos (greenDensity f)) ∧ IsAdmissibleH (testMeasNeg (greenDensity f)) := by
  have hc := continuous_greenDensity (contDiff_two_of_mem_zeroSpace hf)
  have hs := hasCompactSupport_greenDensity hf.2.1
  have hK : tsupport (greenDensity f) ⊆ Hbar :=
    (tsupport_greenDensity_subset f).trans (hf.2.2.trans H_subset_Hbar_K3)
  exact ⟨isAdmissibleH_testMeasPos_of hc hs hK, isAdmissibleH_testMeasNeg_of hc hs hK⟩

theorem integrable_greenH_mul {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (x : ℂ) :
    Integrable (fun y => greenH x y * ψ y) := by
  have e : (fun y => greenH x y * ψ y) =
      fun y => Real.log ‖y - conj x‖ * ψ y - Real.log ‖y - x‖ * ψ y := by
    funext y
    simp only [greenH, norm_sub_conj_comm x y, norm_sub_rev x y]
    ring
  rw [e]
  exact (integrable_log_norm_sub_mul_K3 hψ hc _).sub (integrable_log_norm_sub_mul_K3 hψ hc x)

theorem hasCompactSupport_max_zero {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun y => max (ψ y) 0) :=
  hc.comp_left (g := fun t : ℝ => max t 0) (by simp)

theorem hasCompactSupport_max_neg_zero {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun y => max (-ψ y) 0) :=
  hc.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)

theorem integral_greenH_testMeas_sub {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) {x : ℂ} (hx : x ∈ Hbar) :
    ∫ y, greenH x y ∂(testMeasPos (greenDensity f)) -
      ∫ y, greenH x y ∂(testMeasNeg (greenDensity f)) = f x := by
  have hρc : Continuous (greenDensity f) :=
    continuous_greenDensity (contDiff_two_of_mem_zeroSpace hf)
  have hρs := hasCompactSupport_greenDensity hf.2.1
  have i1 : Integrable (fun y => max (greenDensity f y) 0 * greenH x y) :=
    (integrable_greenH_mul (hρc.max continuous_const) (hasCompactSupport_max_zero hρs) x).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have i2 : Integrable (fun y => max (-greenDensity f y) 0 * greenH x y) :=
    (integrable_greenH_mul (hρc.neg.max continuous_const) (hasCompactSupport_max_neg_zero hρs)
      x).congr (Eventually.of_forall fun y => mul_comm _ _)
  rw [integral_testMeasPos_K3 hρc.measurable, integral_testMeasNeg_K3 hρc.measurable,
    ← integral_sub i1 i2, ← greenH_represent hf hx]
  congr 1
  funext y
  rw [← sub_mul, max_sub_max_neg_K3, mul_comm]

/-- **H2.** Pairings as kernel covariances against `ρ_f^± dz`. -/
theorem integral_eq_kernelCov_greenDensity {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace H) :
    ∫ x, f x ∂μ = kernelCov greenH μ (testMeasPos (greenDensity f))
      - kernelCov greenH μ (testMeasNeg (greenDensity f)) := by
  obtain ⟨hP, hN⟩ := isAdmissibleH_testMeas_greenDensity hf
  have := hP.1
  have := hN.1
  have iP : Integrable (fun x => ∫ y, greenH x y ∂(testMeasPos (greenDensity f))) μ :=
    (integrable_greenH_prod hμ hP).integral_prod_left
  have iN : Integrable (fun x => ∫ y, greenH x y ∂(testMeasNeg (greenDensity f))) μ :=
    (integrable_greenH_prod hμ hN).integral_prod_left
  unfold kernelCov
  rw [← integral_sub iP iN]
  obtain ⟨-, ⟨K, -, hKH, hKc⟩, -⟩ := hμ
  have hae : ∀ᵐ x ∂μ, x ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hKc] with x hx
    exact Set.notMem_compl_iff.mp hx
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  exact (integral_greenH_testMeas_sub hf (hKH hx)).symm

/-- **H2.** The Green energy of `ρ_f⁺ − ρ_f⁻` is the Dirichlet energy of `f`. -/
theorem kernelCov2_greenDensity {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) :
    kernelCov2 greenH (testMeasPos (greenDensity f), testMeasNeg (greenDensity f))
      (testMeasPos (greenDensity f), testMeasNeg (greenDensity f)) = dirichletEnergyOn H f := by
  obtain ⟨hP, hN⟩ := isAdmissibleH_testMeas_greenDensity hf
  have e1 := integral_eq_kernelCov_greenDensity hP hf
  have e2 := integral_eq_kernelCov_greenDensity hN hf
  have hρc : Continuous (greenDensity f) :=
    continuous_greenDensity (contDiff_two_of_mem_zeroSpace hf)
  have hρs := hasCompactSupport_greenDensity hf.2.1
  have hfc : Continuous f := hf.1.continuous
  have i1 : Integrable (fun y => max (greenDensity f y) 0 * f y) :=
    ((hρc.max continuous_const).mul hfc).integrable_of_hasCompactSupport hf.2.1.mul_left
  have i2 : Integrable (fun y => max (-greenDensity f y) 0 * f y) :=
    ((hρc.neg.max continuous_const).mul hfc).integrable_of_hasCompactSupport hf.2.1.mul_left
  have h : kernelCov2 greenH (testMeasPos (greenDensity f), testMeasNeg (greenDensity f))
      (testMeasPos (greenDensity f), testMeasNeg (greenDensity f)) =
      ∫ x, f x ∂(testMeasPos (greenDensity f)) - ∫ x, f x ∂(testMeasNeg (greenDensity f)) := by
    rw [e1, e2]; unfold kernelCov2; ring
  rw [h, integral_testMeasPos_K3 hρc.measurable, integral_testMeasNeg_K3 hρc.measurable,
    ← integral_sub i1 i2, dirichletEnergyOn_H_eq hf]
  congr 1
  funext y
  rw [← sub_mul, max_sub_max_neg_K3, mul_comm]

/-! ## H3 -/

open GFFExist in
/-- **H3.** Signed Cauchy–Schwarz bound. -/
theorem sq_integral_sub_le_energy_mul {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) {f : ℂ → ℝ} (hf : f ∈ zeroSpace H) :
    (∫ x, f x ∂μ - ∫ x, f x ∂ν) ^ 2 ≤
      dirichletEnergyOn H f * kernelCov2 greenH (μ, ν) (μ, ν) := by
  obtain ⟨hP, hN⟩ := isAdmissibleH_testMeas_greenDensity hf
  set a : HkE := zeroVec ⟨μ, hμ⟩ - zeroVec ⟨ν, hν⟩ with ha
  set b : HkE := zeroVec ⟨_, hP⟩ - zeroVec ⟨_, hN⟩ with hb
  have hab : ⟪a, b⟫ = ∫ x, f x ∂μ - ∫ x, f x ∂ν := by
    rw [ha, hb]
    simp only [inner_sub_left, inner_sub_right, zeroVec_inner]
    rw [integral_eq_kernelCov_greenDensity hμ hf, integral_eq_kernelCov_greenDensity hν hf]
    ring
  have haa : ‖a‖ ^ 2 = kernelCov2 greenH (μ, ν) (μ, ν) := by
    rw [← real_inner_self_eq_norm_sq, ha]
    simp only [inner_sub_left, inner_sub_right, zeroVec_inner, kernelCov2]
    ring
  have hbb : ‖b‖ ^ 2 = dirichletEnergyOn H f := by
    rw [← real_inner_self_eq_norm_sq, ← kernelCov2_greenDensity hf, hb]
    simp only [inner_sub_left, inner_sub_right, zeroVec_inner, kernelCov2]
    ring
  rw [← hab, ← haa, ← hbb, mul_comm, sq]
  have h := real_inner_mul_inner_self_le a b
  rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h

theorem isAdmissibleH_zero_K3 : IsAdmissibleH (0 : Measure ℂ) :=
  ⟨inferInstance, ⟨∅, isCompact_empty, empty_subset _, by simp⟩, 0, ENNReal.zero_lt_top,
    fun y => by simp⟩

/-- **H3.** Upper bound for the dual norm on `ℍ`. -/
theorem dualNormSq_H_le {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    dualNormSq H (zeroSpace H) μ ≤ ENNReal.ofReal (kernelCov greenH μ μ) := by
  unfold dualNormSq
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  have h := sq_integral_sub_le_energy_mul hμ isAdmissibleH_zero_K3 hf.1
  have hk : kernelCov2 greenH (μ, 0) (μ, 0) = kernelCov greenH μ μ := by
    simp [kernelCov2, kernelCov]
  rw [integral_zero_measure, sub_zero, hk] at h
  rw [div_le_iff₀ hf.2, mul_comm]
  exact h

/-- **H3.** Finiteness of the dual norm on open subsets of `ℍ`. -/
theorem dualNormSq_zeroSpace_le_of_subset_H {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) : dualNormSq U (zeroSpace U) μ < ⊤ :=
  (dualNormSq_zeroSpace_mono hU hUH).trans_lt
    ((dualNormSq_H_le hμ).trans_lt ENNReal.ofReal_lt_top)

theorem isAdmissibleDual_restrict_of_subset_H {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    IsAdmissibleDual U (zeroSpace U) (μ.restrict U) := by
  obtain ⟨hμf, ⟨K, hK, -, hKc⟩, -⟩ := id hμ
  have := hμf
  refine ⟨inferInstance, ⟨K ∩ closure U, hK.inter_right isClosed_closure, inter_subset_right, ?_⟩,
    ?_⟩
  · rw [Measure.restrict_apply' hU.measurableSet]
    refine measure_mono_null (fun x hx => ?_) hKc
    exact fun hxK => hx.1 ⟨hxK, subset_closure hx.2⟩
  · rw [← dualNormSq_zeroSpace_restrict hU]
    exact dualNormSq_zeroSpace_le_of_subset_H hU hUH hμ

theorem dualCov_zeroSpace_restrict {U : Set ℂ} (hU : IsOpen U) {μ ν : Measure ℂ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dualCov U (zeroSpace U) μ ν = dualCov U (zeroSpace U) (μ.restrict U) (ν.restrict U) := by
  unfold dualCov
  rw [dualNormSq_zeroSpace_restrict hU (μ := μ + ν), dualNormSq_zeroSpace_restrict hU (μ := μ),
    dualNormSq_zeroSpace_restrict hU (μ := ν), Measure.restrict_add]

theorem dualCov_eq_inner_of_subset_H {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H)
    {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    dualCov U (zeroSpace U) μ ν =
      ⟪rieszVec U (zeroSpace U) (μ.restrict U), rieszVec U (zeroSpace U) (ν.restrict U)⟫ := by
  have := hμ.1; have := hν.1
  rw [dualCov_zeroSpace_restrict hU]
  exact dualCov_eq_inner_rieszVec (isDNSpace_zeroSpace U)
    (isAdmissibleDual_restrict_of_subset_H hU hUH hμ)
    (isAdmissibleDual_restrict_of_subset_H hU hUH hν)

theorem isAdmissibleH_testMeas_of_testFun (σ : TestFun H) :
    IsAdmissibleH (testMeasPos σ.1) ∧ IsAdmissibleH (testMeasNeg σ.1) :=
  ⟨isAdmissibleH_testMeasPos_of σ.2.1.continuous σ.2.2.1 (σ.2.2.2.trans H_subset_Hbar_K3),
    isAdmissibleH_testMeasNeg_of σ.2.1.continuous σ.2.2.1 (σ.2.2.2.trans H_subset_Hbar_K3)⟩

/-- **H3.** `zeroGFFTestCov U` is positive semidefinite on `TestFun H` for open `U ⊆ ℍ`. -/
theorem zeroGFFTestCov_psd {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {n : ℕ}
    (ρ : Fin n → TestFun H) (t : Fin n → ℝ) :
    0 ≤ ∑ j, ∑ k, t j * t k * zeroGFFTestCov U (ρ j).1 (ρ k).1 := by
  set u : TestFun H → GradSpace U := fun σ =>
    rieszVec U (zeroSpace U) ((testMeasPos σ.1).restrict U) -
      rieszVec U (zeroSpace U) ((testMeasNeg σ.1).restrict U) with hu
  have hcov : ∀ σ τ : TestFun H, zeroGFFTestCov U σ.1 τ.1 = ⟪u σ, u τ⟫ := by
    intro σ τ
    obtain ⟨hσp, hσn⟩ := isAdmissibleH_testMeas_of_testFun σ
    obtain ⟨hτp, hτn⟩ := isAdmissibleH_testMeas_of_testFun τ
    unfold zeroGFFTestCov
    rw [dualCov_eq_inner_of_subset_H hU hUH hσp hτp, dualCov_eq_inner_of_subset_H hU hUH hσp hτn,
      dualCov_eq_inner_of_subset_H hU hUH hσn hτp, dualCov_eq_inner_of_subset_H hU hUH hσn hτn,
      hu]
    simp only [inner_sub_left, inner_sub_right]
    ring
  simp_rw [hcov]
  have h : ∑ j, ∑ k, t j * t k * ⟪u (ρ j), u (ρ k)⟫ =
      ⟪∑ j, t j • u (ρ j), ∑ k, t k • u (ρ k)⟫ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  rw [h]
  exact real_inner_self_nonneg

end QuantumZipper.K3
