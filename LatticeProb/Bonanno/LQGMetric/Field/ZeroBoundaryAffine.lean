/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ZeroBoundaryAffine at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Conformal
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Affine invariance of the zero-boundary GFF; admissibility on bounded domains (P2-ZB, WP-14)

For `r ≠ 0`, `z ∈ ℂ` and `A(y) = r y + z` (`affFwd r z`, inverse `affMap r z` of
`Statement/Field`):

* `zeroGFFTestCov_affine` : `⟨φ∘A⁻¹, ψ∘A⁻¹⟩_{H⁻¹(AU)} = r⁴ ⟨φ, ψ⟩_{H⁻¹(U)}`;
* `IsZBGFFProcess.affine` : if `X` is a zero-boundary GFF on `AU = rU + z`, then
  `φ ↦ r⁻² ⟨X, φ∘A⁻¹⟩ = ⟨X(r·+z), φ⟩` is a zero-boundary GFF on `U`
  (`h̊^{rU+z}(r·+z) ~ h̊^U`, Sheffield math/0312099 §2.2: conformal invariance of the Dirichlet
  inner product; Berestycki–Powell arXiv:2404.16642 Ch. 1, conformal invariance of the GFF);
* `zbAdmissible_of_isBounded` : every bounded open `U` is `ZBAdmissible` (translate `U` into `ℍ`).

Proof: QZ's conformal invariance of the dual norm `K3.dualNormSq_conformal` (QZ/Proofs/GFF/K3/
Conformal.lean, node C1, after Sheffield §2.2) for the conformal map `A : U → AU`, plus the
change of variables `∫ g(r x + z) dx = r⁻² ∫ g` (mathlib `Measure.integral_comp_smul`,
`integral_add_right_eq_self`), which gives `φ^±∘A⁻¹ dz = r² · A_*(φ^± dz)` on test functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

namespace LQGMetric

open QuantumZipper

/-- `y ↦ r y + z` (inverse of `affMap r z` for `r ≠ 0`) -/
def affFwd (r : ℝ) (z : ℂ) (y : ℂ) : ℂ := r • y + z

section Maps

variable {r : ℝ} {z : ℂ}

lemma affFwd_eq (r : ℝ) (z : ℂ) : affFwd r z = fun y => (r : ℂ) * y + z := by
  funext y; simp [affFwd, Complex.real_smul]

lemma affMap_affFwd (hr : r ≠ 0) (y : ℂ) : affMap r z (affFwd r z y) = y := by
  simp [affMap, affFwd, hr]

lemma affFwd_affMap (hr : r ≠ 0) (x : ℂ) : affFwd r z (affMap r z x) = x := by
  simp [affMap, affFwd, hr]

lemma continuous_affFwd (r : ℝ) (z : ℂ) : Continuous (affFwd r z) := by
  unfold affFwd; fun_prop

lemma continuous_affMap (r : ℝ) (z : ℂ) : Continuous (affMap r z) := by
  unfold affMap; fun_prop

lemma image_affFwd_eq (hr : r ≠ 0) (S : Set ℂ) : affFwd r z '' S = affMap r z ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa [mem_preimage, affMap_affFwd hr] using hy
  · intro hx; exact ⟨affMap r z x, hx, affFwd_affMap hr x⟩

/-- the open set `rU + z` (as a preimage under `affMap`, so no hypothesis is needed) -/
def affOpens (r : ℝ) (z : ℂ) (U : Opens ℂ) : Opens ℂ :=
  ⟨affMap r z ⁻¹' U, U.isOpen.preimage (continuous_affMap r z)⟩

/-- `φ ↦ φ ∘ A⁻¹ = φ((· - z)/r)` from `𝓓(U)` to `𝓓(rU + z)` -/
def zbPull (r : ℝ) (z : ℂ) (hr : r ≠ 0) {U : Opens ℂ} (φ : TestOn U) :
    TestOn (affOpens r z U) :=
  ⟨φ ∘ affMap r z, contDiff_comp_affMap r z φ.contDiff,
    hasCompactSupport_comp_affMap r z hr φ.hasCompactSupport,
    (tsupport_comp_subset_preimage _ (continuous_affMap r z)).trans
      (preimage_mono φ.tsupport_subset)⟩

@[simp] lemma zbPull_apply (hr : r ≠ 0) {U : Opens ℂ} (φ : TestOn U) (x : ℂ) :
    zbPull r z hr φ x = φ (affMap r z x) := rfl

theorem isConformalOnto_affFwd (hr : r ≠ 0) (U : Opens ℂ) :
    K3.IsConformalOnto (affFwd r z) U (affOpens r z U) where
  isOpen := U.isOpen
  diffOn := by
    rw [affFwd_eq]; exact ((differentiable_id.const_mul _).add_const _).differentiableOn
  injOn := fun x _ y _ hxy => by
    rw [← affMap_affFwd (z := z) hr x, hxy, affMap_affFwd hr]
  image_eq := image_affFwd_eq hr _
  deriv_ne := fun y _ => by
    have hd : HasDerivAt (fun y : ℂ => (r : ℂ) * y + z) ((r : ℂ) * 1) y :=
      ((hasDerivAt_id y).const_mul (r : ℂ)).add_const z
    rw [affFwd_eq, hd.deriv]
    simpa using hr

/-- change of variables `∫ g(r x + z) dx = r⁻² ∫ g` -/
lemma integral_comp_affFwd (g : ℂ → ℝ) :
    ∫ x, g (affFwd r z x) = (r ^ 2)⁻¹ * ∫ y, g y := by
  have h1 : ∫ x, g (affFwd r z x) = ∫ x, (fun w => g (w + z)) (r • x) := rfl
  rw [h1, Measure.integral_comp_smul (μ := (volume : Measure ℂ)) (fun w => g (w + z)) r,
    Complex.finrank_real_complex,
    integral_add_right_eq_self (fun w => g w) z, smul_eq_mul, abs_of_nonneg (by positivity)]

end Maps

/-! ## Scaling of the dual norm -/

section Scaling

variable {D : Set ℂ} {V : Set (ℂ → ℝ)}

/-- `dualNormSq` only sees the pairings: a factor `c` on all of them gives `c²`. -/
lemma dualNormSq_eq_of_integral_eq_mul {μ ν : Measure ℂ} {c : ℝ}
    (h : ∀ f ∈ V, ∫ x, f x ∂μ = c * ∫ x, f x ∂ν) :
    dualNormSq D V μ = ENNReal.ofReal (c ^ 2) * dualNormSq D V ν := by
  unfold dualNormSq
  simp_rw [ENNReal.mul_iSup]
  refine iSup_congr fun f => iSup_congr fun hf => ?_
  rw [h f hf.1, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (sq_nonneg c)]

/-- the relation "`μ'` is `r²` times the push-forward of `μ` under `A`, seen by test
functions", for finite measures `μ'`, `μ` with `μ` carried by `U` -/
structure AffRel (r : ℝ) (z : ℂ) (U : Set ℂ) (μ' μ : Measure ℂ) : Prop where
  fin' : IsFiniteMeasure μ'
  fin : IsFiniteMeasure μ
  carried : μ Uᶜ = 0
  pair : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
    ∫ x, f x ∂μ' = r ^ 2 * ∫ x, f x ∂(μ.map (affFwd r z))

lemma AffRel.add {r : ℝ} {z : ℂ} {U : Set ℂ} {μ₁' μ₁ μ₂' μ₂ : Measure ℂ}
    (h₁ : AffRel r z U μ₁' μ₁) (h₂ : AffRel r z U μ₂' μ₂) :
    AffRel r z U (μ₁' + μ₂') (μ₁ + μ₂) := by
  have := h₁.fin'; have := h₁.fin; have := h₂.fin'; have := h₂.fin
  refine ⟨inferInstance, inferInstance, by simp [h₁.carried, h₂.carried], fun f hf hc => ?_⟩
  have hA := (continuous_affFwd r z).measurable
  rw [Measure.map_add _ _ hA, integral_add_measure (hf.integrable_of_hasCompactSupport hc)
      (hf.integrable_of_hasCompactSupport hc),
    integral_add_measure (hf.integrable_of_hasCompactSupport hc)
      (hf.integrable_of_hasCompactSupport hc), h₁.pair f hf hc, h₂.pair f hf hc, mul_add]

lemma dualNormSq_affine {r : ℝ} {z : ℂ} (hr : r ≠ 0) {U : Opens ℂ} {μ' μ : Measure ℂ}
    (h : AffRel r z U μ' μ) :
    dualNormSq (affOpens r z U) (zeroSpace (affOpens r z U)) μ' =
      ENNReal.ofReal ((r ^ 2) ^ 2) * dualNormSq U (zeroSpace U) μ := by
  have := h.fin
  have hres : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by
    simpa [compl_def] using h.carried))
  rw [K3.dualNormSq_conformal (isConformalOnto_affFwd hr U) μ, hres]
  exact dualNormSq_eq_of_integral_eq_mul fun f hf => h.pair f hf.1.continuous hf.2.1

lemma dualCov_affine {r : ℝ} {z : ℂ} (hr : r ≠ 0) {U : Opens ℂ} {μ₁' μ₁ μ₂' μ₂ : Measure ℂ}
    (h₁ : AffRel r z U μ₁' μ₁) (h₂ : AffRel r z U μ₂' μ₂) :
    dualCov (affOpens r z U) (zeroSpace (affOpens r z U)) μ₁' μ₂' =
      r ^ 4 * dualCov U (zeroSpace U) μ₁ μ₂ := by
  unfold dualCov
  rw [dualNormSq_affine hr (h₁.add h₂), dualNormSq_affine hr h₁, dualNormSq_affine hr h₂]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (r ^ 2) ^ 2)]
  ring

end Scaling

/-! ## Test measures -/

section TestMeas

variable {r : ℝ} {z : ℂ}

lemma affRel_testMeasPos (hr : r ≠ 0) {U : Opens ℂ} (φ : TestOn U) :
    AffRel r z U (testMeasPos (zbPull r z hr φ)) (testMeasPos φ) := by
  have hpos := (K3.isGoodMeas_withDensity φ.continuous φ.hasCompactSupport).1
  have hpos' := (K3.isGoodMeas_withDensity (zbPull r z hr φ).continuous
    (zbPull r z hr φ).hasCompactSupport).1
  refine ⟨hpos', hpos, measure_mono_null (compl_subset_compl.2 φ.tsupport_subset)
    (testMeasPos_compl_tsupport φ), fun f hf _ => ?_⟩
  have hA := (continuous_affFwd r z).measurable
  rw [integral_map hA.aemeasurable hf.aestronglyMeasurable,
    K3.integral_testMeasPos_K3 (zbPull r z hr φ).continuous.measurable,
    K3.integral_testMeasPos_K3 φ.continuous.measurable]
  have e : ∫ y, max (φ y) 0 * f (affFwd r z y) =
      ∫ y, (fun w => max (zbPull r z hr φ w) 0 * f w) (affFwd r z y) := by
    simp only [zbPull_apply, affMap_affFwd hr]
  rw [e, integral_comp_affFwd (r := r) (z := z) (fun w => max (zbPull r z hr φ w) 0 * f w),
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]

lemma affRel_testMeasNeg (hr : r ≠ 0) {U : Opens ℂ} (φ : TestOn U) :
    AffRel r z U (testMeasNeg (zbPull r z hr φ)) (testMeasNeg φ) := by
  have hneg := (K3.isGoodMeas_withDensity φ.continuous.neg φ.hasCompactSupport.neg).1
  have hneg' := (K3.isGoodMeas_withDensity (zbPull r z hr φ).continuous.neg
    (zbPull r z hr φ).hasCompactSupport.neg).1
  refine ⟨hneg', hneg, measure_mono_null (compl_subset_compl.2 φ.tsupport_subset)
    (testMeasNeg_compl_tsupport φ), fun f hf _ => ?_⟩
  have hA := (continuous_affFwd r z).measurable
  rw [integral_map hA.aemeasurable hf.aestronglyMeasurable,
    K3.integral_testMeasNeg_K3 (zbPull r z hr φ).continuous.measurable,
    K3.integral_testMeasNeg_K3 φ.continuous.measurable]
  have e : ∫ y, max (-φ y) 0 * f (affFwd r z y) =
      ∫ y, (fun w => max (-zbPull r z hr φ w) 0 * f w) (affFwd r z y) := by
    simp only [zbPull_apply, affMap_affFwd hr]
  rw [e, integral_comp_affFwd (r := r) (z := z) (fun w => max (-zbPull r z hr φ w) 0 * f w),
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr), one_mul]

/-- **Scaling of the covariance**: `⟨φ∘A⁻¹, ψ∘A⁻¹⟩_{H⁻¹(AU)} = r⁴ ⟨φ, ψ⟩_{H⁻¹(U)}`. -/
theorem zeroGFFTestCov_affine (hr : r ≠ 0) {U : Opens ℂ} (φ ψ : TestOn U) :
    zeroGFFTestCov (affOpens r z U) (zbPull r z hr φ) (zbPull r z hr ψ) =
      r ^ 4 * zeroGFFTestCov U φ ψ := by
  unfold zeroGFFTestCov
  rw [dualCov_affine hr (affRel_testMeasPos hr φ) (affRel_testMeasPos hr ψ),
    dualCov_affine hr (affRel_testMeasPos hr φ) (affRel_testMeasNeg hr ψ),
    dualCov_affine hr (affRel_testMeasNeg hr φ) (affRel_testMeasPos hr ψ),
    dualCov_affine hr (affRel_testMeasNeg hr φ) (affRel_testMeasNeg hr ψ)]
  ring

end TestMeas

/-! ## Affine invariance of the law; bounded domains -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Affine invariance** `h̊^{rU+z}(r·+z) ~ h̊^U`: if `X` is a zero-boundary GFF process on
`rU + z`, then `φ ↦ r⁻² ⟨X, φ((·-z)/r)⟩` (the pairing of `X(r·+z)` with `φ`) is one on `U`. -/
theorem IsZBGFFProcess.affine {r : ℝ} {z : ℂ} (hr : r ≠ 0) {U : Opens ℂ}
    {X : TestOn (affOpens r z U) → Ω → ℝ} (hX : IsZBGFFProcess (affOpens r z U) X P) :
    IsZBGFFProcess U (fun φ ω => (r ^ 2)⁻¹ * X (zbPull r z hr φ) ω) P := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  refine ⟨fun φ => (hX.measurable _).const_mul _, ?_, fun φ => ?_, fun φ ψ => ?_⟩
  · exact (hX.gaussian.comp_right (zbPull r z hr)).smul (fun _ => (r ^ 2)⁻¹)
  · rw [integral_const_mul, hX.centered, mul_zero]
  · rw [covariance_const_mul_left, covariance_const_mul_right, hX.covariance_eq,
      zeroGFFTestCov_affine hr]
    field_simp

/-- a bounded set translated by `w = i(|R| + 1)` lies in `ℍ` -/
lemma exists_affOpens_one_subset_H {U : Opens ℂ} (hU : Bornology.IsBounded (U : Set ℂ)) :
    ∃ w : ℂ, ((affOpens 1 w U : Opens ℂ) : Set ℂ) ⊆ H := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall (0 : ℂ)
  refine ⟨⟨0, |R| + 1⟩, fun x hx => ?_⟩
  set w : ℂ := ⟨0, |R| + 1⟩
  have hx' : affMap 1 w x ∈ Metric.closedBall (0 : ℂ) R := hR hx
  have hxe : x = affMap 1 w x + w := by simp [affMap]
  rw [Metric.mem_closedBall, dist_zero_right] at hx'
  have him : |(affMap 1 w x).im| ≤ R := (Complex.abs_im_le_norm _).trans hx'
  show 0 < x.im
  rw [hxe, Complex.add_im]
  have : w.im = |R| + 1 := rfl
  rw [this]
  linarith [neg_abs_le (affMap 1 w x).im, le_abs_self R]

/-- Every bounded open set is `ZBAdmissible` (translate it into `ℍ`, where QZ's dual norms of
bounded densities are finite, and use the conformal invariance of the dual norm). -/
theorem zbAdmissible_of_isBounded {U : Opens ℂ} (hU : Bornology.IsBounded (U : Set ℂ)) :
    ZBAdmissible U := by
  obtain ⟨w, hsub⟩ := exists_affOpens_one_subset_H hU
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have hadm := zbAdmissible_of_subset_H hsub
  intro φ
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  have hKU : tsupport φ ⊆ closure (U : Set ℂ) := φ.tsupport_subset.trans subset_closure
  have hpos := (K3.isGoodMeas_withDensity φ.continuous φ.hasCompactSupport).1
  have hneg := (K3.isGoodMeas_withDensity φ.continuous.neg φ.hasCompactSupport.neg).1
  have fin : ∀ {μ' μ : Measure ℂ}, AffRel 1 w U μ' μ →
      dualNormSq (affOpens 1 w U) (zeroSpace (affOpens 1 w U)) μ' < ⊤ →
      dualNormSq U (zeroSpace U) μ < ⊤ := fun h hlt => by
    rw [dualNormSq_affine h1 h] at hlt
    simpa using hlt
  exact ⟨⟨hpos, ⟨_, hK, hKU, testMeasPos_compl_tsupport φ⟩,
      fin (affRel_testMeasPos h1 φ) (hadm (zbPull 1 w h1 φ)).1.2.2⟩,
    ⟨hneg, ⟨_, hK, hKU, testMeasNeg_compl_tsupport φ⟩,
      fin (affRel_testMeasNeg h1 φ) (hadm (zbPull 1 w h1 φ)).2.2.2⟩⟩

end LQGMetric
