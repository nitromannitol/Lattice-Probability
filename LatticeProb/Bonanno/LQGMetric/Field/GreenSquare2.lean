/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenSquare2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GreenSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spectral form of the zero-boundary covariance on a square and R1 (task P2-KHSQ2, G5 + R1)

See the docstring of `LQGMetric.Field.GreenSquare`.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology QuantumZipper QuantumZipper.K3
open scoped RealInnerProductSpace

namespace LQGMetric
namespace HeatSq

open MarkovExt

variable {a L : ℝ}

/-- the vector `w_σ = ∑_k β_k(σ) e_k` -/
def wvec (a L : ℝ) (σ : ℂ → ℝ) : GradSpace (sqOpen a L) := ∑' k, modeCoef a L σ k • modeE a L k

lemma hasSum_wvec (hL : 0 < L) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) :
    HasSum (fun k => modeCoef a L σ k • modeE a L k) (wvec a L σ) := by
  have ho := orthonormal_modeE (a := a) hL
  have h := (ho.orthogonalFamily.summable_iff_norm_sq_summable
    (fun k => modeCoef a L σ k)).2 (summable_modeCoef_sq hL hσm hC h0)
  simp only [LinearIsometry.toSpanSingleton_apply] at h
  exact h.hasSum

lemma wvec_mem (hL : 0 < L) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) :
    wvec a L σ ∈ gradClosure (sqOpen a L) (zeroSpace (sqOpen a L)) :=
  (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (hasSum_wvec hL hσm hC h0)
    (Eventually.of_forall fun F => Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (modeE_mem hL k))

/-- `⟪w_σ, ∇f⟫ = ∫ f σ` for `f ∈ C_c^∞(U)` (G1 + Parseval) -/
theorem inner_wvec_test (hL : 0 < L) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) :
    ⟪wvec a L σ, gradFeat (sqOpen a L) f⟫ = ∫ z, f z * σ z := by
  have h1 := (innerSL ℝ (gradFeat (sqOpen a L) f)).hasSum (hasSum_wvec hL hσm hC h0)
  have h2 := (shift_injective.hasSum_iff (fun p hp => eq_zero_of_notMem_range_shift
    (F := fun p => 4 / L ^ 2 * (sqCoef a L f p * sqCoef a L σ p)) (ρ := σ)
    (fun p => ⟨4 / L ^ 2 * sqCoef a L f p, by ring⟩) p hp)).2
    (hasSum_sqCoef_parseval hL hf hσm hC h0)
  rw [real_inner_comm]
  refine h1.unique (h2.congr_fun fun k => ?_)
  simp only [innerSL_apply_apply, real_inner_smul_right, Function.comp_apply]
  rw [real_inner_comm, modeCoef_pair hL σ k hf]

/-- the pairing of the Riesz vector of a bounded `σ` with `∇f` -/
lemma inner_rieszFun_test (hL : 0 < L) (σ : BddOn (sqOpen a L)) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (sqOpen a L)) :
    ⟪rieszFun (sqOpens a L) σ.1, gradFeat (sqOpen a L) f⟫ = ∫ z, f z * σ.1 z := by
  have hV := isDNSpace_zeroSpace (sqOpen a L)
  have hpos : ∃ g ∈ zeroSpace (sqOpen a L), 0 < dirichletEnergyOn (sqOpen a L) g := by
    by_contra hno
    have h := eq_zero_of_mem_gradClosure_of_nopos hV hno (modeE_mem (a := a) hL (0, 0))
    have h1 := (orthonormal_modeE (a := a) hL).1 (0, 0)
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hadm : IsAdmissibleDual (sqOpen a L) (zeroSpace (sqOpen a L)) (testMeasPos σ.1) ∧
      IsAdmissibleDual (sqOpen a L) (zeroSpace (sqOpen a L)) (testMeasNeg σ.1) :=
    admissible_bddOn (U := sqOpens a L) (isBounded_sqOpen a L) σ
  obtain ⟨hm, ⟨C, hC⟩, -⟩ := σ.2
  change ⟪rieszVec (sqOpen a L) (zeroSpace (sqOpen a L)) (testMeasPos σ.1) -
    rieszVec (sqOpen a L) (zeroSpace (sqOpen a L)) (testMeasNeg σ.1), gradFeat (sqOpen a L) f⟫ = _
  rw [inner_sub_left, pair_rieszVec hV hadm.1 hpos f hf,
    pair_rieszVec hV hadm.2 hpos f hf, MarkovNorm.integral_testMeas_sub hm hC hf]
  exact integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)

/-- **The Riesz vector is the sine-series vector.** -/
theorem rieszFun_eq_wvec (hL : 0 < L) (σ : BddOn (sqOpen a L)) :
    rieszFun (sqOpens a L) σ.1 = wvec a L σ.1 := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := σ.2
  exact eq_of_mem_gradClosure (U := sqOpens a L) (rieszFun_mem _ _) (wvec_mem hL hm hC h0)
    fun f hf => by
      change ⟪rieszFun (sqOpens a L) σ.1, gradFeat (sqOpen a L) f⟫ =
        ⟪wvec a L σ.1, gradFeat (sqOpen a L) f⟫
      rw [inner_rieszFun_test hL σ hf, inner_wvec_test hL hm hC h0 hf]

lemma inner_modeE_wvec (hL : 0 < L) {σ : ℂ → ℝ} (hσm : Measurable σ) {C : ℝ}
    (hC : ∀ z, |σ z| ≤ C) (h0 : ∀ z ∉ sqOpen a L, σ z = 0) (k : ℕ × ℕ) :
    ⟪modeE a L k, wvec a L σ⟫ = modeCoef a L σ k := by
  have h := (innerSL ℝ (modeE a L k)).hasSum (hasSum_wvec hL hσm hC h0)
  refine h.unique ((hasSum_ite_eq k (modeCoef a L σ k)).congr_fun fun j => ?_)
  simp only [innerSL_apply_apply, real_inner_smul_right]
  rw [orthonormal_iff_ite.1 (orthonormal_modeE hL) k j]
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj, Ne.symm hj]

/-- **G5.** Spectral form of the zero-boundary GFF covariance on the square. -/
theorem zeroGFFTestCov_sqOpen_spectral (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) :
    HasSum (fun p => greenWeight p * (sqCoef a L ρ.1 p * sqCoef a L σ.1 p))
      (zeroGFFTestCov (sqOpens a L) ρ.1 σ.1) := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  obtain ⟨hm', ⟨C', hC'⟩, h0'⟩ := σ.2
  have hcov : zeroGFFTestCov (sqOpens a L) ρ.1 σ.1 = ⟪wvec a L ρ.1, wvec a L σ.1⟫ := by
    rw [← inner_rieszFun (admissible_bddOn (U := sqOpens a L) (isBounded_sqOpen a L) ρ)
      (admissible_bddOn (U := sqOpens a L) (isBounded_sqOpen a L) σ), rieszFun_eq_wvec hL ρ,
      rieszFun_eq_wvec hL σ]
    rfl
  have h := (innerSL ℝ (wvec a L σ.1)).hasSum (hasSum_wvec hL hm hC h0)
  simp only [innerSL_apply_apply, real_inner_smul_right] at h
  rw [hcov, real_inner_comm]
  refine (shift_injective.hasSum_iff (fun p hp => eq_zero_of_notMem_range_shift
    (F := fun p => greenWeight p * (sqCoef a L ρ.1 p * sqCoef a L σ.1 p)) (ρ := ρ.1)
    (fun p => ⟨greenWeight p * sqCoef a L σ.1 p, by ring⟩) p hp)).1
    (h.congr_fun fun k => ?_)
  rw [real_inner_comm, inner_modeE_wvec hL hm' hC' h0' k, Function.comp_apply,
    ← modeCoef_mul hL]

/-- **R1 (general square).** `zeroGFFTestCov U ρ σ = π ∫₀^∞ ∫∫ ρ p^D_s σ`. -/
theorem zeroGFFTestCov_sqOpen_eq_heat_gen (hL : 0 < L) (ρ σ : BddOn (sqOpen a L)) :
    zeroGFFTestCov (sqOpens a L) ρ.1 σ.1 =
      π * ∫ s in Ioi 0, ∫ y', ∫ y, ρ.1 y' * sqDirKernel a L s y' y * σ.1 y := by
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := ρ.2
  obtain ⟨hm', ⟨C', hC'⟩, h0'⟩ := σ.2
  exact (zeroGFFTestCov_sqOpen_spectral hL ρ σ).unique
    (hasSum_heatGreen_spectral hL hm hC h0 hm' hC' h0')

/-- **R1** (DDDF Prop. 29 input, handoff P2-DDDFP29): the square `(−1, 2)²`. -/
theorem zeroGFFTestCov_sqOpen_eq_heat (ρ σ : BddOn (sqOpen (-1) 3)) :
    zeroGFFTestCov (sqOpens (-1) 3) ρ.1 σ.1 =
      π * ∫ s in Ioi 0, ∫ y', ∫ y, ρ.1 y' * sqDirKernel (-1) 3 s y' y * σ.1 y :=
  zeroGFFTestCov_sqOpen_eq_heat_gen (by norm_num) ρ σ

end HeatSq
end LQGMetric
