/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.FibreGaussMaxLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Gram representation of the finite marginals of a centred Gaussian process

For a centred Gaussian process `Z` indexed by `T`, a finite set `G` of labels and a labelling
`φ : ι → T`, we produce vectors `v i ∈ ℝ^G` with `⟪v i, v j⟫ = cov[Z (φ i), Z (φ j)]` on `G`,
such that the vector `(Z (φ g))_{g ∈ G}` has the same law as `(⟪v g, x⟫)_{g ∈ G}` for `x` a
standard Gaussian vector of `ℝ^G`.

Source: standard fact (the finite-dimensional distributions of a Gaussian process are
multivariate Gaussian, determined by mean and covariance; e.g. Adler–Taylor, *Random Fields and
Geometry*, §1.2). The Gram realisation uses `LQGDimension.exists_gram_of_psdOn` (matrix square
root) and `LQGDimension.map_gramMap_stdGaussian`; the identification of laws is by
characteristic functions (`Measure.ext_of_charFun`), following the template of
`LQGDimension.segCombLaw`. Own bookkeeping.
-/

open MeasureTheory ProbabilityTheory WithLp LQGDimension
open scoped ENNReal InnerProductSpace RealInnerProductSpace Matrix

namespace QuantumZipper.RegUnif

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T ι : Type*}

/-- Variance of a finite linear combination of the coordinates of a Gaussian process. -/
lemma fgmLaw_var_sum {Z : T → Ω → ℝ} (hZ : IsGaussianProcess Z P) (G : Finset ι) (φ : ι → T)
    (t : G → ℝ) :
    Var[fun ω => ∑ g : G, t g * Z (φ g) ω; P] =
      ∑ i : G, ∑ j : G, t i * t j * cov[Z (φ i), Z (φ j); P] := by
  have hL : ∀ i : G, MemLp (fun ω => t i * Z (φ i) ω) 2 P := fun i =>
    ((hZ.hasGaussianLaw_eval (φ i)).memLp_two).const_mul _
  have hm : AEMeasurable (fun ω => ∑ g : G, t g * Z (φ g) ω) P :=
    (memLp_finsetSum _ fun g _ => hL g).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hm, covariance_fun_sum_fun_sum hL hL]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Gram representation of the finite marginals of a centred Gaussian process.** -/
theorem fgmLaw_gram {Z : T → Ω → ℝ} (hZ : IsGaussianProcess Z P)
    (hc : ∀ t, ∫ ω, Z t ω ∂P = 0) (G : Finset ι) (φ : ι → T) :
    ∃ v : ι → EuclideanSpace ℝ G,
      (∀ i ∈ G, ∀ j ∈ G, ‖v i - v j‖ ^ 2 = Var[fun ω => Z (φ i) ω - Z (φ j) ω; P]) ∧
      (∀ i ∈ G, ‖v i‖ ^ 2 = Var[Z (φ i); P]) ∧
      ∀ Φ : (G → ℝ) → ℝ≥0∞, Measurable Φ →
        ∫⁻ ω, Φ (fun g : G => Z (φ g) ω) ∂P =
          ∫⁻ x, Φ (fun g : G => ⟪v g, x⟫_ℝ) ∂stdGaussian (EuclideanSpace ℝ G) := by
  classical
  set C : ι → ι → ℝ := fun i j => cov[Z (φ i), Z (φ j); P] with hCdef
  have hmem : ∀ i, MemLp (Z (φ i)) 2 P := fun i => (hZ.hasGaussianLaw_eval (φ i)).memLp_two
  have hquad : ∀ t : G → ℝ, t ⬝ᵥ (Matrix.of fun i j : G => C i j) *ᵥ t =
      Var[fun ω => ∑ g : G, t g * Z (φ g) ω; P] := by
    intro t
    rw [fgmLaw_var_sum hZ G φ t]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, hCdef]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hPSD : PSDOn G C := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [star_trivial, Matrix.of_apply, hCdef]
      exact covariance_comm _ _
    · rw [star_trivial, hquad]
      exact variance_nonneg _ _
  obtain ⟨v, hv⟩ := exists_gram_of_psdOn G C hPSD
  have hvv : ∀ i ∈ G, ‖v i‖ ^ 2 = C i i := fun i hi => by
    rw [← real_inner_self_eq_norm_sq]
    exact hv i hi i hi
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hv i hi i hi, hv j hj j hj, hv i hi j hj, variance_fun_sub (hmem i) (hmem j)]
    simp only [hCdef, covariance_self (hZ.aemeasurable _)]
  · intro i hi
    rw [hvv i hi]
    exact covariance_self (hZ.aemeasurable _)
  · intro Φ hΦ
    set W : Ω → EuclideanSpace ℝ G := fun ω => toLp 2 (fun g : G => Z (φ g) ω) with hW
    have h0 : HasGaussianLaw (fun ω => (fun g : G => Z (φ g) ω)) P :=
      (hZ.comp_right φ).hasGaussianLaw G
    have hWG : HasGaussianLaw W P := h0.toLp_pi 2
    set S : Matrix G G ℝ := Matrix.of fun i j : G => ⟪v i, v j⟫_ℝ with hS
    have hSC : S = Matrix.of fun i j : G => C i j := by
      ext i j
      simp [hS, hv i i.2 j j.2]
    have hlaw : P.map W = multivariateGaussian 0 S := by
      apply Measure.ext_of_charFun
      funext t
      rw [hWG.charFun_map_eq, charFun_multivariateGaussian (posSemidef_gramOn G v),
        inner_zero_right]
      have hinner : ∀ ω, ⟪t, W ω⟫_ℝ = ∑ g : G, t.ofLp g * Z (φ g) ω := by
        intro ω
        simp [hW, PiLp.inner_apply, mul_comm]
      simp_rw [hinner]
      rw [integral_finsetSum _ (fun (g : G) _ =>
        ((hmem (g : ι)).integrable one_le_two).const_mul (t.ofLp g))]
      simp_rw [integral_const_mul, hc, mul_zero, Finset.sum_const_zero]
      have hSC' : (Matrix.of fun i j : G => C i j) = Matrix.of fun i j : G => ⟪v i, v j⟫_ℝ :=
        hSC.symm.trans hS
      rw [← hquad t.ofLp, hSC']
    have hΦm : Measurable fun y : EuclideanSpace ℝ G => Φ (ofLp y) :=
      hΦ.comp (PiLp.continuous_ofLp 2 _).measurable
    calc ∫⁻ ω, Φ (fun g : G => Z (φ g) ω) ∂P = ∫⁻ y, Φ (ofLp y) ∂(P.map W) := by
          rw [lintegral_map' hΦm.aemeasurable hWG.aemeasurable]
      _ = ∫⁻ y, Φ (ofLp y) ∂((stdGaussian (EuclideanSpace ℝ G)).map (gramMap G v)) := by
          rw [hlaw, map_gramMap_stdGaussian]
      _ = _ := by
          rw [lintegral_map hΦm (gramMap G v).continuous.measurable]
          exact lintegral_congr fun x => congrArg Φ (funext fun g => gramMap_apply G v x g)

end QuantumZipper.RegUnif
