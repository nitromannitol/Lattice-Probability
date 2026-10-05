import Mathlib
import LatticeProb.Prob.MehlerInterpolation
import LatticeProb.Prob.MehlerSmoothingN
import LatticeProb.Prob.PittStatements

/-!
# Pitt's covariance representation for the standard Gaussian

For `F ∈ C¹_b`, `G ∈ C²_b` on `ℝ^k` and `γ = stdGaussian`, put
`Φ(a) = ∫ F · U_a G dγ`, `U_a = mehlerI a`.

* `pitt_hasDerivAt_phi`: `Φ'(a) = tan a · ∫ F · S (U_a G) dγ` on `(0, π/2)`;
* `pitt_gaussian_ibp`: `∫ F · S H dγ = - ∑_i ∫ ∂_i F · ∂_i H dγ` (`E[F L H] = -E⟨∇F, ∇H⟩`);
* `pitt_phi_deriv_eq`: `Φ'(a) = - sin a · ∑_i ∫ ∂_i F(z) ∫ ∂_i G(cos a z + sin a w) dγ(w) dγ(z)`;
* `pitt_covRep`: the fundamental theorem of calculus on `[0, π/2]` gives `PittCovRep k`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb

noncomputable section

/-- The weighted Mehler functional `Φ(a) = ∫ F · U_a G dγ`. -/
def pittPhi {d : ℕ} (F G : EuclideanSpace ℝ (Fin d) → ℝ) (a : ℝ) : ℝ :=
  ∫ w, F w * mehlerI a G w ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- Differentiation of `Φ` in the angle, for every angle, for `F ∈ C¹_b` and `G ∈ C¹_b`. -/
theorem pitt_hasDerivAt_weighted {d : ℕ} {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hG : mehlerIClassC1b G) (a : ℝ) :
    HasDerivAt (pittPhi F G)
      (∫ w, F w * mehlerIAng G a w ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) a := by
  obtain ⟨hF1, ⟨CF, hF0⟩, _⟩ := hF
  obtain ⟨hG1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hG
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  have hG' : mehlerIClassC1b G := ⟨hG1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩
  have hFc : Continuous F := hF1.continuous
  have hbd : Integrable (fun w : EuclideanSpace ℝ (Fin d) => CF * (C1 * (‖w‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))))) (stdGaussian _) :=
    (((mehlerI_integrable_norm d).add (integrable_const _)).const_mul C1).const_mul CF
  have hint : ∀ a' : ℝ, Integrable (fun w : EuclideanSpace ℝ (Fin d) => F w * mehlerI a' G w)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun a' =>
    Integrable.of_bound (hFc.aestronglyMeasurable.mul
      (mehlerI_continuous a' hG').aestronglyMeasurable) (CF * C0)
      (ae_of_all _ fun w => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hF0 w) (mehlerI_norm_le h0 a' w) (norm_nonneg _) hCF)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (F := fun a' w => F w * mehlerI a' G w)
    (F' := fun a' w => F w * mehlerIAng G a' w)
    (x₀ := a) (s := Set.univ) (bound := fun w => CF * (C1 * (‖w‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))))) Filter.univ_mem
    (Filter.Eventually.of_forall fun a' => (hint a').1)
    (hint a)
    (hFc.aestronglyMeasurable.mul (mehlerIAng_stronglyMeasurable hG' a).aestronglyMeasurable)
    (ae_of_all _ fun w a' _ => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hF0 w) (mehlerIAng_norm_le hC1 h1 a' w) (norm_nonneg _) hCF)
    hbd
    (ae_of_all _ fun w a' _ => (mehlerI_hasDerivAt_angle hG' w a').const_mul (F w))
  exact this.2

/-- **Step (1)**: for `a ∈ (0, π/2)`, `Φ'(a) = tan a · ∫ F · S (U_a G) dγ`. -/
theorem pitt_hasDerivAt_phi {d : ℕ} {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hG : mehlerIClassC2b G) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < Real.pi / 2) :
    HasDerivAt (pittPhi F G)
      (Real.tan a * ∫ w, F w * mehlerIS (mehlerI a G) w
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) a := by
  refine (pitt_hasDerivAt_weighted hF hG.c1b a).congr_deriv ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  have h := mehlerI_tan_mehlerIS hG ha0 ha1 w
  have h' : mehlerIAng G a w = Real.tan a * mehlerIS (mehlerI a G) w := h.symm
  simp only
  rw [h']
  ring

/-! ### Gaussian integration by parts -/

/-- A bounded continuous function is `γ`-integrable. -/
theorem pitt_integrable_of_cont_bdd {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ fun z => by simpa using hC z)

/-- Products of bounded continuous functions are bounded continuous. -/
theorem pitt_cont_bdd_mul {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfc : Continuous f) (hfb : ∃ C, ∀ x, |f x| ≤ C)
    (hgc : Continuous g) (hgb : ∃ C, ∀ x, |g x| ≤ C) :
    Continuous (fun x => f x * g x) ∧ ∃ C, ∀ x, |f x * g x| ≤ C := by
  obtain ⟨Cf, hf⟩ := hfb
  obtain ⟨Cg, hg⟩ := hgb
  refine ⟨hfc.mul hgc, Cf * Cg, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x) (hg x) (abs_nonneg _) ((abs_nonneg _).trans (hf x))

/-- The product of two `C¹_b` functions is `C¹_b`, with the Leibniz rule. -/
theorem pitt_c1b_mul {d : ℕ} {F K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hK : mehlerIClassC1b K) :
    mehlerIClassC1b (fun z => F z * K z) ∧
      ∀ z v, fderiv ℝ (fun z => F z * K z) z v
        = F z * fderiv ℝ K z v + K z * fderiv ℝ F z v := by
  obtain ⟨hF1, ⟨CF, hF0⟩, ⟨DF, hF1'⟩⟩ := hF
  obtain ⟨hK1, ⟨CK, hK0⟩, ⟨DK, hK1'⟩⟩ := hK
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  have hCK : 0 ≤ CK := (abs_nonneg _).trans (hK0 0)
  have hDF : 0 ≤ DF := (norm_nonneg _).trans (hF1' 0)
  have hDK : 0 ≤ DK := (norm_nonneg _).trans (hK1' 0)
  have hform : ∀ z v, fderiv ℝ (fun z => F z * K z) z v
      = F z * fderiv ℝ K z v + K z * fderiv ℝ F z v := by
    intro z v
    rw [fderiv_fun_mul (hF1.differentiable one_ne_zero z) (hK1.differentiable one_ne_zero z)]
    simp [smul_eq_mul]
  refine ⟨⟨hF1.mul hK1, ⟨CF * CK, fun x => ?_⟩, ⟨CF * DK + CK * DF, fun z => ?_⟩⟩, hform⟩
  · rw [abs_mul]
    exact mul_le_mul (hF0 x) (hK0 x) (abs_nonneg _) hCF
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hform, Real.norm_eq_abs]
    have hKv : |fderiv ℝ K z v| ≤ DK * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hK1' z) (norm_nonneg _))
    have hFv : |fderiv ℝ F z v| ≤ DF * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hF1' z) (norm_nonneg _))
    calc |F z * fderiv ℝ K z v + K z * fderiv ℝ F z v|
        ≤ |F z * fderiv ℝ K z v| + |K z * fderiv ℝ F z v| := abs_add_le _ _
      _ = |F z| * |fderiv ℝ K z v| + |K z| * |fderiv ℝ F z v| := by rw [abs_mul, abs_mul]
      _ ≤ CF * (DK * ‖v‖) + CK * (DF * ‖v‖) := by
          gcongr
          · exact hF0 z
          · exact hK0 z
      _ = (CF * DK + CK * DF) * ‖v‖ := by ring

/-- Integrability of the terms of the coordinate integration by parts. -/
theorem pitt_ibp_coord_integrable {d : ℕ} {F K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hK : mehlerIClassC1b K) (v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun z => F z * (fderiv ℝ K z v - inner ℝ z v * K z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have h1 : Integrable (fun z => F z * fderiv ℝ K z v)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hc, hb⟩ := pitt_cont_bdd_mul hF.1.continuous hF.2.1 (hK.dir_cont_bdd v).1
      (hK.dir_cont_bdd v).2
    exact pitt_integrable_of_cont_bdd hc hb
  have h2 : Integrable (fun z => inner ℝ z v * (F z * K z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hc, C, hC⟩ := pitt_cont_bdd_mul hF.1.continuous hF.2.1 hK.1.continuous hK.2.1
    exact (mehlerI_integrable_inner v).mul_bdd (c := C) hc.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa using hC z)
  refine (h1.sub h2).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply]
  ring

/-- **Coordinatewise Gaussian integration by parts** for `F, K ∈ C¹_b`:
`E[F (∂_v K - ⟨Z, v⟩ K)] = -E[K ∂_v F]`. -/
theorem pitt_ibp_coord {d : ℕ} {F K : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hK : mehlerIClassC1b K) (v : EuclideanSpace ℝ (Fin d)) :
    ∫ z, F z * (fderiv ℝ K z v - inner ℝ z v * K z)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -∫ z, K z * fderiv ℝ F z v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  obtain ⟨hFK, hform⟩ := pitt_c1b_mul hF hK
  have hstein := mehlerI_stein hFK v
  have e1 : Integrable (fun z => F z * fderiv ℝ K z v)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hc, hb⟩ := pitt_cont_bdd_mul hF.1.continuous hF.2.1 (hK.dir_cont_bdd v).1
      (hK.dir_cont_bdd v).2
    exact pitt_integrable_of_cont_bdd hc hb
  have e2 : Integrable (fun z => K z * fderiv ℝ F z v)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hc, hb⟩ := pitt_cont_bdd_mul hK.1.continuous hK.2.1 (hF.dir_cont_bdd v).1
      (hF.dir_cont_bdd v).2
    exact pitt_integrable_of_cont_bdd hc hb
  have e3 : Integrable (fun z => inner ℝ z v * (F z * K z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    obtain ⟨hc, C, hC⟩ := pitt_cont_bdd_mul hF.1.continuous hF.2.1 hK.1.continuous hK.2.1
    exact (mehlerI_integrable_inner v).mul_bdd (c := C) hc.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa using hC z)
  calc ∫ z, F z * (fderiv ℝ K z v - inner ℝ z v * K z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ z, (F z * fderiv ℝ K z v - inner ℝ z v * (F z * K z))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_congr_ae (ae_of_all _ fun z => by ring)
    _ = ∫ z, F z * fderiv ℝ K z v ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        - ∫ z, inner ℝ z v * (F z * K z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_sub e1 e3
    _ = ∫ z, F z * fderiv ℝ K z v ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
        - ∫ z, (F z * fderiv ℝ K z v + K z * fderiv ℝ F z v)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [hstein]
        simp_rw [hform]
    _ = -∫ z, K z * fderiv ℝ F z v ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [integral_add e1 e2]
        ring

/-- **Gaussian integration by parts** on the standard Gaussian (`E[F L H] = -E⟨∇F, ∇H⟩`):
for `F ∈ C¹_b` and `H ∈ C²_b`,
`∫ F · S H dγ = - ∑ᵢ ∫ ∂ᵢF · ∂ᵢH dγ`, with `S H = ΔH - ⟨∇H, w⟩`. -/
theorem pitt_gaussian_ibp {d : ℕ} {F H : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hH : mehlerIClassC2b H) :
    ∫ z, F z * mehlerIS H z ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -∑ i : Fin d, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ H z (EuclideanSpace.single i (1 : ℝ))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hS : ∀ z, F z * mehlerIS H z = ∑ k : Fin d, F z *
      (fderiv ℝ (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H) z
          (EuclideanSpace.single k (1 : ℝ))
        - inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
          mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H z) := by
    intro z
    rw [mehlerIS_eq_iteratedFDeriv hH.1 z, mehlerI_apply_eq_sum (fderiv ℝ H z) z,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mehlerI_fderiv_dir hH.1 z (EuclideanSpace.single k (1 : ℝ))
      (EuclideanSpace.single k (1 : ℝ))]
    rfl
  have hint : ∀ k : Fin d, Integrable (fun z => F z *
      (fderiv ℝ (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H) z
          (EuclideanSpace.single k (1 : ℝ))
        - inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
          mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H z))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun k =>
    pitt_ibp_coord_integrable hF (hH.dir_c1b (EuclideanSpace.single k (1 : ℝ)))
      (EuclideanSpace.single k (1 : ℝ))
  calc ∫ z, F z * mehlerIS H z ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ∫ z, ∑ k : Fin d, F z *
        (fderiv ℝ (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H) z
            (EuclideanSpace.single k (1 : ℝ))
          - inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
            mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_congr_ae (ae_of_all _ fun z => hS z)
    _ = ∑ k : Fin d, ∫ z, F z *
        (fderiv ℝ (mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H) z
            (EuclideanSpace.single k (1 : ℝ))
          - inner ℝ z (EuclideanSpace.single k (1 : ℝ)) *
            mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H z)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := integral_finsetSum _ fun k _ => hint k
    _ = ∑ k : Fin d, -∫ z, mehlerIDir (EuclideanSpace.single k (1 : ℝ)) H z *
          fderiv ℝ F z (EuclideanSpace.single k (1 : ℝ))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        Finset.sum_congr rfl fun k _ =>
          pitt_ibp_coord hF (hH.dir_c1b (EuclideanSpace.single k (1 : ℝ)))
            (EuclideanSpace.single k (1 : ℝ))
    _ = -∑ i : Fin d, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ H z (EuclideanSpace.single i (1 : ℝ))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [mehlerIDir]
        ring

/-! ### Step (3): `U_a G ∈ C²_b` and the gradient formula -/

/-- For `G ∈ C²_b` and `0 < sin a`, the Mehler interpolation `U_a G` is again `C²_b`. -/
theorem pitt_mehlerI_c2b {d : ℕ} {G : EuclideanSpace ℝ (Fin d) → ℝ} (hG : mehlerIClassC2b G)
    {a : ℝ} (hs : 0 < Real.sin a) : mehlerIClassC2b (mehlerI a G) := by
  obtain ⟨hG2, ⟨C0, h0⟩, ⟨C1, h1⟩, ⟨C2, h2⟩⟩ := hG
  have hG' : mehlerIClassC2b G := ⟨hG2, ⟨C0, h0⟩, ⟨C1, h1⟩, ⟨C2, h2⟩⟩
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (h2 0)
  have hD1 : ∀ (v x : EuclideanSpace ℝ (Fin d)), |mehlerIDir v G x| ≤ C1 * ‖v‖ := fun v x => by
    calc |mehlerIDir v G x| = ‖fderiv ℝ G x v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ G x‖ * ‖v‖ := (fderiv ℝ G x).le_opNorm v
      _ ≤ C1 * ‖v‖ := mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg _)
  have hD2 : ∀ (v e x : EuclideanSpace ℝ (Fin d)),
      |mehlerIDir v (mehlerIDir e G) x| ≤ C2 * (‖v‖ * ‖e‖) := fun v e x => by
    show |fderiv ℝ (mehlerIDir e G) x v| ≤ _
    rw [mehlerI_fderiv_dir hG2, ← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 G x ![v, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 G x‖ * ∏ i, ‖(![v, e] : Fin 2 → _) i‖ :=
          (iteratedFDeriv ℝ 2 G x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 G x‖ * (‖v‖ * ‖e‖) := by simp [Fin.prod_univ_two]
      _ ≤ C2 * (‖v‖ * ‖e‖) := mul_le_mul_of_nonneg_right (h2 x) (by positivity)
  have hder : ∀ w v : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (mehlerI a G) w v = Real.cos a * mehlerI a (mehlerIDir v G) w :=
    mehlerI_fderiv_apply a hG'.c1b
  have hH2 : ContDiff ℝ 2 (mehlerI a G) := by
    have h : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (mehlerI a G) :=
      mehlerN_contDiff_nat 2 a G hG2.continuous.measurable ⟨C0, h0⟩ hs
    exact_mod_cast h
  refine ⟨hH2, ⟨C0, fun x => ?_⟩, ⟨|Real.cos a| * C1, fun w => ?_⟩,
    ⟨Real.cos a ^ 2 * C2, fun w => ?_⟩⟩
  · exact (Real.norm_eq_abs _).symm.le.trans (mehlerI_norm_le h0 a x)
  · refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) hC1) fun v => ?_
    rw [hder, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Real.norm_eq_abs]
    exact (mehlerI_norm_le (hD1 v) a w).trans (by rw [mul_comm])
  · refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (sq_nonneg _) hC2) fun m => ?_
    have hm : m = ![m 0, m 1] := by
      ext i
      fin_cases i <;> rfl
    have hDe : ∀ e : EuclideanSpace ℝ (Fin d), mehlerIDir e (mehlerI a G)
        = fun x => Real.cos a * mehlerI a (mehlerIDir e G) x := fun e => funext fun x => hder x e
    have h3 : iteratedFDeriv ℝ 2 (mehlerI a G) w m
        = fderiv ℝ (mehlerIDir (m 1) (mehlerI a G)) w (m 0) := by
      rw [mehlerI_fderiv_dir hH2 w (m 0) (m 1), ← hm]
    have hsec : iteratedFDeriv ℝ 2 (mehlerI a G) w m
        = Real.cos a * (Real.cos a * mehlerI a (mehlerIDir (m 0) (mehlerIDir (m 1) G)) w) := by
      rw [h3, hDe (m 1),
        fderiv_const_mul (mehlerI_differentiable a (hG'.dir_c1b (m 1)) w) (Real.cos a)]
      simp only [smul_apply, smul_eq_mul]
      rw [mehlerI_fderiv_apply a (hG'.dir_c1b (m 1)) w (m 0)]
    rw [hsec, Fin.prod_univ_two, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hb := mehlerI_norm_le (hD2 (m 0) (m 1)) a w
    rw [Real.norm_eq_abs] at hb
    calc |Real.cos a| * (|Real.cos a| * |mehlerI a (mehlerIDir (m 0) (mehlerIDir (m 1) G)) w|)
        ≤ |Real.cos a| * (|Real.cos a| * (C2 * (‖m 0‖ * ‖m 1‖))) := by gcongr
      _ = Real.cos a ^ 2 * C2 * (‖m 0‖ * ‖m 1‖) := by
          rw [← sq_abs (Real.cos a)]
          ring

/-- **Step (3)**: for `a ∈ (0, π/2)`,
`tan a · ∫ F · S (U_a G) dγ = - sin a · ∑ᵢ ∫ ∂ᵢF(z) ∫ ∂ᵢG(cos a z + sin a w) dγ(w) dγ(z)`. -/
theorem pitt_phi_deriv_eq {d : ℕ} {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hG : mehlerIClassC2b G) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < Real.pi / 2) :
    Real.tan a * ∫ w, F w * mehlerIS (mehlerI a G) w ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = -(Real.sin a * ∑ i : Fin d, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
          (∫ w, fderiv ℝ G (Real.cos a • z + Real.sin a • w)
            (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [Real.pi_pos])
  have hcos : Real.cos a ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩).ne'
  rw [pitt_gaussian_ibp hF (pitt_mehlerI_c2b hG hsin)]
  have hterm : ∀ i : Fin d, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ (mehlerI a G) z (EuclideanSpace.single i (1 : ℝ))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = Real.cos a * ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
          (∫ w, fderiv ℝ G (Real.cos a • z + Real.sin a • w)
            (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro i
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [mehlerI_fderiv_apply a hG.c1b z (EuclideanSpace.single i (1 : ℝ))]
    simp only [mehlerI, mehlerIDir]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  rw [mul_neg, ← mul_assoc, Real.tan_mul_cos hcos]

/-! ### Step (4): the fundamental theorem of calculus on `[0, π/2]` -/

/-- The angle derivative `a ↦ ∫ F · ∂_a U_a G dγ` is interval integrable on `[0, π/2]`. -/
theorem pitt_angle_intervalIntegrable {d : ℕ} {F G : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : mehlerIClassC1b F) (hG : mehlerIClassC1b G) :
    IntervalIntegrable
      (fun a : ℝ => ∫ w, F w * mehlerIAng G a w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
      volume 0 (Real.pi / 2) := by
  obtain ⟨hF1, ⟨CF, hF0⟩, _⟩ := hF
  obtain ⟨hG1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩ := hG
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hCF : 0 ≤ CF := (abs_nonneg _).trans (hF0 0)
  have hG' : mehlerIClassC1b G := ⟨hG1, ⟨C0, h0⟩, ⟨C1, h1⟩⟩
  have hF' : mehlerIClassC1b F := ⟨hF1, ⟨CF, hF0⟩, ‹_›⟩
  have hbd : Integrable (fun w : EuclideanSpace ℝ (Fin d) => CF * (C1 * (‖w‖ +
      ∫ z, ‖z‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))))) (stdGaussian _) :=
    (((mehlerI_integrable_norm d).add (integrable_const _)).const_mul C1).const_mul CF
  have hmeas : Measurable fun a : ℝ =>
      ∫ w, F w * mehlerIAng G a w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    have : (fun a : ℝ => ∫ w, F w * mehlerIAng G a w ∂(stdGaussian (EuclideanSpace ℝ (Fin d))))
        = deriv (pittPhi F G) :=
      funext fun a => (pitt_hasDerivAt_weighted hF' hG' a).deriv.symm
    rw [this]
    exact measurable_deriv _
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
  exact Measure.integrableOn_of_bounded (by simp) hmeas.aestronglyMeasurable
    (ae_of_all _ fun a => norm_integral_le_of_norm_le hbd
      (ae_of_all _ fun w => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hF0 w) (mehlerIAng_norm_le hC1 h1 a w) (norm_nonneg _) hCF))

/-- **Pitt's covariance representation** for the standard Gaussian on `ℝ^k`:
for `F ∈ C¹_b`, `G ∈ C²_b`,
`Cov_γ(F, G) = ∫_0^{π/2} sin a · ∑ᵢ E[∂ᵢF(Z) · E_W ∂ᵢG(cos a Z + sin a W)] da`. -/
theorem pitt_covRep (k : ℕ) : PittCovRep k := by
  intro F G hF hG
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ => pitt_hasDerivAt_weighted hF hG.c1b a)
    (pitt_angle_intervalIntegrable hF hG.c1b)
  have hΦ0 : pittPhi F G 0
      = ∫ z, F z * G z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    simp [pittPhi, mehlerI]
  have hΦ1 : pittPhi F G (Real.pi / 2)
      = (∫ z, F z ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        * (∫ z, G z ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    simp [pittPhi, mehlerI, integral_mul_const]
  have hIoo : ∫ a in Set.Ioo 0 (Real.pi / 2),
        ∫ w, F w * mehlerIAng G a w ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))
      = ∫ a in Set.Ioo 0 (Real.pi / 2), -(Real.sin a *
          ∑ i : Fin k, ∫ z, fderiv ℝ F z (EuclideanSpace.single i (1 : ℝ)) *
            (∫ w, fderiv ℝ G (Real.cos a • z + Real.sin a • w)
              (EuclideanSpace.single i (1 : ℝ)) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
            ∂(stdGaussian (EuclideanSpace ℝ (Fin k)))) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
    simp only
    rw [← pitt_phi_deriv_eq hF hG ha.1 ha.2]
    exact (pitt_hasDerivAt_weighted hF hG.c1b a).unique (pitt_hasDerivAt_phi hF hG ha.1 ha.2)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi] at hIoo
  rw [hftc, hΦ0, hΦ1, integral_neg] at hIoo
  linarith

end

end LatticeProb
