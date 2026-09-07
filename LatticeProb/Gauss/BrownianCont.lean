/-
Brownian motion exists.

`LatticeProb/Gauss/Brownian.lean` builds a pre-Brownian motion out of white
noise, with no Kolmogorov extension theorem.  Kolmogorov-Chentsov, proved in
`LatticeProb/Prob/Chentsov.lean`, turns it into a Brownian motion: the fourth
moment of a centred Gaussian of variance `v` is a fixed multiple of `v ^ 2`, so
a pre-Brownian motion satisfies the Kolmogorov condition with exponents
`p = 4`, `q = 2`, and `q > 1` is what the chaining needs.
-/
import Mathlib
import LatticeProb.Prob.Chentsov
import LatticeProb.Gauss.Brownian

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

/-! ### The fourth moment of a centred Gaussian -/

/-- The fourth moment of the standard Gaussian. -/
def gaussFourth : ℝ≥0∞ := ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂(gaussianReal 0 1)

theorem gaussFourth_lt_top : gaussFourth < ∞ := by
  have h := memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ((4 : ℝ≥0) : ℝ≥0∞)) (f := (id : ℝ → ℝ)) (μ := gaussianReal 0 1)
    (by simp) (by simp) h.2
  simpa [gaussFourth] using this

theorem gaussFourth_ne_top : gaussFourth ≠ ∞ := gaussFourth_lt_top.ne

/-- The fourth moment of a centred Gaussian of variance `v` is `v ^ 2` times the
fourth moment of the standard Gaussian. -/
theorem lintegral_enorm_rpow_gaussianReal (v : ℝ≥0) :
    ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂(gaussianReal 0 v) = (v : ℝ≥0∞) ^ (2 : ℝ) * gaussFourth := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    have := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
    rw [mul_zero, mul_one] at this
    rw [show (fun x : ℝ => Real.sqrt v * x) = (Real.sqrt v * ·) from rfl, this]
    congr 1
    rw [← NNReal.coe_inj]
    simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hmap, lintegral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, ‖Real.sqrt v * x‖ₑ ^ (4 : ℝ)
      = ENNReal.ofReal (Real.sqrt v) ^ (4 : ℝ) * ‖x‖ₑ ^ (4 : ℝ) := by
    intro x
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    congr 2
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
    ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_nonneg v.coe_nonneg (by norm_num)]
  congr 1
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt v.coe_nonneg]

/-! ### A pre-Brownian motion is a Kolmogorov process -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem edist_nnreal_eq (s t : ℝ≥0) : edist s t = (nndist (s : ℝ) (t : ℝ) : ℝ≥0∞) := by
  rw [edist_nndist]
  congr 1

/-- **A pre-Brownian motion satisfies the Kolmogorov condition** with `p = 4`
and `q = 2`, because the fourth moment of a centred Gaussian of variance `v` is
a fixed multiple of `v ^ 2`. -/
theorem isKolmogorovProcess_of_isPreBrownianReal (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) :
    IsKolmogorovProcess B P 4 2 gaussFourth.toNNReal := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hm (fun s t => ?_)
    (by norm_num) (by norm_num)
  have hlaw := hB.hasLaw_sub s t
  have hkey : ∫⁻ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) ∂P
      = ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℝ) ∂(gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) := by
    have h1 : ∫⁻ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) ∂P
        = ∫⁻ ω, ‖(B s - B t) ω‖ₑ ^ (4 : ℝ) ∂P :=
      lintegral_congr fun ω => by rw [Pi.sub_apply, ← edist_eq_enorm_sub]
    have h2 := lintegral_map' (μ := P) (f := fun x : ℝ => ‖x‖ₑ ^ (4 : ℝ))
      (g := B s - B t) (by fun_prop) hlaw.aemeasurable
    rw [h1, ← h2, hlaw.map_eq]
    rfl
  rw [hkey, lintegral_enorm_rpow_gaussianReal, edist_nnreal_eq,
    ENNReal.coe_toNNReal gaussFourth_ne_top, mul_comm]

/-! ### Brownian motion exists -/

/-- **A pre-Brownian motion has a Brownian modification.**  This is the step
Mathlib 4.32 records as missing. -/
theorem exists_isBrownianReal_modification (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ (∀ t, B t =ᵐ[P] C t) ∧ IsBrownianReal C P := by
  obtain ⟨C, hCm, hmod, hcont⟩ :=
    exists_continuous_modification (isKolmogorovProcess_of_isPreBrownianReal hB hm) (by norm_num)
  exact ⟨C, hCm, hmod, { toIsPreBrownianReal := hB.congr hmod, cont := hcont }⟩

/-- **Brownian motion exists**, on the Gaussian product space over a countable
orthonormal basis of `L²(ℝ)`. -/
theorem exists_isBrownianReal :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), (∀ t, @Measurable Ω ℝ mΩ _ (B t)) ∧ @IsBrownianReal Ω mΩ B P := by
  obtain ⟨C, hCm, -, hC⟩ := exists_isBrownianReal_modification isPreBrownianReal_brownianOf
    (fun t => measurable_whiteNoise _ _)
  exact ⟨_, inferInstance, whiteNoiseLaw (volume : Measure ℝ), C, hCm, hC⟩

/-! ### Brownian motion on `ℝ ^ d` -/

section Dim

variable {d : ℕ}

/-- `d` independent copies of a real Brownian motion, scaled so that the
generator is `Δ / (2d)`, started at `x`. -/
def dimBrownian (d : ℕ) (C : ℝ≥0 → Ω → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (t : ℝ≥0) (ω : Fin d → Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => x i + (Real.sqrt d)⁻¹ * C t (ω i)

theorem isBrownianReal_comp_eval [IsProbabilityMeasure P] {C : ℝ≥0 → Ω → ℝ}
    (hC : IsBrownianReal C P) (i : Fin d) :
    IsBrownianReal (fun t ω => C t (ω i)) (Measure.pi fun _ : Fin d => P) := by
  refine ⟨⟨fun I => ?_⟩, ?_⟩
  · exact (hC.hasLaw I).comp (measurePreserving_eval (fun _ : Fin d => P) i).hasLaw
  · exact (measurePreserving_eval (fun _ : Fin d => P) i).quasiMeasurePreserving.ae hC.cont

/-- **Brownian motion on `ℝ ^ d` with generator `Δ / (2d)` exists**, started at
any point: the three clauses are that it starts at `x`, that each coordinate,
centred and scaled by `√d`, is a real Brownian motion, and that the coordinate
processes are independent. -/
theorem exists_isBrownian (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
      (∀ᵐ ω ∂P, B 0 ω = x) ∧
      (∀ i : Fin d, @IsBrownianReal Ω mΩ (fun t ω => Real.sqrt d * (B t ω i - x i)) P) ∧
      @ProbabilityTheory.iIndepFun Ω (Fin d) mΩ (fun _ => ℝ≥0 → ℝ) _
        (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => B t ω i) P := by
  obtain ⟨Ω₀, mΩ₀, P₀, C, hCm, hC⟩ := exists_isBrownianReal
  haveI : IsProbabilityMeasure P₀ := hC.isGaussianProcess.isProbabilityMeasure
  refine ⟨Fin d → Ω₀, inferInstance, Measure.pi fun _ => P₀, dimBrownian d C x, ?_, ?_, ?_⟩
  · have hzero : ∀ i : Fin d, ∀ᵐ ω ∂(Measure.pi fun _ : Fin d => P₀), C 0 (ω i) = 0 := fun i =>
      (measurePreserving_eval (fun _ : Fin d => P₀) i).quasiMeasurePreserving.ae
        hC.eval_zero_ae_eq_zero
    rw [← ae_all_iff] at hzero
    filter_upwards [hzero] with ω hω
    ext i
    simp [dimBrownian, hω i]
  · intro i
    have hd : (0 : ℝ) < d := by
      have := i.pos
      exact_mod_cast this
    have hsq : Real.sqrt d * (Real.sqrt d)⁻¹ = 1 :=
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hd)
    have hfun : (fun (t : ℝ≥0) (ω : Fin d → Ω₀) =>
        Real.sqrt d * (dimBrownian d C x t ω i - x i)) = fun t ω => C t (ω i) := by
      funext t ω
      show Real.sqrt d * (x i + (Real.sqrt d)⁻¹ * C t (ω i) - x i) = C t (ω i)
      rw [add_sub_cancel_left, ← mul_assoc, hsq, one_mul]
    rw [hfun]
    exact isBrownianReal_comp_eval hC i
  · have : (fun (i : Fin d) (ω : Fin d → Ω₀) => fun t : ℝ≥0 => dimBrownian d C x t ω i)
        = fun (i : Fin d) (ω : Fin d → Ω₀) =>
          (fun ω₀ : Ω₀ => fun t : ℝ≥0 => x i + (Real.sqrt d)⁻¹ * C t ω₀) (ω i) := rfl
    rw [this]
    exact iIndepFun_pi fun i =>
      (measurable_pi_lambda _ fun t => (hCm t).const_mul _ |>.const_add _).aemeasurable

end Dim

end LatticeProb

end
