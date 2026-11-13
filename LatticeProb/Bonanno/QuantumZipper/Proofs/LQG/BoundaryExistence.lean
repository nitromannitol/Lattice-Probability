/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.BoundaryExistence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.TwoRadius
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GaussianToolkit
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.CircleContinuity
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures

/-!
# M4-B3, part 1: the two-radius lemma for the free field's approximating boundary measures

Blueprint `M4_BLUEPRINT.md`, nodes M4-B2 (instantiation) and M4-B3.

For the free field `X` (`IsFreeGFFModConstH X P`) and `R > 0` we work with the normalized field
`zField X R ω = addConst (X ω) (-X ω (fc(0,R)))` (`Z` of blueprint §0). The additive constant
only multiplies the approximating measures by `e^{γ c/2}` (handled in `BoundaryExistenceAS`).

* `ae_avgReg_spec`, `avgReg_zField_ae_eq`: almost surely the dyadic regularization `avgReg`
  converges everywhere on `Hbar`, and at each fixed point it equals the raw folded-circle value.
* `trlHyp_field`: the Gaussian hypotheses `TRLHyp` of the two-radius lemma hold for
  `U t = avgReg (Z) k t` (coarse radius `2^{-k}`) and `Δ t = avgReg (Z) (k+1) t - U t`, on any
  set `S` with `|t| + 1 ≤ R` (M4-R1/R2 through `GaussianToolkit`).
* `integral_abs_bdryApprox_step_le_rate`: for `f` bounded measurable, vanishing off `S`,
  `E|∫ f dν_k - ∫ f dν_{k+1}| ≤ C e^{-β k log 2}` with `β = bdryRate γ > 0` for every
  `γ ∈ (0,2)`, where `ν_k = bdryApprox γ (Z ω) k`.
* `integral_abs_bdryApprox_le_rate`: the telescoped form, for `k ≤ k'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace BdryExist

open GaussTK TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The normalized field `Z = X − X(fc(0,R))`. -/
def zField (X : Ω → FieldSample) (R : ℝ) (ω : Ω) : FieldSample :=
  addConst (X ω) (-X ω (foldedCircle 0 R))

/-- Coarse coordinate `U t = h_{2^{-k}}(t)` of the normalized field. -/
def bU (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  avgReg (zField X R ω) k (t : ℂ)

/-- Increment `Δ t = h_{2^{-k-1}}(t) − h_{2^{-k}}(t)`. -/
def bΔ (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  bU X R (k + 1) t ω - bU X R k t ω

/-- Density of `bdryApprox γ (Z ω) k`. -/
def bDens (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * bU X R k t ω)

/-- Variance of `U t`. -/
def bV (R : ℝ) (k : ℕ) : ℝ≥0 := (2 * log R - 2 * log (radius k)).toNNReal

theorem radius_succ (k : ℕ) : radius (k + 1) = radius k / 2 := by
  simp [radius, pow_succ, div_eq_mul_inv]

theorem radius_le_one (k : ℕ) : radius k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem log_one_div_radius (k : ℕ) : log (1 / radius k) = k * log 2 := by
  rw [one_div, log_inv, radius, log_pow, log_inv]; ring

theorem measurable_zField (hX : IsFreeGFFModConstH X P) (R : ℝ) : Measurable (zField X R) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  simp only [zField, addConst]
  exact (hX.measurable_coord μ).add ((hX.measurable_coord _).neg.mul_const _)

theorem measurable_bU (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × Ω => bU X R k p.1 p.2) :=
  (measurable_avgReg k).comp (((measurable_zField hX R).comp measurable_snd).prodMk
    (Complex.continuous_ofReal.measurable.comp measurable_fst))

/-! ### Almost sure identification of `avgReg` -/

/-- Almost surely the dyadic roundings converge at every point of `Hbar` (so `avgReg` is a
genuine limit), and at each fixed point `avgReg` equals the raw folded-circle value a.s. -/
theorem ae_avgReg_spec (hX : IsFreeGFFModConstH X P) (k : ℕ) :
    (∀ᵐ ω ∂P, ∀ z ∈ Hbar, Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 (avgReg (X ω) k z))) ∧
    ∀ z ∈ Hbar, (fun ω => avgReg (X ω) k z) =ᵐ[P] fun ω => X ω (foldedCircle z (radius k)) := by
  have hr := radius_pos k
  obtain ⟨Y, -, hae, hlim⟩ := CircleCont.exists_continuous_modification
    (Z := fun z ω => X ω (foldedCircle z (radius k)) - X ω (foldedCircle 0 (radius k)))
    (fun z => ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable)
    (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hr.le) 4) (gaussianAbsMoment_nonneg 8))
    (CircleCont.momentBound_circleDiff hX hr 0)
  have hlim' : ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)))
        atTop (𝓝 (Y z ω + X ω (foldedCircle 0 (radius k)))) := by
    filter_upwards [hlim] with ω hω z hz
    have := (hω z hz).add_const (X ω (foldedCircle 0 (radius k)))
    simpa using this
  refine ⟨?_, ?_⟩
  · filter_upwards [hlim'] with ω hω z hz
    have h := hω z hz
    have he : avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := h.limUnder_eq
    rw [he]; exact h
  · intro z hz
    filter_upwards [hlim', hae z hz] with ω hω hY
    have he : avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := (hω z hz).limUnder_eq
    rw [he, hY]
    ring

/-- `avgReg` of the normalized field is `avgReg` of `X` minus the constant, a.s. everywhere. -/
theorem ae_avgReg_zField (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      avgReg (zField X R ω) k z = avgReg (X ω) k z - X ω (foldedCircle 0 R) := by
  filter_upwards [(ae_avgReg_spec hX k).1] with ω hω z hz
  have h := (hω z hz).add_const (-X ω (foldedCircle 0 R))
  have e : (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k)) + -X ω (foldedCircle 0 R)) =
      fun n => zField X R ω (foldedCircle (dyadicRoundC n z) (radius k)) := by
    funext n; simp [zField, addConst]
  rw [e] at h
  have := h.limUnder_eq
  change avgReg (zField X R ω) k z = _ at this
  rw [this]; ring

theorem avgReg_zField_ae_eq (hX : IsFreeGFFModConstH X P) (R : ℝ) (k : ℕ) {z : ℂ}
    (hz : z ∈ Hbar) :
    (fun ω => avgReg (zField X R ω) k z) =ᵐ[P] fcPairVal X (z, radius k, 0, R) := by
  filter_upwards [ae_avgReg_zField hX R k, (ae_avgReg_spec hX k).2 z hz] with ω h1 h2
  rw [h1 z hz, h2]; rfl

/-! ### Gaussian laws and variances -/

theorem hasLaw_fcPairVal (hX : IsFreeGFFModConstH X P) {p : FcIdx} (hp : p.Good) :
    HasLaw (fcPairVal X p) (gaussianReal 0 (fcPairCov p p).toNNReal) P := by
  have hG : HasGaussianLaw (fcPairVal X p) P :=
    (isGaussianProcess_fcPair hX).hasGaussianLaw_eval ⟨p, hp⟩
  have hm : AEMeasurable (fcPairVal X p) P := (measurable_fcPairVal hX p).aemeasurable
  refine ⟨hm, ?_⟩
  rw [hG.map_eq_gaussianReal, integral_fcPairVal hX hp, ← covariance_self hm,
    covariance_fcPairVal hX hp hp]

theorem fcPairCov_Zself {t r R : ℝ} (hr : 0 < r) (h : |t| + r ≤ R) :
    fcPairCov ((t : ℂ), r, 0, R) ((t : ℂ), r, 0, R) = 2 * log R - 2 * log r := by
  have h' : ‖(t : ℂ)‖ + r ≤ R := by rw [norm_ofReal']; exact h
  rw [fcPairCov_Z hr hr h' h', kernelCov_fc_real_sameCenter hr hr, max_self]; ring

theorem fcPairCov_incr_self {t r : ℝ} (hr : 0 < r) :
    fcPairCov ((t : ℂ), r / 2, (t : ℂ), r) ((t : ℂ), r / 2, (t : ℂ), r) = 2 * log 2 := by
  have hr2 : 0 < r / 2 := by positivity
  have hle : r / 2 ≤ r := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hr2 hr2, kernelCov_fc_real_sameCenter hr2 hr,
    kernelCov_fc_real_sameCenter hr hr2, kernelCov_fc_real_sameCenter hr hr,
    max_eq_right hle, max_eq_left hle]
  simp only [max_self]
  rw [log_div hr.ne' two_ne_zero]
  ring

/-! ### The Gaussian hypotheses of the two-radius lemma (M4-R1/R2 → `TRLHyp`) -/

/-- **Instantiation of `TRLHyp`** for the normalized free field at the consecutive radii
`2^{-k}` (coarse, `U`) and `2^{-k-1}` (fine, `U + Δ`), on any `S` with `|t| + 1 ≤ R`. -/
theorem trlHyp_field (hX : IsFreeGFFModConstH X P) {R : ℝ} {S : Set ℝ}
    (hSR : ∀ t ∈ S, |t| + 1 ≤ R) (k : ℕ) :
    TRLHyp P S (2 * radius k) (2 * log R) (2 * log 2) (fun _ => log (1 / radius k))
      (fun _ => bV R k) (fun _ => (2 * log 2).toNNReal) (bU X R k) (bΔ X R k) := by
  have hr := radius_pos k
  have hr1 := radius_le_one k
  have hlog2 : (0 : ℝ) ≤ 2 * log 2 := mul_nonneg zero_le_two (log_nonneg one_le_two)
  have hUe : ∀ j, ∀ t : ℝ, bU X R j t =ᵐ[P] fcPairVal X ((t : ℂ), radius j, 0, R) :=
    fun j t => avgReg_zField_ae_eq hX R j (ofReal_mem_Hbar t)
  have hΔe : ∀ t : ℝ,
      bΔ X R k t =ᵐ[P] fcPairVal X ((t : ℂ), radius k / 2, (t : ℂ), radius k) := by
    intro t
    filter_upwards [hUe (k + 1) t, hUe k t] with ω h1 h2
    simp only [bΔ, h1, h2, fcPairVal, radius_succ]
    ring
  have hR : ∀ t ∈ S, |t| + radius k ≤ R := fun t ht => by linarith [hSR t ht]
  have hR0 : ∀ t ∈ S, 0 < R := fun t ht => by linarith [hSR t ht, abs_nonneg t]
  refine
    { measU := measurable_bU hX R k
      measΔ := (measurable_bU hX R (k + 1)).sub (measurable_bU hX R k)
      measL := measurable_const
      measw := measurable_const
      lawU := ?_, lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro t ht
    have := (hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar t) hr (hR0 t ht))).congr (hUe k t)
    rwa [fcPairCov_Zself hr (hR t ht)] at this
  · intro t ht
    have := (hasLaw_fcPairVal hX (good_real (s := t) (t := t) (by positivity) hr)).congr (hΔe t)
    rwa [fcPairCov_incr_self hr] at this
  · intro t ht
    have hlogR : 0 ≤ log R := log_nonneg (by linarith [hSR t ht, abs_nonneg t])
    have hlogr : log (radius k) ≤ 0 := log_nonpos hr.le hr1
    show ((2 * log R - 2 * log (radius k)).toNNReal : ℝ) ≤ 2 * log (1 / radius k) + 2 * log R
    rw [Real.coe_toNNReal _ (by linarith), one_div, log_inv]
    linarith
  · intro t _
    exact (Real.coe_toNNReal _ hlog2).le
  · intro t ht
    have hI := indepFun_fcPair hX
      (fun _ : Unit => (⟨((t : ℂ), radius k / 2, (t : ℂ), radius k),
        good_real (by positivity) hr⟩ : {p : FcIdx // p.Good}))
      (fun _ : Unit => (⟨((t : ℂ), radius k, 0, R),
        good_Z (ofReal_mem_Hbar t) hr (hR0 t ht)⟩ : {p : FcIdx // p.Good}))
      (fun _ _ => fcPairCov_incr_Zsame (by positivity) (by linarith) (hR t ht))
    have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    exact hI2.congr (hΔe t).symm (hUe k t).symm
  · intro t ht u hu htu
    have hI := indepFun_incr_bullet1 hX (t := t) (u := u) (ε := radius k / 2) (ε' := radius k)
      (r := radius k) (δ := radius k / 2) (δ' := radius k) (R := R) (by positivity)
      (by linarith) hr (by positivity) (by linarith) (hR t ht) (hR u hu)
      (by rw [max_self]; linarith)
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    refine hI2.congr (hΔe t).symm ?_
    filter_upwards [hUe k t, hUe k u, hΔe u] with ω h1 h2 h3
    simp [h1, h2, h3]

/-! ### Pathwise integrals and integrability -/

/-- `∫ f dν_k` as a Lebesgue integral over `S` when `f` vanishes off `S`. -/
theorem integral_bdryApprox_eq (γ : ℝ) (x : FieldSample) (k : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) {f : ℝ → ℝ} (hfS : ∀ t ∉ S, f t = 0) :
    ∫ t, f t ∂(bdryApprox γ x k) =
      ∫ t in S, f t * (radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg x k (t : ℂ))) := by
  have hm : Measurable (fun t : ℝ => avgReg x k (t : ℂ)) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.continuous_ofReal.measurable)
  have hg : Measurable (fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg x k (t : ℂ)))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hm.const_mul _).exp))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfS]
  unfold bdryApprox
  rw [restrict_withDensity hS,
    integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (rpow_nonneg (radius_pos k).le _) (exp_pos _).le)]
  ring

theorem integral_exp_bU [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R : ℝ}
    {S : Set ℝ} (hSR : ∀ t ∈ S, |t| + 1 ≤ R) (k : ℕ) {t : ℝ} (ht : t ∈ S) (c : ℝ) :
    ∫ ω, exp (c * bU X R k t ω) ∂P = exp (bV R k * c ^ 2 / 2) := by
  have hL := (trlHyp_field hX hSR k).lawU t ht
  have h2 := integral_exp_mul_add_gaussianReal (bV R k) c 0
  simp only [zero_add] at h2
  rw [← h2]
  exact hL.integral_comp (f := fun x => exp (c * x)) (by fun_prop)

/-- Joint integrability of `f t · dens_j(t, ω)` on `P × (vol|S)`. -/
theorem integrable_fDens [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {R : ℝ}
    {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R)
    (γ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, |f t| ≤ M) (j : ℕ) :
    Integrable (fun p : Ω × ℝ => f p.2 * bDens γ X R j p.2 p.1) (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  have h1 : Measurable (fun p : Ω × ℝ => bU X R j p.2 p.1) :=
    (measurable_avgReg j).comp (((measurable_zField hX R).comp measurable_fst).prodMk
      (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hmeas : Measurable (fun p : Ω × ℝ => f p.2 * bDens γ X R j p.2 p.1) :=
    (hf.comp measurable_snd).mul (measurable_const.mul ((h1.const_mul _).exp))
  have hr := (rpow_pos_of_pos (radius_pos j) (γ ^ 2 / 4))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · rw [ae_restrict_iff' hS]
    refine ae_of_all _ fun t ht => ?_
    have hL := (trlHyp_field hX hSR j).lawU t ht
    have hi : Integrable (fun ω => exp (0 + γ / 2 * bU X R j t ω)) P :=
      hL.integrable_fun_comp (integrable_exp_mul_add_gaussianReal _ (γ / 2) 0)
    simp only [zero_add] at hi
    exact (hi.const_mul _).const_mul (f t)
  · refine Integrable.mono' (integrable_const
      (M * (radius j ^ (γ ^ 2 / 4) * exp (bV R j * (γ / 2) ^ 2 / 2)))) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    · rw [ae_restrict_iff' hS]
      refine ae_of_all _ fun t ht => ?_
      have e : ∀ ω, ‖f t * bDens γ X R j t ω‖ =
          |f t| * (radius j ^ (γ ^ 2 / 4) * exp (γ / 2 * bU X R j t ω)) := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, bDens, abs_of_pos (mul_pos hr (exp_pos _))]
      simp_rw [e]
      rw [integral_const_mul, integral_const_mul, integral_exp_bU hX hSR j ht,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hM t) (by positivity)

omit [MeasurableSpace Ω] in
/-- The field approximant `G_j(ω) = ∫ f dν_j(Z ω)` equals `∫_S f · dens_j`. -/
theorem integral_bdryApprox_zField (γ : ℝ) (R : ℝ) (j : ℕ) {S : Set ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hfS : ∀ t ∉ S, f t = 0) (ω : Ω) :
    ∫ t, f t ∂(bdryApprox γ (zField X R ω) j) = ∫ t in S, f t * bDens γ X R j t ω :=
  integral_bdryApprox_eq γ _ j hS hfS

theorem integrable_integral_bdryApprox [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {R : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSR : ∀ t ∈ S, |t| + 1 ≤ R) (γ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, |f t| ≤ M) (hfS : ∀ t ∉ S, f t = 0) (j : ℕ) :
    Integrable (fun ω => ∫ t, f t ∂(bdryApprox γ (zField X R ω) j)) P := by
  simp_rw [integral_bdryApprox_zField γ R j hS hfS]
  exact (integrable_fDens hX hS hSf hSR γ hf hM j).integral_prod_left

/-- A.s. the density is integrable on `S` (so `ν_j(S) < ∞`). -/
theorem ae_integrableOn_bDens [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {R : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hSR : ∀ t ∈ S, |t| + 1 ≤ R) (γ : ℝ) (j : ℕ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun t => bDens γ X R j t ω) S := by
  filter_upwards [(integrable_fDens hX hS hSf hSR γ (f := fun _ => 1) measurable_const
    (M := 1) (fun _ => by simp) j).prod_right_ae] with ω hω
  simp only [one_mul] at hω
  exact hω

/-! ### The two-radius bound for consecutive dyadic levels -/

/-- **M4-B2 for the free field**: `E|∫ f dν_k − ∫ f dν_{k+1}|` is bounded by the right side of
`trl_bound`, with `δ = 2^{1-k}`, `K = 2 log R`, `W = 2 log 2`, `L = log 2^k`. -/
theorem integral_abs_bdryApprox_step_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R M : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {f : ℝ → ℝ} (hf : Measurable f)
    (hM : ∀ t, |f t| ≤ M) (hfS : ∀ t ∉ S, f t = 0) (k : ℕ) :
    ∫ ω, |∫ t, f t ∂(bdryApprox γ (zField X R ω) k) -
        ∫ t, f t ∂(bdryApprox γ (zField X R ω) (k + 1))| ∂P
      ≤ √(M ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log 2))) *
            (exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * (2 * log R) / 2) *
            exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * log (1 / radius k)))) *
            (2 * (2 * radius k) * volume.real S))
        + M * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) *
            exp (-((2 - γ) ^ 2 / 16) * log (1 / radius k)))) * volume.real S := by
  have h := trlHyp_field hX hSR k
  have hr := radius_pos k
  have hb := trl_bound hγ hγ2 (δ := 2 * radius k) (Lmin := log (1 / radius k))
    (Lmax := log (1 / radius k)) (by positivity) hS hSf hf hM h (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
  refine le_trans (le_of_eq (integral_congr_ae ?_)) hb
  filter_upwards [(integrable_fDens hX hS hSf hSR γ hf hM k).prod_right_ae,
    (integrable_fDens hX hS hSf hSR γ hf hM (k + 1)).prod_right_ae] with ω h1 h2
  rw [integral_bdryApprox_zField γ R k hS hfS, integral_bdryApprox_zField γ R (k + 1) hS hfS,
    ← integral_sub h1 h2]
  congr 1
  refine setIntegral_congr_fun hS fun t _ => ?_
  set A := bU X R k t ω with hA
  set B := bU X R (k + 1) t ω with hB
  have e1 : radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * A)
      = exp (-(γ ^ 2 / 4) * log (1 / radius k) + γ / 2 * A) := by
    rw [rpow_def_of_pos hr, ← exp_add, one_div, log_inv]; congr 1; ring
  have e2 : radius (k + 1) ^ (γ ^ 2 / 4) * exp (γ / 2 * B)
      = exp (-(γ ^ 2 / 4) * log (1 / radius k) + γ / 2 * A) *
        exp (-(γ ^ 2 / 8 * (2 * log 2)) + γ / 2 * (B - A)) := by
    rw [radius_succ, rpow_def_of_pos (by positivity), ← exp_add, ← exp_add,
      log_div hr.ne' two_ne_zero, one_div, log_inv]
    congr 1; ring
  have hlog2 : (0 : ℝ) ≤ 2 * log 2 := mul_nonneg zero_le_two (log_nonneg one_le_two)
  simp only [bDens, trlD, tiltY, bΔ, ← hA, ← hB]
  rw [Real.coe_toNNReal _ hlog2, e1, e2]
  ring

/-- The boundary rate `β(γ) = min(e₁/2, e₂)`, `e₁ = 1 − γ²/2 + θ²`, `e₂ = (2−γ)²/16`. -/
def bdryRate (γ : ℝ) : ℝ :=
  min ((1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2) / 2) ((2 - γ) ^ 2 / 16)

theorem bdryRate_e1_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    0 < 1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2 := by
  rcases le_total ((3 * γ - 2) / 4) 0 with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

theorem bdryRate_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < bdryRate γ := by
  unfold bdryRate
  have := bdryRate_e1_pos hγ hγ2
  have h2 : 0 < (2 - γ) ^ 2 / 16 := div_pos (pow_pos (by linarith) 2) (by norm_num)
  exact lt_min (by linarith) h2

/-- **Rate form (M4-B3, input):** `E|∫ f dν_k − ∫ f dν_{k+1}| ≤ C e^{-β k log 2}`,
`β = bdryRate γ > 0`, uniformly in `k`. -/
theorem integral_abs_bdryApprox_step_le_rate [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R M : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {f : ℝ → ℝ}
    (hf : Measurable f) (hM : ∀ t, |f t| ≤ M) (hfS : ∀ t ∉ S, f t = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ,
      ∫ ω, |∫ t, f t ∂(bdryApprox γ (zField X R ω) k) -
        ∫ t, f t ∂(bdryApprox γ (zField X R ω) (k + 1))| ∂P
        ≤ C * exp (-bdryRate γ * (k * log 2)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set θ := max 0 ((3 * γ - 2) / 4) with hθ
  set e₁ := 1 - γ ^ 2 / 2 + θ ^ 2 with he₁
  set β := bdryRate γ with hβ
  have hβ1 : β ≤ e₁ / 2 := min_le_left _ _
  have hβ2 : β ≤ (2 - γ) ^ 2 / 16 := min_le_right _ _
  set c₁ := M ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log 2))) *
      exp ((γ - θ) ^ 2 * (2 * log R) / 2)) * (4 * volume.real S) with hc₁
  set c₂ := M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2)) * volume.real S
    with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨√c₁ + c₂, by positivity, fun k => ?_⟩
  refine (integral_abs_bdryApprox_step_le hX hγ hγ2 hS hSf hSR hf hM hfS k).trans ?_
  set L := log (1 / radius k) with hL
  have hLk : L = k * log 2 := log_one_div_radius k
  have hL0 : 0 ≤ L := by rw [hLk]; exact mul_nonneg (Nat.cast_nonneg k) (log_nonneg one_le_two)
  have hrad : radius k = exp (-L) := by
    rw [hL, one_div, log_inv, neg_neg, exp_log (radius_pos k)]
  have hin : M ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log 2))) *
        (exp ((γ - θ) ^ 2 * (2 * log R) / 2) * exp ((γ ^ 2 / 2 - θ ^ 2) * L))) *
        (2 * (2 * radius k) * volume.real S) = c₁ * exp (-e₁ * L) := by
    rw [hrad, hc₁, he₁]
    have : exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L) = exp (-(1 - γ ^ 2 / 2 + θ ^ 2) * L) := by
      rw [← exp_add]; congr 1; ring
    calc _ = M ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log 2))) *
          exp ((γ - θ) ^ 2 * (2 * log R) / 2)) * (4 * volume.real S) *
          (exp ((γ ^ 2 / 2 - θ ^ 2) * L) * exp (-L)) := by ring
      _ = _ := by rw [this]
  have hexp1 : exp (-e₁ * L) ≤ exp (-β * L) ^ 2 := by
    rw [← exp_nat_mul]; apply exp_le_exp.2; push_cast; nlinarith
  have hexp2 : exp (-((2 - γ) ^ 2 / 16) * L) ≤ exp (-β * L) := by
    apply exp_le_exp.2; nlinarith
  rw [hin, ← hLk]
  have ht1 : √(c₁ * exp (-e₁ * L)) ≤ √c₁ * exp (-β * L) := by
    rw [← Real.sqrt_sq (exp_pos (-β * L)).le, ← Real.sqrt_mul hc₁0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hexp1 hc₁0)
  have ht2 : M * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) *
      exp (-((2 - γ) ^ 2 / 16) * L))) * volume.real S ≤ c₂ * exp (-β * L) := by
    rw [hc₂]
    calc _ = M * (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2)) * volume.real S *
          exp (-((2 - γ) ^ 2 / 16) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp2 (by positivity)
  calc _ ≤ √c₁ * exp (-β * L) + c₂ * exp (-β * L) := add_le_add ht1 ht2
    _ = (√c₁ + c₂) * exp (-β * L) := by ring

theorem geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, q ^ i ≤ 1 / (1 - q) := by
  have h1 : 0 < 1 - q := by linarith
  have e : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [← neg_sub (1 : ℝ) (q ^ n), ← neg_sub (1 : ℝ) q, neg_div_neg_eq]
  rw [geom_sum_eq hq1.ne, e]
  exact (div_le_div_iff_of_pos_right h1).2 (by linarith [pow_nonneg hq0 n])

/-- **Telescoped rate (goal 1 of M4-B3)**: for `k ≤ k' = k + n`,
`E|∫ f dν_{k'} − ∫ f dν_k| ≤ C e^{-β k log 2}`, uniformly in `n`. -/
theorem integral_abs_bdryApprox_le_rate [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R M : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {f : ℝ → ℝ}
    (hf : Measurable f) (hM : ∀ t, |f t| ≤ M) (hfS : ∀ t ∉ S, f t = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k n : ℕ,
      ∫ ω, |∫ t, f t ∂(bdryApprox γ (zField X R ω) (k + n)) -
        ∫ t, f t ∂(bdryApprox γ (zField X R ω) k)| ∂P
        ≤ C * exp (-bdryRate γ * (k * log 2)) := by
  obtain ⟨C, hC0, hC⟩ :=
    integral_abs_bdryApprox_step_le_rate hX hγ hγ2 hS hSf hSR hf hM hfS
  set G : ℕ → Ω → ℝ := fun j ω => ∫ t, f t ∂(bdryApprox γ (zField X R ω) j) with hG
  have hint : ∀ j, Integrable (G j) P :=
    integrable_integral_bdryApprox hX hS hSf hSR γ hf hM hfS
  set q := exp (-bdryRate γ * log 2) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]
    have := bdryRate_pos hγ hγ2
    have := log_pos one_lt_two
    nlinarith
  have hpow : ∀ j : ℕ, exp (-bdryRate γ * (j * log 2)) = q ^ j := by
    intro j; rw [hq, ← exp_nat_mul]; congr 1; ring
  refine ⟨C / (1 - q), div_nonneg hC0 (by linarith), fun k n => ?_⟩
  have hpt : ∀ ω, |G (k + n) ω - G k ω| ≤
      ∑ i ∈ Finset.range n, |G (k + i) ω - G (k + i + 1) ω| := by
    intro ω
    have := dist_le_range_sum_dist (fun i => G (k + i) ω) n
    simp only [Real.dist_eq, add_zero] at this
    rw [abs_sub_comm]
    simpa [add_assoc] using this
  calc ∫ ω, |G (k + n) ω - G k ω| ∂P
      ≤ ∫ ω, ∑ i ∈ Finset.range n, |G (k + i) ω - G (k + i + 1) ω| ∂P := by
        refine integral_mono ((hint _).sub (hint _)).abs
          (integrable_finsetSum _ fun i _ => ((hint _).sub (hint _)).abs) hpt
    _ = ∑ i ∈ Finset.range n, ∫ ω, |G (k + i) ω - G (k + i + 1) ω| ∂P :=
        integral_finsetSum _ fun i _ => ((hint _).sub (hint _)).abs
    _ ≤ ∑ i ∈ Finset.range n, C * q ^ k * q ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (hC (k + i)).trans (le_of_eq ?_)
        rw [hpow, pow_add]; ring
    _ = C * q ^ k * ∑ i ∈ Finset.range n, q ^ i := by rw [Finset.mul_sum]
    _ ≤ C * q ^ k * (1 / (1 - q)) :=
        mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub hq0.le hq1 n) (by positivity)
    _ = C / (1 - q) * exp (-bdryRate γ * (k * log 2)) := by rw [hpow]; ring

end BdryExist
end QuantumZipper
