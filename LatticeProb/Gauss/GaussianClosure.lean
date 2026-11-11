import Mathlib
import LatticeProb.Gauss.Limit

/-!
# Centred Gaussian spaces are closed under almost sure limits

A family of real random variables is a *centred Gaussian space* if each of its elements is measurable and centred
Gaussian. Such a space is closed under almost sure limits, as the Gaussian Hilbert space of a Gaussian process
(Duplantier-Sheffield, arXiv:0808.1560, Sec. 3.1):

* `exists_map_eq_gaussianReal_of_tendsto_ae`: an almost sure limit of centred Gaussians is a centred Gaussian. No
  hypothesis on the variances is needed: the characteristic functions `exp(-σ_n t²/2)` converge, and a limit `0` at
  `t = 1` would make the characteristic function of the limit vanish on `{1/(m+1)}`, against its continuity at `0`.
  The case of convergent variances is `LatticeProb.map_eq_gaussianReal_of_tendsto_ae` (LatticeProb/Gauss/Limit.lean).
* `isCentredGaussianSpace_sup_span`, `isCentredGaussianSpace_sup_span_finset`,
  `isCentredGaussianSpace_sup_span_range`: adjoining almost sure limits of elements of a centred Gaussian linear space
  keeps it a centred Gaussian linear space.
* `tendsto_variance_of_tendsto_ae`, `tendsto_covariance_of_tendsto_ae`: variances and covariances are continuous along
  almost sure limits in a centred Gaussian space; covariances are polarized variances (Armitage-Gardiner, Classical
  Potential Theory, Sec. 3.1, for the bilinear calculus used here).
-/

noncomputable section

namespace LatticeProb.GaussianClosure

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The characteristic function `t ↦ E[e^{itZ}]` of a real random variable `Z` under `P`. -/
noncomputable def cf (P : Measure Ω) (Z : Ω → ℝ) (t : ℝ) : ℂ :=
  ∫ ω, Complex.exp ((t : ℂ) * (Z ω : ℂ) * Complex.I) ∂P

lemma norm_exp_mul_I (t u : ℝ) : ‖Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I)‖ = 1 := by
  rw [show (t : ℂ) * (u : ℂ) * Complex.I = ((t * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma tendsto_cf_of_tendsto_ae [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hXm : ∀ n, Measurable (X n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) (t : ℝ) :
    Tendsto (fun n => cf P (X n) t) atTop (𝓝 (cf P Y t)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const 1)
    (fun n => Eventually.of_forall fun ω => le_of_eq (norm_exp_mul_I _ _)) ?_
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (hXm n)).const_mul _ |>.mul_const _)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    exact (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp hω).const_mul _ |>.mul_const _)

lemma tendsto_cf_param [IsFiniteMeasure P] {Y : Ω → ℝ} (hYm : Measurable Y) {τ : ℕ → ℝ} {t : ℝ}
    (hτ : Tendsto τ atTop (𝓝 t)) : Tendsto (fun m => cf P Y (τ m)) atTop (𝓝 (cf P Y t)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun m => ?_) (integrable_const 1)
    (fun m => Eventually.of_forall fun ω => le_of_eq (norm_exp_mul_I _ _)) (Eventually.of_forall fun ω => ?_)
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hYm).const_mul _ |>.mul_const _)).aestronglyMeasurable
  · exact (Complex.continuous_exp.tendsto _).comp
      ((((Complex.continuous_ofReal.tendsto _).comp hτ).mul_const _).mul_const _)

lemma cf_zero [IsProbabilityMeasure P] (Y : Ω → ℝ) : cf P Y 0 = 1 := by
  simp [cf]

lemma cf_eq_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) (t : ℝ) :
    cf P Z t = ((Real.exp (-(v : ℝ) * t ^ 2 / 2) : ℝ) : ℂ) := by
  have h1 : charFun (P.map Z) t = cf P Z t := by
    rw [charFun_apply_real, integral_map hZ.aemeasurable]
    · rfl
    exact (Complex.measurable_exp.comp (Complex.measurable_ofReal.const_mul _ |>.mul_const _)).aestronglyMeasurable
  rw [← h1, h, charFun_gaussianReal]
  push_cast
  ring_nf

/-- **An almost sure limit of centred Gaussians is a centred Gaussian.** -/
theorem exists_map_eq_gaussianReal_of_tendsto_ae [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y) (hX : ∀ n, ∃ v : ℝ≥0, P.map (X n) = gaussianReal 0 v)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v := by
  choose σ hσ using hX
  have hre : ∀ t, Tendsto (fun n => Real.exp (-(σ n : ℝ) * t ^ 2 / 2)) atTop (𝓝 (cf P Y t).re) := by
    intro t
    refine ((Complex.continuous_re.tendsto _).comp (tendsto_cf_of_tendsto_ae hXm hae t)).congr fun n => ?_
    simp only [Function.comp_apply, cf_eq_of_map_eq (hXm n) (hσ n) t, Complex.ofReal_re]
  have hL0 : 0 ≤ (cf P Y 1).re := ge_of_tendsto' (hre 1) fun n => (Real.exp_pos _).le
  rcases hL0.lt_or_eq with hL | hL
  · have hlog : Tendsto (fun n => (σ n : ℝ)) atTop (𝓝 (-2 * Real.log (cf P Y 1).re)) := by
      refine (((Real.continuousAt_log hL.ne').tendsto.comp (hre 1)).const_mul (-2)).congr fun n => ?_
      simp only [Function.comp_apply, Real.log_exp]
      ring
    have hL1 : (cf P Y 1).re ≤ 1 := le_of_tendsto' (hre 1) fun n =>
      Real.exp_le_one_iff.2 (by have := (σ n).2; nlinarith)
    have hv : 0 ≤ -2 * Real.log (cf P Y 1).re := by nlinarith [Real.log_nonpos hL0 hL1]
    exact ⟨⟨_, hv⟩, LatticeProb.map_eq_gaussianReal_of_tendsto_ae hXm hYm hσ hae hlog⟩
  · exfalso
    have hzero : ∀ m : ℕ, (cf P Y (1 / ((m : ℝ) + 1))).re = 0 := by
      intro m
      have hq : 0 < (1 / ((m : ℝ) + 1)) ^ 2 := by positivity
      have h1 := ((Real.continuous_rpow_const hq.le).tendsto _).comp (hre 1)
      rw [← hL, Real.zero_rpow hq.ne'] at h1
      refine tendsto_nhds_unique (hre _) (h1.congr fun n => ?_)
      rw [Function.comp_apply, ← Real.exp_mul]
      congr 1
      ring
    have hlim := (Complex.continuous_re.tendsto _).comp (tendsto_cf_param (P := P) hYm
      tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [cf_zero, Complex.one_re] at hlim
    have h0 : Tendsto (fun m : ℕ => (0 : ℝ)) atTop (𝓝 1) := hlim.congr fun m => hzero m
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h0)

/-! ## Centred Gaussian spaces -/

/-- Every element of `M` is a measurable centred Gaussian random variable. -/
def IsCentredGaussianSpace (P : Measure Ω) (M : Set (Ω → ℝ)) : Prop :=
  ∀ Y ∈ M, Measurable Y ∧ ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v

/-- `Z` is the almost sure limit of a sequence of elements of `M`. -/
def IsAeLimitOf (P : Measure Ω) (M : Set (Ω → ℝ)) (Z : Ω → ℝ) : Prop :=
  ∃ Y : ℕ → Ω → ℝ, (∀ n, Y n ∈ M) ∧ ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))

lemma IsAeLimitOf.mono {M M' : Set (Ω → ℝ)} (h : M ⊆ M') {Z : Ω → ℝ} (hZ : IsAeLimitOf P M Z) :
    IsAeLimitOf P M' Z := by
  obtain ⟨Y, hY, hlim⟩ := hZ
  exact ⟨Y, fun n => h (hY n), hlim⟩

lemma isAeLimitOf_of_mem {M : Set (Ω → ℝ)} {Z : Ω → ℝ} (hZ : Z ∈ M) : IsAeLimitOf P M Z :=
  ⟨fun _ => Z, fun _ => hZ, Eventually.of_forall fun _ => tendsto_const_nhds⟩

/-- Adjoining an almost sure limit to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : IsAeLimitOf P M Z) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ {Z} : Submodule ℝ (Ω → ℝ)) := by
  intro W hW
  obtain ⟨Y, hY, U, hU, rfl⟩ := Submodule.mem_sup.1 hW
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hU
  obtain ⟨Yn, hYn, hlim⟩ := hZ
  have hm : Measurable (Y + c • Z) := (hM Y hY).1.add (hZm.const_smul c)
  have hmem : ∀ n, Y + c • Yn n ∈ M := fun n => M.add_mem hY (M.smul_mem c (hYn n))
  refine ⟨hm, exists_map_eq_gaussianReal_of_tendsto_ae (X := fun n => Y + c • Yn n)
    (fun n => (hM _ (hmem n)).1) hm (fun n => (hM _ (hmem n)).2) ?_⟩
  filter_upwards [hlim] with ω hω
  exact tendsto_const_nhds.add (hω.const_smul c)

/-- Adjoining finitely many almost sure limits to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span_finset [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) (T : Finset (Ω → ℝ)) (hTm : ∀ Z ∈ T, Measurable Z)
    (hT : ∀ Z ∈ T, IsAeLimitOf P M Z) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ (T : Set (Ω → ℝ)) : Submodule ℝ (Ω → ℝ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hM
  | insert Z T hZT ih =>
    have hT' := ih (fun Z' h => hTm Z' (Finset.mem_insert_of_mem h))
      (fun Z' h => hT Z' (Finset.mem_insert_of_mem h))
    have heq : M ⊔ Submodule.span ℝ ((insert Z T : Finset (Ω → ℝ)) : Set (Ω → ℝ)) =
        (M ⊔ Submodule.span ℝ (T : Set (Ω → ℝ))) ⊔ Submodule.span ℝ {Z} := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_comm (Submodule.span ℝ {Z}), sup_assoc]
    rw [heq]
    exact isCentredGaussianSpace_sup_span hT' (hTm Z (Finset.mem_insert_self Z T))
      ((hT Z (Finset.mem_insert_self Z T)).mono
        (SetLike.coe_subset_coe.2 (le_sup_left : M ≤ M ⊔ Submodule.span ℝ (T : Set (Ω → ℝ)))))

/-- Adjoining a countable family of almost sure limits to a centred Gaussian linear space. -/
theorem isCentredGaussianSpace_sup_span_range [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {ι : Type*} (Z : ι → Ω → ℝ) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, IsAeLimitOf P M (Z i)) :
    IsCentredGaussianSpace P (M ⊔ Submodule.span ℝ (Set.range Z) : Submodule ℝ (Ω → ℝ)) := by
  intro W hW
  obtain ⟨Y, hY, U, hU, rfl⟩ := Submodule.mem_sup.1 hW
  obtain ⟨T, hTsub, hUT⟩ := Submodule.mem_span_finite_of_mem_span hU
  have hgood := isCentredGaussianSpace_sup_span_finset hM T
    (fun Z' h => by obtain ⟨i, rfl⟩ := hTsub h; exact hZm i)
    (fun Z' h => by obtain ⟨i, rfl⟩ := hTsub h; exact hZ i)
  exact hgood _ (Submodule.add_mem_sup hY hUT)

/-- **Joint Gaussianity.** A family of elements of a centred Gaussian linear space is a Gaussian process. -/
theorem isGaussianProcess_of_isCentredGaussianSpace [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {T : Type*} {W : T → Ω → ℝ} (hW : ∀ t, W t ∈ M) :
    IsGaussianProcess W P := by
  classical
  refine ⟨fun I => ?_⟩
  have hmeas : Measurable fun ω => I.restrict fun x => W x ω :=
    measurable_pi_iff.2 fun i => (hM _ (hW i)).1
  refine ⟨hmeas.aemeasurable, IsGaussian.mk fun L => ?_⟩
  set μ := P.map fun ω => I.restrict fun x => W x ω
  have hcomb : (fun ω => L (I.restrict fun x => W x ω)) =
      ∑ i : I, L (fun j => if i = j then 1 else 0) • W i := by
    funext ω
    rw [show L (I.restrict fun x => W x ω) = (L : (I → ℝ) →ₗ[ℝ] ℝ) (I.restrict fun x => W x ω) from rfl,
      LinearMap.pi_apply_eq_sum_univ]
    simp [Finset.sum_apply, mul_comm]
  have hmem : (fun ω => L (I.restrict fun x => W x ω)) ∈ M := by
    rw [hcomb]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hW i)
  obtain ⟨-, v, hv⟩ := hM _ hmem
  have hL : μ.map L = gaussianReal 0 v := by
    rw [Measure.map_map L.continuous.measurable hmeas]
    exact hv
  have hint : ∫ x, L x ∂μ = 0 := by
    have h := integral_map (μ := μ) L.continuous.measurable.aemeasurable
      (aestronglyMeasurable_id (μ := μ.map L))
    simp only [id_eq] at h
    rw [← h, hL, integral_id_gaussianReal]
  have hvar : Var[⇑L; μ] = v := by
    rw [← variance_id_map L.continuous.measurable.aemeasurable, hL, variance_id_gaussianReal]
  rw [hL, hint, hvar, Real.toNNReal_coe]

/-! ## Variances and covariances along almost sure limits -/

lemma memLp_two_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) :
    MemLp Z 2 P := by
  have hG : HasGaussianLaw Z P := ⟨hZ.aemeasurable, by rw [h]; infer_instance⟩
  exact hG.memLp_two

lemma variance_of_map_eq {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ≥0} (h : P.map Z = gaussianReal 0 v) :
    Var[Z; P] = v := by
  rw [← variance_id_map hZ.aemeasurable, h, variance_id_gaussianReal]

lemma IsCentredGaussianSpace.memLp {M : Set (Ω → ℝ)} (hM : IsCentredGaussianSpace P M) {Z : Ω → ℝ} (hZ : Z ∈ M) :
    MemLp Z 2 P :=
  memLp_two_of_map_eq (hM Z hZ).1 (hM Z hZ).2.choose_spec

/-- Variances of centred Gaussians are continuous along almost sure limits. -/
lemma tendsto_variance_of_tendsto_ae [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y) (hX : ∀ n, ∃ v : ℝ≥0, P.map (X n) = gaussianReal 0 v)
    (hY : ∃ v : ℝ≥0, P.map Y = gaussianReal 0 v) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => Var[X n; P]) atTop (𝓝 Var[Y; P]) := by
  choose σ hσ using hX
  obtain ⟨v, hv⟩ := hY
  have hre : Tendsto (fun n => Real.exp (-(σ n : ℝ) * 1 ^ 2 / 2)) atTop
      (𝓝 (Real.exp (-(v : ℝ) * 1 ^ 2 / 2))) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_cf_of_tendsto_ae hXm hae 1)
    rw [cf_eq_of_map_eq hYm hv, Complex.ofReal_re] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, cf_eq_of_map_eq (hXm n) (hσ n), Complex.ofReal_re]
  have hlog := ((Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hre).const_mul (-2)
  have e : ∀ a : ℝ, -2 * (-a * 1 ^ 2 / 2) = a := fun a => by ring
  simp only [Function.comp_def, Real.log_exp, e] at hlog
  rw [variance_of_map_eq hYm hv]
  exact hlog.congr fun n => (variance_of_map_eq (hXm n) (hσ n)).symm

lemma covariance_eq_polar [IsFiniteMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    cov[X, Y; P] = (Var[X + Y; P] - Var[X - Y; P]) / 4 := by
  rw [variance_add hX hY, variance_sub hX hY]
  ring

/-- **Covariances are continuous along almost sure limits in a centred Gaussian linear space.** -/
theorem tendsto_covariance_of_tendsto_ae [IsProbabilityMeasure P] {M : Submodule ℝ (Ω → ℝ)}
    (hM : IsCentredGaussianSpace P M) {X : Ω → ℝ} (hX : X ∈ M) {Z : ℕ → Ω → ℝ} (hZ : ∀ n, Z n ∈ M)
    {Y : Ω → ℝ} (hY : Y ∈ M) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => cov[X, Z n; P]) atTop (𝓝 cov[X, Y; P]) := by
  have hadd := tendsto_variance_of_tendsto_ae (X := fun n => X + Z n) (Y := X + Y)
    (fun n => (hM _ (M.add_mem hX (hZ n))).1) (hM _ (M.add_mem hX hY)).1
    (fun n => (hM _ (M.add_mem hX (hZ n))).2) (hM _ (M.add_mem hX hY)).2
    (by filter_upwards [hae] with ω hω; exact tendsto_const_nhds.add hω)
  have hsub := tendsto_variance_of_tendsto_ae (X := fun n => X - Z n) (Y := X - Y)
    (fun n => (hM _ (M.sub_mem hX (hZ n))).1) (hM _ (M.sub_mem hX hY)).1
    (fun n => (hM _ (M.sub_mem hX (hZ n))).2) (hM _ (M.sub_mem hX hY)).2
    (by filter_upwards [hae] with ω hω; exact tendsto_const_nhds.sub hω)
  rw [covariance_eq_polar (hM.memLp hX) (hM.memLp hY)]
  exact ((hadd.sub hsub).div_const 4).congr fun n =>
    (covariance_eq_polar (hM.memLp hX) (hM.memLp (hZ n))).symm

end LatticeProb.GaussianClosure

end
