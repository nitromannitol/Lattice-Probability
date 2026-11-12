/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.Chatterjee at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Gaussian.SudakovFernique
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Chatterjee's error bound: expected maxima are Lipschitz in the covariance (node `G6`)

We prove `Blueprint.Draft.ExpectedMaxCovLipschitz`: if `C₁`, `C₂` are positive semidefinite on
a finite set `F` and `|C₁ i j - C₂ i j| ≤ γ` on `F × F`, then
`|E max_F (X + b) - E max_F (Y + b)| ≤ 2 √(2 γ log |F|)`.

The proof is the Sudakov–Fernique interpolation of `LQGDimension.Gaussian.SudakovFernique`:
realise `C₁`, `C₂` as Gram matrices of orthogonal families `u`, `u'`, and put
`φ(θ) = E[F_β((⟪cos θ u i + sin θ u' i, x⟫ + b i)_i)]` with the smooth maximum `F_β`.  After
Gaussian integration by parts,
`φ'(θ) = β cos θ sin θ · E ∑_i p_i (D_ii - ∑_j p_j D_ji)`, `D = C₂ - C₁`,
and since `p` is a probability vector, `|∑_i p_i (D_ii - ∑_j p_j D_ji)| ≤ 2γ`; with
`|cos θ sin θ| ≤ 1/2` this gives `|φ'| ≤ βγ`, hence `|φ(π/2) - φ(0)| ≤ βγ π/2`.  Together with
`max ≤ F_β ≤ max + log|F|/β` we get `|ΔE max| ≤ log|F|/β + βγπ/2` for all `β > 0`, and
optimizing in `β` gives `(1 + π/2) √(γ log|F|) ≤ 2 √(2 γ log |F|)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension

namespace Chatterjee

open SudakovFernique

/-! ### The algebraic bound on the derivative -/

section Algebra

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For probability weights `p` on `F` and `|D i j| ≤ γ` on `F`,
`|∑_i p_i (D_ii - ∑_j p_j D_ji)| ≤ 2γ`. -/
lemma abs_sum_weighted_quad_le (F : Finset ι) (D : ι → ι → ℝ) {γ : ℝ}
    (hD : ∀ i ∈ F, ∀ j ∈ F, |D i j| ≤ γ) {p : ι → ℝ} (hp : ∀ i ∈ F, 0 ≤ p i)
    (hp1 : ∑ i ∈ F, p i = 1) :
    |∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i)| ≤ 2 * γ := by
  have hinner : ∀ i ∈ F, |∑ j ∈ F, p j * D j i| ≤ γ := by
    intro i hi
    calc |∑ j ∈ F, p j * D j i| ≤ ∑ j ∈ F, |p j * D j i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ F, p j * γ := Finset.sum_le_sum fun j hj => by
          rw [abs_mul, abs_of_nonneg (hp j hj)]
          exact mul_le_mul_of_nonneg_left (hD j hj i hi) (hp j hj)
      _ = γ := by rw [← Finset.sum_mul, hp1, one_mul]
  calc |∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i)|
      ≤ ∑ i ∈ F, |p i * (D i i - ∑ j ∈ F, p j * D j i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F, p i * (2 * γ) := Finset.sum_le_sum fun i hi => by
        rw [abs_mul, abs_of_nonneg (hp i hi)]
        refine mul_le_mul_of_nonneg_left ?_ (hp i hi)
        have h1 := hD i hi i hi
        have h2 := hinner i hi
        rw [abs_le] at h1 h2 ⊢
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    _ = 2 * γ := by rw [← Finset.sum_mul, hp1, one_mul]

lemma abs_cos_mul_sin_le (θ : ℝ) : |Real.cos θ * Real.sin θ| ≤ 1 / 2 := by
  have h := Real.abs_sin_le_one (2 * θ)
  rw [Real.sin_two_mul, show 2 * Real.sin θ * Real.cos θ = 2 * (Real.cos θ * Real.sin θ) by ring,
    abs_mul, abs_two] at h
  linarith

/-- The pointwise bound on the integrand of `φ'` (after integration by parts). -/
lemma abs_interp_quadratic_le (F : Finset ι) {u u' : ι → H} (horth : ∀ i j, ⟪u i, u' j⟫ = 0)
    {γ : ℝ} (hγ : ∀ i ∈ F, ∀ j ∈ F, |⟪u' i, u' j⟫ - ⟪u i, u j⟫| ≤ γ)
    {p : ι → ℝ} (hp : ∀ i ∈ F, 0 ≤ p i) (hp1 : ∑ i ∈ F, p i = 1) (θ : ℝ) :
    |∑ i ∈ F, p i * (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
      ∑ j ∈ F, p j * ⟪interpVec u u' θ j, interpVec' u u' θ i⟫)| ≤ γ := by
  set D : ι → ι → ℝ := fun j i => ⟪u' j, u' i⟫ - ⟪u j, u i⟫ with hDdef
  have e : ∑ i ∈ F, p i * (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
      ∑ j ∈ F, p j * ⟪interpVec u u' θ j, interpVec' u u' θ i⟫) =
      Real.cos θ * Real.sin θ * ∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_interpVec_interpVec' horth, hDdef]
    rw [show ∑ j ∈ F, p j * (Real.cos θ * Real.sin θ * (⟪u' j, u' i⟫ - ⟪u j, u i⟫)) =
        Real.cos θ * Real.sin θ * ∑ j ∈ F, p j * (⟪u' j, u' i⟫ - ⟪u j, u i⟫) by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring]
    ring
  rw [e, abs_mul]
  have h1 := abs_sum_weighted_quad_le F D hγ hp hp1
  have h2 := abs_cos_mul_sin_le θ
  calc |Real.cos θ * Real.sin θ| * |∑ i ∈ F, p i * (D i i - ∑ j ∈ F, p j * D j i)|
      ≤ (1 / 2) * (2 * γ) := mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
    _ = γ := by ring

end Algebra

/-! ### The derivative of the interpolation -/

section Gaussian

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- Gaussian integration by parts in the derivative of the interpolation. -/
lemma integral_interpDeriv_eq {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) :
    ∫ x, interpDeriv F β u u' b θ x ∂(stdGaussian H) =
      ∫ x, β * ∑ i ∈ F, softmax F β (interpZ u u' b θ x) i *
        (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
          ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j *
            ⟪interpVec u u' θ j, interpVec' u u' θ i⟫) ∂(stdGaussian H) := by
  have hp : ∀ j, Continuous fun x => softmax F β (interpZ u u' b θ x) j := fun j =>
    continuous_softmax hF β (fun k => continuous_interpZ u u' b θ k) j
  have hint1 : ∀ i ∈ F, Integrable (fun x => ⟪interpVec' u u' θ i, x⟫ *
      softmax F β (interpZ u u' b θ x) i) (stdGaussian H) := by
    intro i hi
    exact (IsGaussian.integrable_fun_id.const_inner (interpVec' u u' θ i)).mul_bdd
      (hp i).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_softmax_le_one β _ hi)
  have hint2 : ∀ i ∈ F, Integrable (fun x => ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫)
      (stdGaussian H) := by
    intro i hi
    refine Integrable.of_bound
      ((continuous_steinGrad hF β u u' b θ i).inner continuous_const).aestronglyMeasurable
      (β * (‖interpVec u u' θ i‖ + ∑ j ∈ F, ‖interpVec u u' θ j‖) * ‖interpVec' u u' θ i‖)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    gcongr
    exact norm_steinGrad_le hβ u u' b θ hi x
  have hsum : ∫ x, interpDeriv F β u u' b θ x ∂(stdGaussian H) =
      ∫ x, ∑ i ∈ F, ⟪steinGrad F β u u' b θ i x, interpVec' u u' θ i⟫ ∂(stdGaussian H) := by
    rw [integral_finsetSum _ hint2]
    rw [← Finset.sum_congr rfl fun i hi =>
      integral_inner_mul_softmax hF hβ u u' b θ hi (interpVec' u u' θ i)]
    rw [← integral_finsetSum _ hint1]
    congr 1
    funext x
    unfold interpDeriv
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]
  congr 1
  funext x
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [steinGrad, real_inner_smul_left, inner_sub_left, sum_inner]
  ring

/-- **The derivative of the interpolation is bounded by `βγ`.** -/
lemma abs_integral_interpDeriv_le {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    {u u' : ι → H} (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0) {γ : ℝ}
    (hγ : ∀ i ∈ F, ∀ j ∈ F, |⟪u' i, u' j⟫ - ⟪u i, u j⟫| ≤ γ) (θ : ℝ) :
    |∫ x, interpDeriv F β u u' b θ x ∂(stdGaussian H)| ≤ β * γ := by
  rw [integral_interpDeriv_eq hF hβ]
  have hb : ∀ x : H, ‖β * ∑ i ∈ F, softmax F β (interpZ u u' b θ x) i *
      (⟪interpVec u u' θ i, interpVec' u u' θ i⟫ -
        ∑ j ∈ F, softmax F β (interpZ u u' b θ x) j *
          ⟪interpVec u u' θ j, interpVec' u u' θ i⟫)‖ ≤ β * γ := fun x => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (abs_interp_quadratic_le F horth hγ
      (fun i _ => softmax_nonneg F β _ i) (sum_softmax hF β _) θ) hβ.le
  have h := norm_integral_le_of_norm_le_const (μ := stdGaussian H) (ae_of_all _ hb)
  rw [Real.norm_eq_abs] at h
  simpa using h

/-- `|φ(π/2) - φ(0)| ≤ βγ π/2`. -/
lemma abs_interpPhi_sub_le {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    {u u' : ι → H} (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0) {γ : ℝ}
    (hγ : ∀ i ∈ F, ∀ j ∈ F, |⟪u' i, u' j⟫ - ⟪u i, u j⟫| ≤ γ) :
    |interpPhi F β u u' b (π / 2) - interpPhi F β u u' b 0| ≤ β * γ * (π / 2) := by
  have hd := fun θ => hasDerivAt_interpPhi (H := H) hF hβ u u' b θ
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := interpPhi F β u u' b)
    (s := univ) (x := 0) (y := π / 2) (C := β * γ)
    (fun θ _ => (hd θ).hasDerivWithinAt)
    (fun θ _ => by
      rw [Real.norm_eq_abs]
      exact abs_integral_interpDeriv_le hF hβ b horth hγ θ)
    convex_univ (mem_univ _) (mem_univ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < π / 2)]
    at h
  exact h

omit [BorelSpace H] in
/-- Comparison of the smooth interpolation with the expected maximum at a fixed `θ`. -/
lemma vecExpectedMax_interpPhi_bounds {F : Finset ι} (hF : F.Nonempty) {β : ℝ} (hβ : 0 < β)
    (u u' : ι → H) (b : ι → ℝ) (θ : ℝ) (w : ι → H)
    (hw : ∀ x i, interpZ u u' b θ x i = ⟪w i, x⟫ + b i)
    (hint : Integrable (fun x => ⨆ i : F, ⟪w i, x⟫ + b i) (stdGaussian H))
    (hint' : Integrable (fun x => smoothMax F β (interpZ u u' b θ x)) (stdGaussian H)) :
    vecExpectedMax F w b ≤ interpPhi F β u u' b θ ∧
      interpPhi F β u u' b θ ≤ vecExpectedMax F w b + Real.log F.card / β := by
  unfold vecExpectedMax interpPhi
  constructor
  · refine integral_mono hint hint' fun x => ?_
    have := iSup_le_smoothMax hF hβ (interpZ u u' b θ x)
    simpa only [hw] using this
  · have hle : ∀ x, smoothMax F β (interpZ u u' b θ x) ≤
        (⨆ i : F, ⟪w i, x⟫ + b i) + Real.log F.card / β := fun x => by
      have := smoothMax_le_iSup hF hβ (interpZ u u' b θ x)
      simpa only [hw] using this
    calc ∫ x, smoothMax F β (interpZ u u' b θ x) ∂(stdGaussian H)
        ≤ ∫ x, ((⨆ i : F, ⟪w i, x⟫ + b i) + Real.log F.card / β) ∂(stdGaussian H) :=
          integral_mono hint' (hint.fun_add (integrable_const _)) hle
      _ = ∫ x, (⨆ i : F, ⟪w i, x⟫ + b i) ∂(stdGaussian H) + Real.log F.card / β := by
          rw [integral_add hint (integrable_const _), integral_const]
          simp

/-- **Chatterjee's bound for two orthogonal families**, for each `β > 0`. -/
theorem abs_vecExpectedMax_sub_le_of_orthogonal {F : Finset ι} (hF : F.Nonempty) {β : ℝ}
    (hβ : 0 < β) (u u' : ι → H) (b : ι → ℝ) (horth : ∀ i j, ⟪u i, u' j⟫ = 0) {γ : ℝ}
    (hγ : ∀ i ∈ F, ∀ j ∈ F, |⟪u' i, u' j⟫ - ⟪u i, u j⟫| ≤ γ) :
    |vecExpectedMax F u b - vecExpectedMax F u' b| ≤
      Real.log F.card / β + β * γ * (π / 2) := by
  have h0 := vecExpectedMax_interpPhi_bounds hF hβ u u' b 0 u
    (fun x i => interpZ_zero u u' b x i) (integrable_iSup_inner_add F u b)
    (integrable_smoothMax_interpZ hF hβ u u' b 0)
  have h1 := vecExpectedMax_interpPhi_bounds hF hβ u u' b (π / 2) u'
    (fun x i => interpZ_pi_div_two u u' b x i) (integrable_iSup_inner_add F u' b)
    (integrable_smoothMax_interpZ hF hβ u u' b (π / 2))
  have h2 := abs_interpPhi_sub_le hF hβ b horth hγ
  rw [abs_le] at h2 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

end Gaussian

/-! ### Optimizing in `β` -/

/-- If `Δ ≤ L/β + βγπ/2` for every `β > 0`, then `Δ ≤ 2 √(2γL)`. -/
lemma le_two_sqrt_of_forall_beta {Δ L γ : ℝ} (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (h : ∀ β : ℝ, 0 < β → Δ ≤ L / β + β * γ * (π / 2)) :
    Δ ≤ 2 * Real.sqrt (2 * γ * L) := by
  -- for each `t > 0`: `Δ ≤ (1 + π/2) √((L + t)(γ + t))`
  have hstep : ∀ t : ℝ, 0 < t → Δ ≤ (1 + π / 2) * Real.sqrt ((L + t) * (γ + t)) := by
    intro t ht
    set s := Real.sqrt ((L + t) * (γ + t)) with hs
    have hprod : 0 < (L + t) * (γ + t) := by positivity
    have hspos : 0 < s := Real.sqrt_pos.2 hprod
    have hss : s * s = (L + t) * (γ + t) := Real.mul_self_sqrt hprod.le
    have hβ : 0 < (L + t) / s := by positivity
    have h' := h _ hβ
    have e1 : L / ((L + t) / s) ≤ s := by
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have e2 : (L + t) / s * γ ≤ s := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hspos]
      nlinarith
    have hpi : 0 ≤ π / 2 := by positivity
    have e3 : (L + t) / s * γ * (π / 2) ≤ s * (π / 2) := mul_le_mul_of_nonneg_right e2 hpi
    nlinarith
  -- let `t → 0⁺`
  have hcont : Tendsto (fun t : ℝ => (1 + π / 2) * Real.sqrt ((L + t) * (γ + t))) (𝓝[>] 0)
      (𝓝 ((1 + π / 2) * Real.sqrt ((L + 0) * (γ + 0)))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((continuous_const.mul (Real.continuous_sqrt.comp
      ((continuous_const.add continuous_id).mul (continuous_const.add continuous_id))))).tendsto 0
  have hle : Δ ≤ (1 + π / 2) * Real.sqrt ((L + 0) * (γ + 0)) :=
    ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => hstep t ht)
  rw [add_zero, add_zero] at hle
  refine hle.trans ?_
  have hsq2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hpi := Real.pi_lt_d2
  have e : Real.sqrt (2 * γ * L) = Real.sqrt 2 * Real.sqrt (L * γ) := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num), mul_comm γ L]
  rw [e]
  have h0 : 0 ≤ Real.sqrt (L * γ) := Real.sqrt_nonneg _
  nlinarith

end Chatterjee

open Chatterjee SudakovFernique

/-- **Node `G6`** (`Blueprint.Draft.ExpectedMaxCovLipschitz`): Chatterjee's error bound. -/
theorem expectedMaxCovLipschitz : Blueprint.Draft.ExpectedMaxCovLipschitz := by
  intro ι F C₁ C₂ b γ hC₁ hC₂ hγ
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [gaussianExpectedMax]
  have hγ0 : 0 ≤ γ := by
    obtain ⟨i, hi⟩ := hF
    exact (abs_nonneg _).trans (hγ i hi i hi)
  have hL : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hF.card_pos)
  obtain ⟨v, hv, hv'⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F C₁ hC₁
  obtain ⟨w, hw, hw'⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F C₂ hC₂
  let u : ι → WithLp 2 (EuclideanSpace ℝ F × EuclideanSpace ℝ F) :=
    fun i => WithLp.toLp 2 (v i, 0)
  let u' : ι → WithLp 2 (EuclideanSpace ℝ F × EuclideanSpace ℝ F) :=
    fun i => WithLp.toLp 2 (0, w i)
  have hu : vecExpectedMax F v b = vecExpectedMax F u b :=
    vecExpectedMax_eq_of_gram_eq F v u b fun i _ j _ => by simp [u]
  have hu' : vecExpectedMax F w b = vecExpectedMax F u' b :=
    vecExpectedMax_eq_of_gram_eq F w u' b fun i _ j _ => by simp [u']
  have horth : ∀ i j, ⟪u i, u' j⟫ = 0 := fun i j => by simp [u, u']
  have hγ' : ∀ i ∈ F, ∀ j ∈ F, |⟪u' i, u' j⟫ - ⟪u i, u j⟫| ≤ γ := by
    intro i hi j hj
    have e1 : ⟪u i, u j⟫ = C₁ i j := by simp [u, hv i hi j hj]
    have e2 : ⟪u' i, u' j⟫ = C₂ i j := by simp [u', hw i hi j hj]
    rw [e1, e2, abs_sub_comm]
    exact hγ i hi j hj
  rw [hv' b, hw' b, hu, hu']
  have key := fun β (hβ : 0 < β) =>
    abs_vecExpectedMax_sub_le_of_orthogonal hF hβ u u' b horth hγ'
  rw [abs_le]
  constructor
  · have := le_two_sqrt_of_forall_beta (Δ := vecExpectedMax F u' b - vecExpectedMax F u b)
      hL hγ0 fun β hβ => by
        have h := key β hβ
        rw [abs_le] at h
        linarith [h.1]
    linarith
  · exact le_two_sqrt_of_forall_beta hL hγ0 fun β hβ => by
      have h := key β hβ
      rw [abs_le] at h
      linarith [h.2]

end LQGDimension
