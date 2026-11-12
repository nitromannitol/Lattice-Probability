/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.WhiteNoiseLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoisePhi
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Laws of `φ_{a,b}`: isometry invariance and scaling (task P2-WN; DDDF.D2.phi (i), (ii))

DDDF (arXiv:1904.08021, `tightness.tex` l. 289–292): the law of `φ_{a,b}` is invariant under
Euclidean isometries, and `φ_{a,b}(r ·) =ᵈ φ_{a/r, b/r}(·)` as processes (the computation at
l. 290–292 is the change of variables `t = r² s` in the covariance).

* `map_eq_of_forall_finset'`: the law of a process indexed by any type is determined by its
  finite-dimensional laws (QuantumZipper `Williams.map_eq_of_forall_finset`, generalized from
  the index `ℝ≥0`; mathlib `isProjectiveLimit_map`, `IsProjectiveLimit.unique`).
* `map_phi_eq_of_cov`: two `φ` fields (possibly on different spaces, reparametrized by maps
  `f`, `g`) with the same covariances have the same law on `ℂ → ℝ` (QZ
  `WedgeRes.map_eq_of_gaussian_vec` for the finite-dimensional laws).
* `map_phi_isometry`, `map_phi_scale`: (i) and (ii).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace WhiteNoise

/-- The law of a process is determined by its finite-dimensional laws. -/
theorem map_eq_of_forall_finset' {T Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {X : T → Ω → ℝ} {X' : T → Ω' → ℝ} (hX : AEMeasurable (fun ω t => X t ω) P)
    (hX' : AEMeasurable (fun ω t => X' t ω) P')
    (h : ∀ I : Finset T, P.map (fun ω => I.restrict (X · ω)) =
      P'.map (fun ω => I.restrict (X' · ω))) :
    P.map (fun ω t => X t ω) = P'.map (fun ω t => X' t ω) := by
  have h1 := ProbabilityTheory.isProjectiveLimit_map (P := P) (X := X) hX
  have h2 := ProbabilityTheory.isProjectiveLimit_map (P := P') (X := X') hX'
  have h2' : IsProjectiveLimit (P'.map (fun ω t => X' t ω))
      (fun I : Finset T => P.map fun ω => I.restrict (X · ω)) := by
    intro I
    rw [h2 I]
    exact (h I).symm
  exact h1.unique h2'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `φ_{a,b} ∘ f` is a Gaussian process. -/
theorem isGaussianProcess_phi_comp (hW : IsWhiteNoise P W) (a b : ℝ) {T : Type}
    (f : T → ℂ) : IsGaussianProcess (fun t => phi W a b (f t)) P :=
  QuantumZipper.GFFExist.gs_isGaussianProcess (fun t => (measurable_phi hW a b _).aemeasurable)
    fun I c => ⟨_, (hW.hasLaw (fun i : I => phiKernelL2 a b (f i))
      (fun i => c i * Real.sqrt Real.pi)).congr (Eventually.of_forall fun ω => by
        simp only [phi]
        exact Finset.sum_congr rfl fun i _ => by ring)⟩

lemma integral_phi (hW : IsWhiteNoise P W) (a b : ℝ) (x : ℂ) : ∫ ω, phi W a b x ω ∂P = 0 := by
  unfold phi
  rw [integral_const_mul, QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _),
    mul_zero]

lemma memLp_phi (hW : IsWhiteNoise P W) (a b : ℝ) (x : ℂ) : MemLp (phi W a b x) 2 P := by
  have := hW.isProbabilityMeasure
  exact ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _

/-- Two `φ` fields with the same covariances have the same law as processes. -/
theorem map_phi_eq_of_cov {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {W' : WNSpace → Ω' → ℝ} (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {a b a' b' : ℝ} (f g : ℂ → ℂ)
    (hcov : ∀ x x', cov[phi W a b (f x), phi W a b (f x'); P] =
      cov[phi W' a' b' (g x), phi W' a' b' (g x'); P']) :
    P.map (fun ω x => phi W a b (f x) ω) = P'.map (fun ω x => phi W' a' b' (g x) ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  refine map_eq_of_forall_finset' (X := fun x => phi W a b (f x))
    (X' := fun x => phi W' a' b' (g x))
    (measurable_pi_iff.mpr fun x => measurable_phi hW a b _).aemeasurable
    (measurable_pi_iff.mpr fun x => measurable_phi hW' a' b' _).aemeasurable fun I => ?_
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I)
    (U := fun i => phi W a b (f i)) (V := fun i => phi W' a' b' (g i))
    ((isGaussianProcess_phi_comp hW a b f).hasGaussianLaw I)
    ((isGaussianProcess_phi_comp hW' a' b' g).hasGaussianLaw I)
    (fun i => measurable_phi hW a b _) (fun i => measurable_phi hW' a' b' _)
    (fun i => memLp_phi hW a b _) (fun i => memLp_phi hW' a' b' _)
    (fun i => integral_phi hW a b _) (fun i => integral_phi hW' a' b' _)
    (fun i j => hcov i j)

/-- The change of variables `t = r² s` in the covariance (DDDF l. 290–292). -/
lemma integral_scale {a b r : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 < r) (d : ℝ) :
    ∫ t in Icc (a ^ 2) (b ^ 2), (2 * t)⁻¹ * Real.exp (-(r * d) ^ 2 / (2 * t)) =
      ∫ t in Icc ((a / r) ^ 2) ((b / r) ^ 2), (2 * t)⁻¹ * Real.exp (-d ^ 2 / (2 * t)) := by
  have h1 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h2 : (a / r) ^ 2 ≤ (b / r) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg ha hr.le) (div_le_div_of_nonneg_right hab hr.le) 2
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
  set g : ℝ → ℝ := fun t => (2 * t)⁻¹ * Real.exp (-d ^ 2 / (2 * t)) with hg
  have hc : (r ^ 2)⁻¹ ≠ 0 := by positivity
  have e : ∀ t, (2 * t)⁻¹ * Real.exp (-(r * d) ^ 2 / (2 * t)) =
      (r ^ 2)⁻¹ * g ((r ^ 2)⁻¹ * t) := by
    intro t
    simp only [hg]
    by_cases ht : t = 0
    · simp [ht]
    · have hr0 : r ≠ 0 := hr.ne'
      rw [show -d ^ 2 / (2 * ((r ^ 2)⁻¹ * t)) = -(r * d) ^ 2 / (2 * t) by field_simp]
      field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hc,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  congr 1 <;> field_simp

/-- **Scaling** (DDDF.D2.phi (ii), `tightness.tex` l. 289): `φ_{a,b}(r ·) =ᵈ φ_{a/r, b/r}(·)`
as processes on `ℂ`, for `r > 0`. -/
theorem map_phi_scale (hW : IsWhiteNoise P W) {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 < r) :
    P.map (fun ω x => phi W a b ((r : ℂ) * x) ω) = P.map (fun ω x => phi W (a / r) (b / r) x ω) :=
  map_phi_eq_of_cov hW hW (fun x => (r : ℂ) * x) id fun x x' => by
    rw [cov_phi hW ha, cov_phi hW (div_pos ha hr)]
    simp only [id]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact integral_scale ha.le hab hr _

/-- Modifications have the same law on `ℂ → ℝ` (product σ-algebra). -/
theorem map_eq_of_modification {Y X : ℂ → Ω → ℝ} [IsFiniteMeasure P]
    (hY : ∀ x, Measurable (Y x)) (hX : ∀ x, Measurable (X x)) (hYX : ∀ x, Y x =ᵐ[P] X x) :
    P.map (fun ω x => Y x ω) = P.map (fun ω x => X x ω) := by
  refine map_eq_of_forall_finset' (measurable_pi_iff.mpr hY).aemeasurable
    (measurable_pi_iff.mpr hX).aemeasurable fun I => ?_
  refine Measure.map_congr ?_
  have h : ∀ᵐ ω ∂P, ∀ i : I, Y i ω = X i ω := ae_all_iff.mpr fun i => hYX i
  filter_upwards [h] with ω hω
  funext i
  exact hω i

/-- **Scaling for modifications** (towards DDDF (2.30)): if `Y₁` is a modification of
`x ↦ φ_{a,b}(r x)` and `Y₂` one of `φ_{a/r,b/r}` (e.g. the continuous versions of
`exists_continuous_modification_phi`), then `Y₁ =ᵈ Y₂` on `ℂ → ℝ`; hence `F(Y₁) =ᵈ F(Y₂)` for
every measurable functional `F` (lengths of paths, DDDF l. 490). -/
theorem map_modification_scale (hW : IsWhiteNoise P W) {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : 0 < r) {Y₁ Y₂ : ℂ → Ω → ℝ} (h₁ : ∀ x, Measurable (Y₁ x)) (h₂ : ∀ x, Measurable (Y₂ x))
    (hY₁ : ∀ x, Y₁ x =ᵐ[P] phi W a b ((r : ℂ) * x)) (hY₂ : ∀ x, Y₂ x =ᵐ[P] phi W (a / r) (b / r) x)
    {β : Type*} [MeasurableSpace β] {F : (ℂ → ℝ) → β} (hF : Measurable F) :
    P.map (fun ω => F fun x => Y₁ x ω) = P.map (fun ω => F fun x => Y₂ x ω) := by
  have := hW.isProbabilityMeasure
  have e1 := map_eq_of_modification h₁ (fun x => measurable_phi hW a b _) hY₁
  have e2 := map_eq_of_modification h₂ (fun x => measurable_phi hW (a / r) (b / r) _) hY₂
  have e := map_phi_scale hW ha hab hr
  have m1 : Measurable fun ω x => Y₁ x ω := measurable_pi_iff.mpr h₁
  have m2 : Measurable fun ω x => Y₂ x ω := measurable_pi_iff.mpr h₂
  rw [show (fun ω => F fun x => Y₁ x ω) = F ∘ fun ω x => Y₁ x ω from rfl,
    show (fun ω => F fun x => Y₂ x ω) = F ∘ fun ω x => Y₂ x ω from rfl,
    ← Measure.map_map hF m1, ← Measure.map_map hF m2, e1, e2, e]

/-- `Var φ_{a,b}(x) = log (b/a)` for `0 < a ≤ b` (DDDF l. 289). -/
theorem variance_phi (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℂ) :
    Var[phi W a b x; P] = Real.log (b / a) := by
  have := hW.isProbabilityMeasure
  rw [← covariance_self (memLp_phi hW a b x).aemeasurable, cov_phi hW ha]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Real.exp_zero, mul_one]
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hb : 0 < b := ha.trans_le hab
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h2]
  simp_rw [mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by positivity) (by positivity),
    ← div_pow, Real.log_pow]
  push_cast
  ring

end WhiteNoise
end LQGMetric
