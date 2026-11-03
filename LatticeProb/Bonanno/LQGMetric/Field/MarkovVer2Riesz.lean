/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovVer2Riesz at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovVer2Poinc
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAdmCov
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Riesz vectors of bounded densities: pairing, linearity, variance bound (task P2-MKV)

For an open `V` with `V ∩ ∂𝔻 = ∅` and a bounded measurable `ρ` vanishing off `V` and off a
ball `B(0, A)`:

* `inner_rieszFun_gradFeat` : `⟪rieszFun V ρ, ∇f⟫ = ∫ ρ f` for `f ∈ C_c^∞(V)`;
* `rieszFun_sub` : `rieszFun V (ρ - σ) = rieszFun V ρ - rieszFun V σ` (Riesz uniqueness,
  QZ `K3.eq_of_mem_gradClosure_of_inner_eq`);
* `norm_rieszFun_sq_le` : `‖rieszFun V ρ‖² ≤ 2π A³ ∫ ρ²` (`A ≥ 1`), i.e.
  `Var⟨h̊^V, ρ⟩ ≤ 2π A³ ‖ρ‖²_{L²}`: the variational formula (Sheffield math/0312099 §2,
  `Var = sup (∫ f ρ)² / (f,f)_∇`, as in `ZeroBoundaryVar.ofReal_zeroGFFTestCov_self`),
  Cauchy–Schwarz and the Poincaré inequality `MarkovVer2.lintegral_ball_sq_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Real TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace MarkovVer2

open QuantumZipper QuantumZipper.K3 MarkovExt MarkovNorm MarkovAdm

/-- bounded measurable densities supported in `V ∩ B(0, A)` -/
structure IsBddDensOn (V : Set ℂ) (A : ℝ) (ρ : ℂ → ℝ) : Prop where
  meas : Measurable ρ
  bdd : ∃ C, ∀ z, |ρ z| ≤ C
  ball : ∀ z ∉ ball (0 : ℂ) A, ρ z = 0
  zero : ∀ z ∉ V, ρ z = 0

lemma IsBddDensOn.sub {V : Set ℂ} {A : ℝ} {ρ σ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ)
    (hσ : IsBddDensOn V A σ) : IsBddDensOn V A (ρ - σ) := by
  obtain ⟨C, hC⟩ := hρ.bdd
  obtain ⟨D, hD⟩ := hσ.bdd
  refine ⟨hρ.meas.sub hσ.meas, ⟨C + D, fun z => ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · exact (abs_sub _ _).trans (add_le_add (hC z) (hD z))
  · simp [hρ.ball z hz, hσ.ball z hz]
  · simp [hρ.zero z hz, hσ.zero z hz]

lemma IsBddDensOn.admissible {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {A : ℝ}
    {ρ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ρ) ∧
      IsAdmissibleDual V (zeroSpace V) (testMeasNeg ρ) := by
  obtain ⟨C, hC⟩ := hρ.bdd
  exact admissible_of_disjoint_sphere hV hρ.meas hC (R := A)
    (fun z hz => hρ.ball z fun h => hz (ball_subset_closedBall h)) hρ.zero

theorem inner_rieszFun_gradFeat {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {A : ℝ}
    {ρ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ) {f : ℂ → ℝ} (hf : f ∈ zeroSpace V)
    (hp : 0 < dirichletEnergyOn V f) :
    ⟪rieszFun V ρ, gradFeat V f⟫ = ∫ x, ρ x * f x := by
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  obtain ⟨C, hC⟩ := hρ.bdd
  have hadm := hρ.admissible hV
  rw [rieszFun, inner_sub_left, pair_rieszVec hDN hadm.1 ⟨f, hf, hp⟩ f hf,
    pair_rieszVec hDN hadm.2 ⟨f, hf, hp⟩ f hf]
  exact integral_testMeas_sub hρ.meas hC hf

lemma integrable_mul_zeroSpace {V : Set ℂ} {A : ℝ} {ρ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) : Integrable fun x => ρ x * f x := by
  obtain ⟨C, hC⟩ := hρ.bdd
  exact (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1).bdd_mul
    hρ.meas.aestronglyMeasurable (c := C) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)

/-- linearity of the Riesz vector on bounded densities -/
theorem rieszFun_sub {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {A : ℝ}
    {ρ σ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ) (hσ : IsBddDensOn V A σ) :
    rieszFun V (ρ - σ) = rieszFun V ρ - rieszFun V σ := by
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  refine LQGMetric.eq_of_mem_gradClosure (rieszFun_mem V _)
    (sub_mem (rieszFun_mem V _) (rieszFun_mem V _)) fun f hf => ?_
  rcases (energy_nonneg (V : Set ℂ) f).lt_or_eq with hp | hz
  · rw [inner_sub_left, inner_rieszFun_gradFeat hV (hρ.sub hσ) hf hp,
      inner_rieszFun_gradFeat hV hρ hf hp, inner_rieszFun_gradFeat hV hσ hf hp,
      ← integral_sub (integrable_mul_zeroSpace hρ hf) (integrable_mul_zeroSpace hσ hf)]
    congr 1; funext x; simp [sub_mul]
  · rw [gradFeat_eq_zero_of_energy hDN hf hz.symm, inner_zero_right, inner_zero_right]

/-- Cauchy–Schwarz for integrals (discriminant form) -/
lemma sq_integral_mul_le {μ : Measure ℂ} {ρ f : ℂ → ℝ} (h1 : Integrable (fun x => ρ x ^ 2) μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) (h3 : Integrable (fun x => ρ x * f x) μ) :
    (∫ x, ρ x * f x ∂μ) ^ 2 ≤ (∫ x, ρ x ^ 2 ∂μ) * ∫ x, f x ^ 2 ∂μ := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x, ρ x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, ρ x * f x ∂μ) * t +
      ∫ x, f x ^ 2 ∂μ := by
    intro t
    have e : ∫ x, (t * ρ x - f x) ^ 2 ∂μ = (∫ x, ρ x ^ 2 ∂μ) * (t * t) +
        (-2 * ∫ x, ρ x * f x ∂μ) * t + ∫ x, f x ^ 2 ∂μ := by
      have : (fun x => (t * ρ x - f x) ^ 2) =
          fun x => (t * t) * ρ x ^ 2 + (-2 * t) * (ρ x * f x) + f x ^ 2 := by
        funext x; ring
      have hi : Integrable (fun x => t * t * ρ x ^ 2 + -2 * t * (ρ x * f x)) μ :=
        (h1.const_mul (t * t)).add (h3.const_mul (-2 * t))
      rw [this, integral_add hi h2,
        integral_add (h1.const_mul _) (h3.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← e]; exact integral_nonneg fun x => sq_nonneg _
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith [hd]

/-- **Variance bound**: `‖rieszFun V ρ‖² ≤ 2π A³ ∫ ρ²` for `ρ` bounded, supported in
`V ∩ B(0, A)`, `A ≥ 1`. -/
theorem norm_rieszFun_sq_le {V : Opens ℂ} (hV : Disjoint (V : Set ℂ) (sphere 0 1)) {A : ℝ}
    (hA : 1 ≤ A) {ρ : ℂ → ℝ} (hρ : IsBddDensOn V A ρ) :
    ‖rieszFun V ρ‖ ^ 2 ≤ 2 * π * A ^ 3 * ∫ x, ρ x ^ 2 := by
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  obtain ⟨C, hC⟩ := hρ.bdd
  set v := rieszFun V ρ
  set Q := 2 * π * A ^ 3 * ∫ x, ρ x ^ 2
  have hfinB : volume (ball (0 : ℂ) A) ≠ ∞ := measure_ball_lt_top.ne
  have hρ2 : Integrable (fun x => ρ x ^ 2) (volume.restrict (ball (0 : ℂ) A)) :=
    Measure.integrableOn_of_bounded (M := C ^ 2) hfinB (hρ.meas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
  have hρ2' : ∫ x, ρ x ^ 2 = ∫ x in ball (0 : ℂ) A, ρ x ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hρ.ball x hx]; ring).symm
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ ∫ x, ρ x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have : 0 ≤ A ^ 3 := pow_nonneg (zero_le_one.trans hA) 3
    positivity
  have hfeat : ∀ f ∈ zeroSpace (V : Set ℂ), ⟪v, gradFeat V f⟫ ≤ √Q * ‖gradFeat V f‖ := by
    intro f hf
    rcases (energy_nonneg (V : Set ℂ) f).lt_or_eq with hp | hz
    · rw [inner_rieszFun_gradFeat hV hρ hf hp]
      have hf1 : ContDiff ℝ 1 f := hDN.smooth f hf
      have hfc : Continuous f := hf1.continuous
      obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hf.2.1
      have hDc : Continuous fun z => ‖fderiv ℝ f z‖ ^ 2 :=
        (hf1.continuous_fderiv one_ne_zero).norm.pow 2
      have hDs : HasCompactSupport fun z => ‖fderiv ℝ f z‖ ^ 2 :=
        (hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun y => ‖y‖ ^ 2) (by simp)
      have hDi : Integrable fun z => ‖fderiv ℝ f z‖ ^ 2 := hDc.integrable_of_hasCompactSupport hDs
      have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict (ball (0 : ℂ) A)) :=
        Measure.integrableOn_of_bounded (M := Cf ^ 2) hfinB (hfc.pow 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_pow, ← Real.norm_eq_abs]
            exact pow_le_pow_left₀ (norm_nonneg _) (hCf x) 2)
      -- Poincaré, real form
      have hP : ∫ x in ball (0 : ℂ) A, f x ^ 2 ≤ A ^ 3 * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := by
        have h0 : ∀ z ∈ sphere (0 : ℂ) 1, f z = 0 := fun z hz =>
          image_eq_zero_of_notMem_tsupport fun h => Set.disjoint_left.1 hV (hf.2.2 h) hz
        have hl := lintegral_ball_sq_le hf1 h0 hA
        rw [← ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun _ =>
          sq_nonneg _), ← ofReal_integral_eq_lintegral_ofReal hDi
          (Filter.Eventually.of_forall fun _ => sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)] at hl
        have := (ENNReal.ofReal_le_ofReal_iff (by
          have : 0 ≤ ∫ z, ‖fderiv ℝ f z‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
          have : 0 ≤ A := zero_le_one.trans hA
          positivity)).1 hl
        calc _ ≤ A ^ 2 * A * ∫ z, ‖fderiv ℝ f z‖ ^ 2 := this
          _ = _ := by ring
      have hE : ∫ z, ‖fderiv ℝ f z‖ ^ 2 = 2 * π * ‖gradFeat V f‖ ^ 2 := by
        rw [norm_gradFeat_sq hf1 (hDN.energy f hf), dirichletEnergyOn,
          setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
            have : fderiv ℝ f z = 0 := by
              by_contra hne
              exact hz (hf.2.2 (support_fderiv_subset ℝ hne))
            rw [this, norm_zero]; ring]
        field_simp
      have hρf : ∫ x, ρ x * f x = ∫ x in ball (0 : ℂ) A, ρ x * f x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [hρ.ball x hx, zero_mul]).symm
      have hCS := sq_integral_mul_le hρ2 hf2 ((integrable_mul_zeroSpace hρ hf).restrict)
      rw [← hρf, ← hρ2'] at hCS
      have hX : (∫ x, ρ x * f x) ^ 2 ≤ Q * ‖gradFeat V f‖ ^ 2 := by
        calc _ ≤ (∫ x, ρ x ^ 2) * ∫ x in ball (0 : ℂ) A, f x ^ 2 := hCS
          _ ≤ (∫ x, ρ x ^ 2) * (A ^ 3 * (2 * π * ‖gradFeat V f‖ ^ 2)) := by
            rw [← hE]; exact mul_le_mul_of_nonneg_left hP (integral_nonneg fun _ => sq_nonneg _)
          _ = _ := by ring
      calc ∫ x, ρ x * f x ≤ |∫ x, ρ x * f x| := le_abs_self _
        _ = √((∫ x, ρ x * f x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √(Q * ‖gradFeat V f‖ ^ 2) := Real.sqrt_le_sqrt hX
        _ = √Q * ‖gradFeat V f‖ := by rw [Real.sqrt_mul hQ0, Real.sqrt_sq (norm_nonneg _)]
    · rw [gradFeat_eq_zero_of_energy hDN hf hz.symm]; simp
  have hsub : (Submodule.span ℝ (gradFeat V '' zeroSpace (V : Set ℂ)) : Set (GradSpace V)) ⊆
      {w | ⟪v, w⟫ ≤ √Q * ‖w‖} := by
    intro w hw
    obtain ⟨f, hf, rfl⟩ := mem_image_of_mem_span hDN hw
    exact hfeat f hf
  have hcl : IsClosed {w : GradSpace V | ⟪v, w⟫ ≤ √Q * ‖w‖} :=
    isClosed_le (continuous_const.inner continuous_id) (continuous_const.mul continuous_norm)
  have hv' : v ∈ closure (Submodule.span ℝ (gradFeat V '' zeroSpace (V : Set ℂ)) :
      Set (GradSpace V)) := by
    rw [← Submodule.topologicalClosure_coe]; exact rieszFun_mem V ρ
  have h := closure_minimal hsub hcl hv'
  simp only [Set.mem_ofPred_eq, real_inner_self_eq_norm_sq] at h
  have hv2 : ‖v‖ ≤ √Q := by
    rcases (norm_nonneg v).lt_or_eq with hp | h0
    · nlinarith [Real.sqrt_nonneg Q]
    · rw [← h0]; exact Real.sqrt_nonneg _
  calc ‖v‖ ^ 2 ≤ (√Q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv2 2
    _ = Q := Real.sq_sqrt hQ0

end MarkovVer2
end LQGMetric
